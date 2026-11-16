import Langlands.AbelianScheme.Tate.PrimePowerTorsionClosure
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothProof
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupGeometry
import Langlands.CategoryTheory.GroupObjectDescent
import Langlands.AlgebraicGeometry.AlgClosedConnectedProof

/-! # An abelian scheme realizing the prime-power torsion closure -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Tate.PrimePowerTorsion

universe u

open Scheme.IdealSheafData

private lemma vanishingIdeal_le_ker_of_range {X Y : Scheme.{u}} [IsReduced X]
    (Z : TopologicalSpace.Closeds Y) (f : X ⟶ Y) (hf : Set.range f ⊆ Z) :
    vanishingIdeal Z ≤ f.ker := by
  rw [← map_bot f, ← Scheme.nilradical_eq_bot (X := X), ← vanishingIdeal_top,
    map_vanishingIdeal]
  apply vanishingIdeal_antimono
  change closure (f '' Set.univ) ⊆ Z
  simpa only [Set.image_univ] using closure_minimal hf Z.isClosed

private lemma vanishingIdeal_le_map_of_image_eq {X : Scheme.{u}}
    (Z : TopologicalSpace.Closeds X) (f : X ⟶ X) (hf : f '' (Z : Set X) = Z) :
    vanishingIdeal Z ≤ (vanishingIdeal Z).map f := by
  rw [map_vanishingIdeal, hf]
  apply vanishingIdeal_antimono
  change closure (Z : Set X) ⊆ Z
  exact Z.isClosed.closure_eq.le

private def restrictClosedIso {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (e : X ≅ X) (he : e.hom '' (Z : Set X) = Z) :
    (vanishingIdeal Z).subscheme ≅ (vanishingIdeal Z).subscheme := by
  let I := vanishingIdeal Z
  have hi (x : X) : e.inv (e.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have he' : e.inv '' (Z : Set X) = Z := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := he.ge hx
      rwa [← hyx, hi]
    · intro x hx
      exact ⟨e.hom x, he.le ⟨x, hx, rfl⟩, hi x⟩
  have hm : I ≤ I.map e.hom := vanishingIdeal_le_map_of_image_eq Z e.hom he
  have hn : I ≤ I.map e.inv := vanishingIdeal_le_map_of_image_eq Z e.inv he'
  let f := subschemeMap I I e.hom hm
  let g := subschemeMap I I e.inv hn
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        apply (cancel_mono I.subschemeι).1
        simp [f, g, Category.assoc]
      inv_hom_id := by
        apply (cancel_mono I.subschemeι).1
        simp [f, g, Category.assoc] }

private lemma restrictClosedIso_hom_ι {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (e : X ≅ X) (he : e.hom '' (Z : Set X) = Z) :
    (restrictClosedIso Z e he).hom ≫ (vanishingIdeal Z).subschemeι =
      (vanishingIdeal Z).subschemeι ≫ e.hom := by
  exact subschemeMap_subschemeι _ _ _ (vanishingIdeal_le_map_of_image_eq Z e.hom he)

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (p : ℕ)

/-- The actual closed subset with its reduced induced scheme structure. -/
abbrev closureIdeal : A.X.left.IdealSheafData :=
  vanishingIdeal ⟨closure (locus A p), isClosed_closure⟩

/-- The reduced induced subscheme on the actual torsion closure. -/
abbrev reducedClosure : Scheme.{u} :=
  (closureIdeal A p).subscheme

/-- Its actual closed immersion into the ambient abelian scheme. -/
abbrev reducedClosureι : reducedClosure A p ⟶ A.X.left :=
  (closureIdeal A p).subschemeι

instance : IsClosedImmersion (reducedClosureι A p) := by
  exact inferInstanceAs (IsClosedImmersion (closureIdeal A p).subschemeι)

instance : IsReduced (reducedClosure A p) :=
  P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme.IntegralSubscheme.isReduced_vanishingIdeal _

lemma range_reducedClosureι :
    Set.range (reducedClosureι A p) = closure (locus A p) := by
  change Set.range (closureIdeal A p).subschemeι = _
  rw [range_subschemeι]
  exact coe_support_vanishingIdeal _

private lemma inverse_image_closure :
    ι[A.X].left '' closure (locus A p) =
      closure (locus A p) := by
  have h : Set.MapsTo ι[A.X].left (locus A p) (locus A p) := by
    rintro x ⟨n, s, hs, rfl⟩
    refine ⟨n, s⁻¹, by simp [inv_pow, hs], ?_⟩
    rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]
  have hc := h.closure ι[A.X].left.continuous
  apply Set.Subset.antisymm hc.image_subset
  intro x hx
  refine ⟨ι[A.X].left x, hc hx, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.inv_comp_inv]
  rfl

/-- The reduced-scheme restrictions needed in the closed subgroup construction. -/
theorem reducedClosure_exists :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ A.X.left),
      IsClosedImmersion i ∧ IsReduced Y ∧
      Set.range i = closure (locus A p) ∧
      (∃ e : Spec (CommRingCat.of K) ⟶ Y,
        e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) ∧
      (∃ v : Y ≅ Y, v.hom ≫ i = i ≫ ι[A.X].left) ∧
      ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
        s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p) →
        ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left := by
  let Z : TopologicalSpace.Closeds A.X.left :=
    ⟨closure (locus A p), isClosed_closure⟩
  let I := vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme.IntegralSubscheme.isReduced_vanishingIdeal Z, ?_, ?_, ?_, ?_⟩
  · rw [range_subschemeι]
    exact coe_support_vanishingIdeal _
  · let e : Spec (CommRingCat.of K) ⟶ A.X.left :=
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left
    have he : Set.range e ⊆ Z := by
      rintro _ ⟨x, rfl⟩
      have hx : x = default := Subsingleton.elim _ _
      rw [hx]
      exact subset_closure ⟨0, 1, by simp, rfl⟩
    exact ⟨IsClosedImmersion.lift I.subschemeι e (by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker_of_range Z e he),
      IsClosedImmersion.lift_fac _ _ _⟩
  · let v : A.X.left ≅ A.X.left := (Over.forget _).mapIso (asIso ι[A.X])
    exact ⟨restrictClosedIso Z v (inverse_image_closure A p),
      restrictClosedIso_hom_ι Z v (inverse_image_closure A p)⟩
  · intro s hs
    let t : A.X.left ≅ A.X.left := (Over.forget _).mapIso (GrpObj.mulRight s)
    have ht : t.hom '' (Z : Set A.X.left) = Z :=
      image_closure_mulRight A p s hs
    exact ⟨restrictClosedIso Z t ht, restrictClosedIso_hom_ι Z t ht⟩

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
private lemma unit_comp_mulRight
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
      (GrpObj.mulRight s).hom = s := by
  change (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
    ((𝟙 A.X) * (toUnit A.X ≫ s)) = s
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
      toUnit A.X = 𝟙 _ := toUnit_unique _ _
  rw [h, Category.id_comp, one_mul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma smooth_of_closureRestrictions
    (Y : Scheme.{u}) (i : Y ⟶ A.X.left) [IsClosedImmersion i] [IsReduced Y]
    (hi : Set.range i = closure (locus A p))
    (e : Spec (CommRingCat.of K) ⟶ Y)
    (he : e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left)
    (htrans : ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
      s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p) →
      ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left) :
    Smooth (i ≫ A.X.hom) := by
  let π := i ≫ A.X.hom
  have : LocallyOfFiniteType π := inferInstance
  apply Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth K Y π
  intro x y hx hy
  let x' := pointOfClosedPoint π x hx
  let y' := pointOfClosedPoint π y hy
  let sx : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
    Over.homMk (x' ≫ i) (by
      change x' ≫ π = 𝟙 _
      exact pointOfClosedPoint_comp π x hx)
  let sy : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
    Over.homMk (y' ≫ i) (by
      change y' ≫ π = 𝟙 _
      exact pointOfClosedPoint_comp π y hy)
  have hsx : sx.left (default : Spec (CommRingCat.of K)) ∈
      closure (locus A p) := by
    rw [← hi]
    exact ⟨x' (default : Spec (CommRingCat.of K)), rfl⟩
  have hsy : sy.left (default : Spec (CommRingCat.of K)) ∈
      closure (locus A p) := by
    rw [← hi]
    exact ⟨y' (default : Spec (CommRingCat.of K)), rfl⟩
  obtain ⟨tx, htx⟩ := htrans sx hsx
  obtain ⟨ty, hty⟩ := htrans sy hsy
  have htxe : e ≫ tx.hom = x' := by
    apply (cancel_mono i).mp
    rw [Category.assoc, htx, ← Category.assoc, he]
    exact congrArg Over.Hom.left (unit_comp_mulRight A sx)
  have htye : e ≫ ty.hom = y' := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hty, ← Category.assoc, he]
    exact congrArg Over.Hom.left (unit_comp_mulRight A sy)
  have htxp : tx.hom ≫ π = π := by
    dsimp only [π]
    rw [← Category.assoc, htx, Category.assoc, Over.w]
  have htyp : ty.hom ≫ π = π := by
    dsimp only [π]
    rw [← Category.assoc, hty, Category.assoc, Over.w]
  let α := tx.symm ≪≫ ty
  refine ⟨α, ?_, ?_⟩
  · change tx.inv ≫ ty.hom ≫ π = π
    rw [htyp]
    calc
      tx.inv ≫ π = tx.inv ≫ tx.hom ≫ π := by rw [htxp]
      _ = π := by simp
  · have hxy : x' ≫ α.hom = y' := by
      dsimp only [α, Iso.trans_hom, Iso.symm_hom]
      rw [← htxe]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using htye
    simpa [x', y'] using congrArg
      (fun q : Spec (CommRingCat.of K) ⟶ Y =>
        q (default : Spec (CommRingCat.of K))) hxy

/-- The actual torsion closure has a smooth closed realization. -/
theorem smoothClosure_exists :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ A.X.left),
      IsClosedImmersion i ∧ Smooth (i ≫ A.X.hom) ∧
      Set.range i = closure (locus A p) ∧
      (∃ e : Spec (CommRingCat.of K) ⟶ Y,
        e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) ∧
      (∃ v : Y ≅ Y, v.hom ≫ i = i ≫ ι[A.X].left) ∧
      ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
        s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p) →
        ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left := by
  obtain ⟨Y, i, hi, hred, hrange, ⟨e, he⟩, hv, htrans⟩ := reducedClosure_exists A p
  have : IsClosedImmersion i := hi
  have : IsReduced Y := hred
  exact ⟨Y, i, hi,
    smooth_of_closureRestrictions A p Y i hrange e he htrans,
    hrange, ⟨e, he⟩, hv, htrans⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma exists_mul_on_smooth_closure
    (Y : Scheme.{u}) (i : Y ⟶ A.X.left) [IsClosedImmersion i]
    [Smooth (i ≫ A.X.hom)]
    (hi : Set.range i = closure (locus A p)) :
    let P := Over.mk (i ≫ A.X.hom)
    let j : P ⟶ A.X := Over.homMk i
    ∃ m : P ⊗ P ⟶ P, m ≫ j = (j ⊗ₘ j) ≫ μ[A.X] := by
  let P := Over.mk (i ≫ A.X.hom)
  let j : P ⟶ A.X := Over.homMk i
  let g : P ⊗ P ⟶ A.X := (j ⊗ₘ j) ≫ μ[A.X]
  have : Smooth P.hom := ‹Smooth (i ≫ A.X.hom)›
  have hp : Smooth (P ⊗ P).hom := inferInstanceAs
    (Smooth (pullback.fst P.hom P.hom ≫ P.hom))
  have : IsReduced (P ⊗ P).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K (P ⊗ P).left (P ⊗ P).hom
  have : JacobsonSpace (P ⊗ P).left :=
    LocallyOfFiniteType.jacobsonSpace (P ⊗ P).hom
  have hc : IsClosed (g.left ⁻¹' Set.range i) :=
    i.isClosedEmbedding.isClosed_range.preimage g.left.continuous
  have hclosed : closedPoints (P ⊗ P).left ⊆ g.left ⁻¹' Set.range i := by
    intro z hz
    let s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P ⊗ P :=
      Over.homMk (pointOfClosedPoint (P ⊗ P).hom z hz)
        (pointOfClosedPoint_comp (P ⊗ P).hom z hz)
    let s₁ := s ≫ fst P P ≫ j
    let s₂ := s ≫ snd P P ≫ j
    have hs₁ : s₁ ∈ closureSectionSubgroup A p := by
      change s₁.left (default : Spec (CommRingCat.of K)) ∈
        closure (locus A p)
      rw [← hi]
      exact ⟨(s ≫ fst P P).left (default : Spec (CommRingCat.of K)), rfl⟩
    have hs₂ : s₂ ∈ closureSectionSubgroup A p := by
      change s₂.left (default : Spec (CommRingCat.of K)) ∈
        closure (locus A p)
      rw [← hi]
      exact ⟨(s ≫ snd P P).left (default : Spec (CommRingCat.of K)), rfl⟩
    have hsg : s ≫ g = s₁ * s₂ := by
      simp only [g, s₁, s₂, Hom.mul_def, ← comp_lift_assoc, lift_fst_comp_snd_comp]
    have hmul := (closureSectionSubgroup A p).mul_mem hs₁ hs₂
    change (s₁ * s₂).left (default : Spec (CommRingCat.of K)) ∈
      closure (locus A p) at hmul
    rw [← hsg, Over.comp_left, Scheme.Hom.comp_apply] at hmul
    change g.left z ∈ Set.range i
    rw [hi]
    simpa [s] using hmul
  have hrange : Set.range g.left ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    have hall : Set.univ ⊆ g.left ⁻¹' Set.range i := by
      rw [← closure_closedPoints]
      exact hc.closure_subset_iff.mpr hclosed
    exact hall (Set.mem_univ z)
  obtain ⟨m, hm⟩ := exists_factor_closedImmersion_of_reduced i g.left hrange
  have hmp : m ≫ P.hom = (P ⊗ P).hom := by
    change m ≫ i ≫ A.X.hom = _
    rw [← Category.assoc, hm, Over.w]
  exact ⟨Over.homMk m hmp, Over.OverMorphism.ext hm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem closureGroupScheme_exists :
    ∃ (G : CommGroupScheme (Spec (CommRingCat.of K)))
      (f : G ⟶ A.toCommGroupScheme),
      IsClosedImmersion (CommGroupScheme.hom f) ∧
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Set.range (CommGroupScheme.hom f) = closure (locus A p) := by
  obtain ⟨Y, i, hi, hs, hrange, ⟨e, he⟩, ⟨v, hv⟩, _⟩ :=
    smoothClosure_exists A p
  have : IsClosedImmersion i := hi
  have : Smooth (i ≫ A.X.hom) := hs
  let P := Over.mk (i ≫ A.X.hom)
  let j : P ⟶ A.X := Over.homMk i
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
    Over.homMk e (by
      change e ≫ i ≫ A.X.hom = 𝟙 _
      rw [← Category.assoc, he, Over.w]
      rfl)
  have he' : e' ≫ j = η[A.X] := by
    apply Over.OverMorphism.ext
    change e ≫ i = η[A.X].left
    change e ≫ i = (𝟙 (Spec (CommRingCat.of K))) ≫ η[A.X].left at he
    exact he.trans (Category.id_comp η[A.X].left)
  let v' : P ⟶ P := Over.homMk v.hom (by
    change v.hom ≫ i ≫ A.X.hom = i ≫ A.X.hom
    rw [← Category.assoc, hv, Category.assoc, Over.w])
  have hv' : v' ≫ j = j ≫ ι[A.X] :=
    Over.OverMorphism.ext hv
  obtain ⟨m, hm⟩ := exists_mul_on_smooth_closure A p Y i hrange
  let := Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    j e' m v' he' hm hv'
  have : IsMonHom j :=
    Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
      j e' m v' he' hm hv'
  have : IsCommMonObj P :=
    Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono j
  let G : CommGroupScheme (Spec (CommRingCat.of K)) := { X := P }
  let f : G ⟶ A.toCommGroupScheme := Additive.ofMul (Grp.homMk j)
  exact ⟨G, f, hi, hs, inferInstanceAs (IsProper (i ≫ A.X.hom)), hrange⟩

theorem closureAbelianScheme_exists [CharZero K] [Fact p.Prime] :
    ∃ (B : AbelianScheme (Spec (CommRingCat.of K))) (f : B ⟶ A),
      IsClosedImmersion (AbelianScheme.hom f) ∧
      Set.range (AbelianScheme.hom f) = closure (locus A p) := by
  obtain ⟨G, f, hi, hs, hp, hrange⟩ :=
    closureGroupScheme_exists A p
  have : IsClosedImmersion (CommGroupScheme.hom f) := hi
  have : Smooth G.X.hom := hs
  have : IsProper G.X.hom := hp
  have hconn : _root_.IsConnected (Set.range (CommGroupScheme.hom f)) := by
    rw [hrange]
    exact isConnected_closure_locus A p
  have : ConnectedSpace G.X.left := by
    obtain ⟨_, ⟨x, rfl⟩⟩ := hconn.nonempty
    refine connectedSpace_iff_univ.mpr ⟨⟨x, Set.mem_univ _⟩, ?_⟩
    apply (CommGroupScheme.hom f).isClosedEmbedding.isInducing.isPreconnected_image.mp
    simpa only [Set.image_univ] using hconn.isPreconnected
  have : GeometricallyConnected G.X.hom :=
    Langlands.AlgebraicGeometry.algClosedConnected K G.X.left G.X.hom
  let B : AbelianScheme (Spec (CommRingCat.of K)) := { G with }
  let j : B ⟶ A := f
  exact ⟨B, j, hi, hrange⟩

end Langlands.AbelianScheme.Tate.PrimePowerTorsion
