import Langlands.GroupScheme.ClosedOrbitStatement
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-!
# Closed orbits of smooth affine group actions

A minimal nonempty closed subset stable under the rational points of the group, with its reduced
induced structure, is a single orbit: the orbit map is constructible by Chevalley's theorem,
hence contains a nonempty open subset, and its translates cover the minimal set.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace Topology
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.ClosedOrbit

/-! ### Constructible sets -/

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- On each irreducible set, a constructible set contains or misses a nonempty relatively open
part. -/
theorem constructible_dichotomy {s : Set T} (hs : IsConstructible s) :
    ∀ W : Set T, IsIrreducible W →
      (∃ U, IsOpen U ∧ (U ∩ W).Nonempty ∧ U ∩ W ⊆ s) ∨
        (∃ U, IsOpen U ∧ (U ∩ W).Nonempty ∧ U ∩ W ⊆ sᶜ) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    intro W hW
    by_cases hUW : (U ∩ W).Nonempty
    · exact Or.inl ⟨U, hU, hUW, Set.inter_subset_left⟩
    · refine Or.inr ⟨Set.univ, isOpen_univ, by simpa using hW.nonempty, ?_⟩
      rintro w ⟨-, hw⟩ hwU
      exact hUW ⟨w, hwU, hw⟩
  | union s _ t _ hs ht =>
    intro W hW
    rcases hs W hW with ⟨U, hU, hne, hsub⟩ | ⟨U₁, hU₁, hne₁, hsub₁⟩
    · exact Or.inl ⟨U, hU, hne, hsub.trans Set.subset_union_left⟩
    rcases ht W hW with ⟨U, hU, hne, hsub⟩ | ⟨U₂, hU₂, hne₂, hsub₂⟩
    · exact Or.inl ⟨U, hU, hne, hsub.trans Set.subset_union_right⟩
    obtain ⟨w, hwW, hw₁, hw₂⟩ := hW.2 U₁ U₂ hU₁ hU₂
      (by rw [Set.inter_comm]; exact hne₁) (by rw [Set.inter_comm]; exact hne₂)
    refine Or.inr ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨w, ⟨hw₁, hw₂⟩, hwW⟩, ?_⟩
    rintro v ⟨⟨hv₁, hv₂⟩, hvW⟩ (hv | hv)
    · exact hsub₁ ⟨hv₁, hvW⟩ hv
    · exact hsub₂ ⟨hv₂, hvW⟩ hv
  | compl s _ hs =>
    intro W hW
    rcases hs W hW with h | h
    · exact Or.inr (by simpa only [compl_compl] using h)
    · exact Or.inl h

/-- A dense constructible subset of a nonempty noetherian space contains a nonempty open set. -/
theorem exists_isOpen_subset_of_dense [NoetherianSpace T] [Nonempty T]
    {s : Set T} (hs : IsConstructible s) (hd : Dense s) :
    ∃ N : Set T, IsOpen N ∧ N.Nonempty ∧ N ⊆ s := by
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨o, ho, hone, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent t) (irreducibleComponent_mem_irreducibleComponents t)
  have hoirr : IsIrreducible o :=
    ⟨hone, isIrreducible_irreducibleComponent.isPreirreducible.open_subset ho hoZ⟩
  rcases constructible_dichotomy hs o hoirr with ⟨U, hU, hne, hsub⟩ | ⟨U, hU, hne, hsub⟩
  · exact ⟨U ∩ o, hU.inter ho, hne, hsub⟩
  · obtain ⟨v, hv, hvs⟩ := hd.inter_open_nonempty (U ∩ o) (hU.inter ho) hne
    exact absurd hvs (hsub hv)

end Topology

/-! ### Translations by points over the base

`OrbitMapFlat.actBy`, `FiniteIndexTransfer.leftMul` and their basic lemmas come from the Library.
-/

open Langlands.GroupScheme.OrbitMapFlat

section Translation

variable {S : Scheme.{u}} {G : GroupScheme S} {O : Over S} (a : SchemeAction G O)

/-- On points over any `T`, `actBy a g` is the action of `g`. -/
theorem comp_actBy_of {T : Over S} (g : 𝟙_ (Over S) ⟶ G.X) (y : T ⟶ O) :
    y ≫ actBy a g = a.act (toUnit T ≫ g) y := by
  rw [actBy, SchemeAction.naturality, comp_toUnit_assoc, Category.comp_id]

end Translation

/-- Points `g • y` of the action, evaluated at the closed point of a field, are images of `y`
under `actBy a g`. -/
theorem act_apply {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {O : Over (Spec (CommRingCat.of k))} (a : SchemeAction G O)
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X)
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O) :
    (a.act g y).left (IsLocalRing.closedPoint k) =
      (actBy a g).left (y.left (IsLocalRing.closedPoint k)) := by
  rw [← comp_actBy a g y, Over.comp_left, Scheme.Hom.comp_apply]

end Langlands.GroupScheme.ClosedOrbit

namespace Langlands.GroupScheme

open ClosedOrbit OrbitMapFlat

/-- A smooth affine group acting on a nonempty scheme of finite type over an algebraically closed
field has a closed orbit. -/
theorem closedOrbit : ClosedOrbitStatement.{u} := by
  intro k _ _ G _ _ X _ _ hne a
  -- Finiteness properties of `X`.
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  -- A minimal nonempty closed subset stable under the rational points of `G`.
  let Stable : Set X.left → Prop := fun Z =>
    ∀ (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X), ∀ z ∈ Z, (actBy a g).left z ∈ Z
  obtain ⟨Z, ⟨hZne, hZst⟩, hZmin⟩ := (wellFounded_lt (α := Closeds X.left)).has_min
    {Z | (Z : Set X.left).Nonempty ∧ Stable Z}
    ⟨⊤, by simp, fun _ _ _ => by simp⟩
  have hmin : ∀ Z' : Closeds X.left, (Z' : Set X.left).Nonempty → Stable Z' →
      (Z' : Set X.left) ⊆ Z → Z' = Z := by
    intro Z' hne' hst' hle
    by_contra hne''
    exact hZmin Z' ⟨hne', hst'⟩ (lt_of_le_of_ne hle hne'')
  -- The reduced induced closed subscheme on `Z`.
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred : IsReduced I.subscheme :=
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1
  let O : Over (Spec (CommRingCat.of k)) := Over.mk (I.subschemeι ≫ X.hom)
  let j : O ⟶ X := Over.homMk I.subschemeι rfl
  have : IsReduced O.left := hred
  have : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hjrange : Set.range j.left = Z := by
    change Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have : LocallyOfFiniteType O.hom := by
    change LocallyOfFiniteType (I.subschemeι ≫ X.hom)
    infer_instance
  have : QuasiCompact O.hom := by
    change QuasiCompact (I.subschemeι ≫ X.hom)
    infer_instance
  have : IsLocallyNoetherian O.left := LocallyOfFiniteType.isLocallyNoetherian O.hom
  have : CompactSpace O.left := QuasiCompact.compactSpace_of_compactSpace O.hom
  have : IsNoetherian O.left := {}
  have : QuasiSeparated O.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have : JacobsonSpace O.left := LocallyOfFiniteType.jacobsonSpace O.hom
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hjcancel : ∀ {T : Over (Spec (CommRingCat.of k))} (f₁ f₂ : T ⟶ O),
      f₁ ≫ j = f₂ ≫ j → f₁ = f₂ := by
    intro T f₁ f₂ h
    have : Mono j := Over.mono_of_mono_left j
    exact (cancel_mono j).mp h
  -- The action on `G × O` lands in `Z`.
  have : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth G.X.hom
  have : IsReduced (G.X ⊗ O).left :=
    inferInstanceAs (IsReduced (Limits.pullback G.X.hom O.hom))
  have : LocallyOfFiniteType (G.X ⊗ O).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst G.X.hom O.hom ≫ G.X.hom)
    infer_instance
  have : JacobsonSpace (G.X ⊗ O).left := LocallyOfFiniteType.jacobsonSpace (G.X ⊗ O).hom
  let m : G.X ⊗ O ⟶ X := (G.X ◁ j) ≫ a.hom
  have hm : Set.range m.left ⊆ Set.range j.left := by
    rw [hjrange]
    have hclosed : IsClosed (m.left ⁻¹' (Z : Set X.left)) := Z.isClosed.preimage m.left.continuous
    have hcl : closedPoints (G.X ⊗ O).left ⊆ m.left ⁻¹' (Z : Set X.left) := by
      intro w hw
      let p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X ⊗ O :=
        Over.homMk (pointOfClosedPoint (G.X ⊗ O).hom w hw) (by simp)
      have hpw : p.left (IsLocalRing.closedPoint k) = w := pointOfClosedPoint_apply _ _ _ _
      have hp : p ≫ m = a.act (p ≫ fst _ _) ((p ≫ snd _ _) ≫ j) := by
        rw [SchemeAction.act]
        simp only [m, ← Category.assoc]
        congr 1
        apply CartesianMonoidalCategory.hom_ext <;> simp
      have h := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hp
      simp only [Over.comp_left, Scheme.Hom.comp_apply, hpw] at h
      change m.left w ∈ (Z : Set X.left)
      rw [h, act_apply]
      apply hZst
      rw [← hjrange]
      exact ⟨(p ≫ snd _ _).left (IsLocalRing.closedPoint k), by
        simp only [Over.comp_left, Scheme.Hom.comp_apply]⟩
    rintro _ ⟨w, rfl⟩
    have hall := closure_minimal hcl hclosed
    rw [closure_closedPoints] at hall
    exact hall (Set.mem_univ w)
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset j.left m.left hm
  let hom : G.X ⊗ O ⟶ O := Over.homMk l (by
    change l ≫ j.left ≫ X.hom = _
    rw [← Category.assoc, hl]
    exact Over.w m)
  have hhom : hom ≫ j = m := Over.OverMorphism.ext hl
  have hkey : ∀ {T : Over (Spec (CommRingCat.of k))} (f : T ⟶ G.X) (o : T ⟶ O),
      (lift f o ≫ hom) ≫ j = a.act f (o ≫ j) := by
    intro T f o
    rw [Category.assoc, hhom, SchemeAction.act]
    simp only [m, ← Category.assoc, lift_whiskerLeft]
  have hone : ∀ {T : Over (Spec (CommRingCat.of k))} (o : T ⟶ O),
      lift (1 : T ⟶ G.X) o ≫ hom = o := by
    intro T o
    apply hjcancel
    rw [hkey, SchemeAction.act_one]
  have hmul : ∀ {T : Over (Spec (CommRingCat.of k))} (h h' : T ⟶ G.X) (o : T ⟶ O),
      lift (h * h') o ≫ hom = lift h (lift h' o ≫ hom) ≫ hom := by
    intro T h h' o
    apply hjcancel
    rw [hkey, hkey, hkey, SchemeAction.act_mul]
  let b : SchemeAction G O := schemeActionOfPointLaws hom hone hmul
  have hb : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (o : T ⟶ O),
      b.act g o ≫ j = a.act g (o ≫ j) := fun g o => hkey g o
  -- `j` intertwines the actions of rational points.
  have hbj : ∀ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      actBy b g ≫ j = j ≫ actBy a g := by
    intro g
    rw [comp_actBy_of, actBy, hb, Category.id_comp]
  have hbj' : ∀ (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) (w : O.left),
      j.left ((actBy b g).left w) = (actBy a g).left (j.left w) := by
    intro g w
    have := congrArg (fun f => f.left w) (hbj g)
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using this
  -- Minimality of `Z` transfers to `O`.
  have hOmin : ∀ C : Set O.left, IsClosed C → C.Nonempty →
      (∀ (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X), ∀ w ∈ C, (actBy b g).left w ∈ C) →
      C = Set.univ := by
    intro C hC hCne hCst
    let Z' : Closeds X.left := ⟨j.left '' C, j.left.isClosedEmbedding.isClosedMap C hC⟩
    have hZ' : Z' = Z := by
      refine hmin Z' (hCne.image _) ?_ ?_
      · rintro g _ ⟨w, hw, rfl⟩
        exact ⟨_, hCst g w hw, hbj' g w⟩
      · rintro _ ⟨w, -, rfl⟩
        rw [← hjrange]
        exact ⟨w, rfl⟩
    rw [Set.eq_univ_iff_forall]
    intro w
    have hw : j.left w ∈ (Z' : Set X.left) := by
      rw [hZ', ← hjrange]
      exact ⟨w, rfl⟩
    obtain ⟨c, hc, hcw⟩ := hw
    rwa [← j.left.isClosedEmbedding.injective hcw]
  -- A rational point of `O` and its orbit map.
  have : Nonempty O.left := by
    obtain ⟨z, hz⟩ := hZne
    rw [← hjrange] at hz
    obtain ⟨w, -⟩ := hz
    exact ⟨w⟩
  obtain ⟨c₀, -, hc₀⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := O.left))
    isClosed_univ.isLocallyClosed
  let x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O :=
    Over.homMk (pointOfClosedPoint O.hom c₀ hc₀) (by simp)
  set π := b.act (𝟙 G.X) (toUnit G.X ≫ x) with hπ
  have hw : π.left ≫ O.hom = G.X.hom := Over.w π
  have : LocallyOfFiniteType π.left := by
    have : LocallyOfFiniteType (π.left ≫ O.hom) := hw ▸ inferInstance
    exact locallyOfFiniteType_of_comp π.left O.hom
  have : QuasiCompact π.left := by
    have : QuasiCompact (π.left ≫ O.hom) := hw ▸ inferInstance
    exact QuasiCompact.of_comp π.left O.hom
  -- The orbit is stable and dense.
  have hRst : ∀ (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X), ∀ w ∈ Set.range π.left,
      (actBy b g).left w ∈ Set.range π.left := by
    rintro g _ ⟨z, rfl⟩
    refine ⟨(FiniteIndexTransfer.leftMul G g).left z, ?_⟩
    have := congrArg (fun f => f.left z) (leftMul_comp_orbit b g x)
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using this
  have hdense : Dense (Set.range π.left) := by
    rw [dense_iff_closure_eq]
    refine hOmin _ isClosed_closure ?_ ?_
    · exact ⟨_, subset_closure
        ⟨(1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X).left (IsLocalRing.closedPoint k), rfl⟩⟩
    · intro g w hw
      exact map_mem_closure (actBy b g).left.continuous hw (hRst g)
  -- Chevalley: the orbit contains a nonempty open subset.
  have hcons : IsConstructible (Set.range π.left) := by
    rw [← Set.image_univ]
    exact π.left.isConstructible_image IsConstructible.univ
  obtain ⟨N, hN, hNne, hNR⟩ := exists_isOpen_subset_of_dense hcons hdense
  -- Translates of `N` cover `O`.
  have hcover : ∀ w : O.left, ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      (actBy b g).left w ∈ N := by
    by_contra! hno
    obtain ⟨w, hw⟩ := hno
    let C : Set O.left := ⋂ g, (actBy b g).left ⁻¹' Nᶜ
    have hC : C = Set.univ := by
      refine hOmin C (isClosed_iInter fun g => hN.isClosed_compl.preimage
        (actBy b g).left.continuous) ⟨w, Set.mem_iInter.mpr hw⟩ ?_
      intro h v hv
      refine Set.mem_iInter.mpr fun g => ?_
      have := Set.mem_iInter.mp hv (g * h)
      rw [← actBy_comp_actBy] at this
      simpa only [Set.mem_preimage, Over.comp_left, Scheme.Hom.comp_apply] using this
    obtain ⟨v, hvN⟩ := hNne
    have := Set.mem_iInter.mp (show v ∈ C by rw [hC]; trivial) 1
    rw [actBy_one] at this
    exact this hvN
  have hsurj : Function.Surjective π.left := by
    intro w
    obtain ⟨g, hg⟩ := hcover w
    obtain ⟨z, hz⟩ := hRst g⁻¹ _ (hNR hg)
    refine ⟨z, ?_⟩
    rw [hz]
    have := congrArg (fun f => f.left w) (actBy_comp_actBy b g g⁻¹)
    simp only [Over.comp_left, Scheme.Hom.comp_apply, inv_mul_cancel, actBy_one] at this
    exact this
  -- Every rational point of `O` lies in the orbit of `x`.
  refine ⟨O, j, b, x, inferInstance, inferInstance, inferInstance, inferInstance,
    fun T g o => hb g o, fun y => ?_⟩
  have hy : y.left ≫ O.hom = 𝟙 _ := by simp
  have hyc : IsClosed {y.left (IsLocalRing.closedPoint k)} :=
    ((pointEquivClosedPoint O.hom) ⟨y.left, hy⟩).2
  obtain ⟨z₀, hz₀⟩ := hsurj (y.left (IsLocalRing.closedPoint k))
  obtain ⟨z, hzF, hz⟩ := nonempty_inter_closedPoints (Z := π.left ⁻¹' {y.left (IsLocalRing.closedPoint k)})
    ⟨z₀, hz₀⟩ (hyc.preimage π.left.continuous).isLocallyClosed
  let g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom z hz) (by simp)
  refine ⟨g, ?_⟩
  rw [← comp_orbit, ← hπ]
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq O.hom (by simp) hy ?_
  simp only [Over.comp_left, Scheme.Hom.comp_apply]
  exact (congrArg π.left (pointOfClosedPoint_apply G.X.hom z hz _)).trans hzF

end Langlands.GroupScheme
