import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement
import Langlands.AlgebraicGeometry.Picard.LocalEquationCartier
import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealLocalFreeness
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionDivisors
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Langlands.CommutativeAlgebra.CartierLocusDescent

/-! # Proof that the relative effective Cartier locus is open and stable under base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocus

open StructureKernelModule

section Local

variable {X : Scheme.{u}}

/-- Near `x`, the ideal `I` is generated on an affine open by one regular function. -/
def HasLocalEquation (I : X.IdealSheafData) (x : X) : Prop :=
  ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ s : Γ(X, W.1),
    I.ideal W = Ideal.span {s} ∧ IsSMulRegular Γ(X, W.1) s

/-- **Effective Cartier ideals have local equations.** -/
theorem hasLocalEquation_of_isEffectiveCartierIdeal {I : X.IdealSheafData}
    (hI : IsEffectiveCartierIdeal I) (x : X) : HasLocalEquation I x := by
  obtain ⟨O, hxO, e, he⟩ := OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne hI x
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hxO
  have hWO' : W ≤ O := hWO
  let K := kernelModule I.subschemeι
  let σ : Γ(K, W) := K.presheaf.map (homOfLE hWO').op e
  have hsmul : ∀ (g : Γ(X, W)) (m : Γ(K, W)), (g • m).val = g * m.val := by
    intro g m
    exact Scheme.Modules.Hom.app_smul (kernelModuleι I.subschemeι) g m
  have hbij := he hWO' hWO'
  have hmem : ∀ a : Γ(X, W), a ∈ I.ideal ⟨W, hW⟩ ↔
      a ∈ RingHom.ker (I.subschemeι.app W).hom := by
    intro a
    rw [I.ker_subschemeι_app ⟨W, hW⟩]
  refine ⟨⟨W, hW⟩, hxW, σ.val, ?_, ?_⟩
  · apply le_antisymm
    · intro a ha
      obtain ⟨g, hg⟩ := hbij.2 ⟨a, (hmem a).1 ha⟩
      rw [Ideal.mem_span_singleton']
      refine ⟨g, ?_⟩
      have := congrArg Subtype.val hg
      rw [hsmul] at this
      exact this
    · rw [Ideal.span_singleton_le_iff_mem, hmem]
      exact σ.property
  · rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro g hg
    apply hbij.1
    change g • σ = (0 : Γ(X, W)) • σ
    rw [zero_smul]
    apply Subtype.ext
    rw [hsmul]
    rw [smul_eq_mul, mul_comm] at hg
    exact hg

/-- Regular elements stay regular along a flat ring homomorphism. -/
theorem isSMulRegular_map_of_flat {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.Flat) {s : R} (hs : IsSMulRegular R s) : IsSMulRegular S (φ s) := by
  let _ := φ.toAlgebra
  have : Module.Flat R S := hφ
  exact hs.of_flat

/-- **Local equations pull back along flat morphisms.** -/
theorem hasLocalEquation_comap {X' : Scheme.{u}} (f : X' ⟶ X) [Flat f] {I : X.IdealSheafData}
    {x : X'} (h : HasLocalEquation I (f.base x)) : HasLocalEquation (I.comap f) x := by
  obtain ⟨W, hxW, s, hgen, hreg⟩ := h
  obtain ⟨W', hW', hxW', hW'le⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ W.1) (x := x) hxW
  have hle : W' ≤ f ⁻¹ᵁ W.1 := hW'le
  refine ⟨⟨W', hW'⟩, hxW', (f.appLE W.1 W' hle).hom s, ?_, ?_⟩
  · rw [I.ideal_comap_of_le f W ⟨W', hW'⟩ hle, hgen, Ideal.map_span, Set.image_singleton]
  · exact isSMulRegular_map_of_flat _
      (HasRingHomProperty.appLE @Flat f ‹_› W ⟨W', hW'⟩ hle) hreg

/-- The points with a local equation form an open set. -/
theorem isOpen_setOf_hasLocalEquation (I : X.IdealSheafData) :
    IsOpen {x : X | HasLocalEquation I x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hxW, s, hgen, hreg⟩ := hx
  exact ⟨W.1, fun y hy => ⟨W, hy, s, hgen, hreg⟩, W.1.2, hxW⟩

end Local

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The ring map from sections near `f x` to the stalk of the source at `x`. -/
def stalkHom (W : Y.Opens) (h : f.base x ∈ W) : Γ(Y, W) →+* X.presheaf.stalk x :=
  (Y.presheaf.germ W (f.base x) h ≫ f.stalkMap x).hom

lemma stalkHom_eq_comp_appLE (W : Y.Opens) (h : f.base x ∈ W) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ W)
    (hx : x ∈ V) :
    stalkHom f x W h = (X.presheaf.germ V x hx).hom.comp (f.appLE W V e).hom := by
  ext a
  simp [stalkHom, Scheme.Hom.appLE]

/-- A section becomes a unit in the stalk exactly on its basic open. -/
lemma isUnit_stalkHom_iff (W : Y.Opens) (h : f.base x ∈ W) (a : Γ(Y, W)) :
    IsUnit (stalkHom f x W h a) ↔ f.base x ∈ Y.basicOpen a := by
  rw [Scheme.mem_basicOpen _ _ _ h]
  exact isUnit_map_iff (f.stalkMap x).hom _

/-- On an affine open, the stalk is flat over the sections. -/
lemma flat_germ {V : X.Opens} (hV : IsAffineOpen V) (hx : x ∈ V) :
    (X.presheaf.germ V x hx).hom.Flat := by
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have : Module.Flat Γ(X, V) (X.presheaf.stalk x) :=
    IsLocalization.flat _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact this

/-- **The pulled-back ideal at a stalk.** If the pulled-back ideal has a regular local equation
near `x`, then on every affine open around `f x` the ideal generates the same principal ideal of
the stalk, with a regular generator. -/
lemma map_stalkHom_eq (I : Y.IdealSheafData) {W' : X.affineOpens} (hxW' : x ∈ W'.1)
    {s' : Γ(X, W'.1)} (hs' : (I.comap f).ideal W' = Ideal.span {s'}) (W : Y.affineOpens)
    (h : f.base x ∈ W.1) :
    (I.ideal W).map (stalkHom f x W.1 h) = Ideal.span {X.presheaf.germ W'.1 x hxW' s'} := by
  have hx3 : x ∈ W'.1 ⊓ f ⁻¹ᵁ W.1 := ⟨hxW', h⟩
  obtain ⟨U₃, hU₃, hxU₃, hU₃le⟩ := exists_isAffineOpen_mem_and_subset hx3
  have hle : U₃ ≤ W'.1 ⊓ f ⁻¹ᵁ W.1 := hU₃le
  have h1 := I.ideal_comap_of_le f W ⟨U₃, hU₃⟩ (hle.trans inf_le_right)
  have h2 := (I.comap f).map_ideal (U := ⟨U₃, hU₃⟩) (V := W') (hle.trans inf_le_left)
  rw [hs', Ideal.map_span, Set.image_singleton] at h2
  rw [stalkHom_eq_comp_appLE f x W.1 h U₃ (hle.trans inf_le_right) hxU₃, ← Ideal.map_map,
    ← h1, ← h2, Ideal.map_span, Set.image_singleton]
  congr 2
  exact X.presheaf.germ_res_apply _ _ _ _

end Stalk

section Chart

variable {B Y T YT : Scheme.{u}} {q : Y ⟶ B} {g : T ⟶ B} {gY : YT ⟶ Y} {qT : YT ⟶ T}

/-- Flatness of the closed subscheme over the base gives flatness of the quotient ring on each
affine chart. -/
lemma flat_quotient (Z : Y.IdealSheafData) [Flat (Z.subschemeι ≫ q)] (VB : B.affineOpens)
    (W : Y.affineOpens) (hWB : W.1 ≤ q ⁻¹ᵁ VB.1) :
    ((Ideal.Quotient.mk (Z.ideal W)).comp (q.appLE VB.1 W.1 hWB).hom).Flat := by
  have e : Z.subschemeι ⁻¹ᵁ W.1 ≤ (Z.subschemeι ≫ q) ⁻¹ᵁ VB.1 := fun y hy => hWB hy
  have hU' : IsAffineOpen (Z.subschemeι ⁻¹ᵁ W.1) := W.2.preimage _
  have hflat := HasRingHomProperty.appLE @Flat (Z.subschemeι ≫ q) ‹_› VB ⟨_, hU'⟩ e
  have heq : (Z.subschemeι ≫ q).appLE VB.1 (Z.subschemeι ⁻¹ᵁ W.1) e =
      q.appLE VB.1 W.1 hWB ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal W)) ≫
        (Z.subschemeObjIso W).inv := by
    rw [← Z.subschemeι_app W, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have heq' : q.appLE VB.1 W.1 hWB ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal W)) =
      (Z.subschemeι ≫ q).appLE VB.1 (Z.subschemeι ⁻¹ᵁ W.1) e ≫ (Z.subschemeObjIso W).hom := by
    rw [heq]
    simp
  have := congrArg CommRingCat.Hom.hom heq'
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
  rw [this]
  exact RingHom.Flat.comp hflat
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Z.subschemeObjIso W).hom))

variable (sq : IsPullback gY qT q g) (Z : Y.IdealSheafData)

include sq in
/-- **The chart lemma.** Over affine charts `VB` of `B` and `VT` of `T`, and for an affine open
`W` of `Y` over `VB` containing the image of `y'`, the descent results of
`CartierLocusDescent` apply to the ring map from `Γ(Y, W)` to the stalk of `YT` at `y'`. -/
theorem chart [IsLocallyNoetherian Y] [Flat q] [Flat (Z.subschemeι ≫ q)]
    (VB : B.affineOpens) (VT : T.affineOpens) (hVTB : VT.1 ≤ g ⁻¹ᵁ VB.1)
    (y' : YT) (hy'T : qT.base y' ∈ VT.1)
    (W : Y.affineOpens) (hWB : W.1 ≤ q ⁻¹ᵁ VB.1) (hy'W : gY.base y' ∈ W.1) :
    (∀ f ∈ Z.ideal W, (Z.ideal W).map (stalkHom gY y' W.1 hy'W) =
        Ideal.span {stalkHom gY y' W.1 hy'W f} →
        ∃ a : Γ(Y, W.1), IsUnit (stalkHom gY y' W.1 hy'W a) ∧
          ∀ x ∈ Z.ideal W, ∃ r, a * x = r * f) ∧
    (∀ f : Γ(Y, W.1), Z.ideal W = Ideal.span {f} →
        IsSMulRegular (YT.presheaf.stalk y') (stalkHom gY y' W.1 hy'W f) →
        ∃ a : Γ(Y, W.1), IsUnit (stalkHom gY y' W.1 hy'W a) ∧
          ∀ r, r * f = 0 → a * r = 0) := by
  set UY : YT.Opens := gY ⁻¹ᵁ W.1 ⊓ qT ⁻¹ᵁ VT.1 with hUY
  have hy'UY : y' ∈ UY := ⟨hy'W, hy'T⟩
  have hUY1 : UY ≤ gY ⁻¹ᵁ W.1 := inf_le_left
  have hUY2 : UY ≤ qT ⁻¹ᵁ VT.1 := inf_le_right
  have hUYaff : IsAffineOpen UY := by
    have : IsAffine VB.1 := VB.2
    have : IsAffine VT.1 := VT.2
    have : IsAffine W.1 := W.2
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq hVTB hWB hUY).isoPullback.hom
  have hP := (isIso_pushoutSection_iff sq hVTB hWB hUY).mp
    (isIso_pushoutSection_of_isAffineOpen sq hVTB hWB hUY VB.2 VT.2 W.2)
  let _ : Algebra Γ(B, VB.1) Γ(Y, W.1) := (q.appLE VB.1 W.1 hWB).hom.toAlgebra
  let _ : Algebra Γ(B, VB.1) Γ(T, VT.1) := (g.appLE VB.1 VT.1 hVTB).hom.toAlgebra
  let _ : Algebra Γ(Y, W.1) Γ(YT, UY) := (gY.appLE W.1 UY hUY1).hom.toAlgebra
  let _ : Algebra Γ(T, VT.1) Γ(YT, UY) := (qT.appLE VT.1 UY hUY2).hom.toAlgebra
  let _ : Algebra Γ(B, VB.1) Γ(YT, UY) :=
    (q.appLE VB.1 W.1 hWB ≫ gY.appLE W.1 UY hUY1).hom.toAlgebra
  have : IsScalarTower Γ(B, VB.1) Γ(Y, W.1) Γ(YT, UY) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(B, VB.1) Γ(T, VT.1) Γ(YT, UY) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hP.w)
  have : Algebra.IsPushout Γ(B, VB.1) Γ(Y, W.1) Γ(T, VT.1) Γ(YT, UY) :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  let _ : Algebra Γ(YT, UY) (YT.presheaf.stalk y') :=
    (YT.presheaf.germ UY y' hy'UY).hom.toAlgebra
  let _ : Algebra Γ(Y, W.1) (YT.presheaf.stalk y') := (stalkHom gY y' W.1 hy'W).toAlgebra
  have : IsScalarTower Γ(Y, W.1) Γ(YT, UY) (YT.presheaf.stalk y') :=
    IsScalarTower.of_algebraMap_eq' (stalkHom_eq_comp_appLE gY y' W.1 hy'W UY hUY1 hy'UY)
  have : Module.Flat Γ(YT, UY) (YT.presheaf.stalk y') := flat_germ y' hUYaff hy'UY
  have : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
  have : Module.Flat Γ(B, VB.1) Γ(Y, W.1) := HasRingHomProperty.appLE @Flat q ‹_› VB W hWB
  have hQ : Module.Flat Γ(B, VB.1) (Γ(Y, W.1) ⧸ Z.ideal W) := by
    rw [← RingHom.flat_algebraMap_iff, ← Ideal.Quotient.mk_comp_algebraMap]
    exact flat_quotient Z VB W hWB
  constructor
  · intro f hf hgen
    exact CommutativeAlgebra.CartierLocusDescent.exists_mul_eq_of_map_eq_span (A := Γ(B, VB.1))
      (A' := Γ(T, VT.1)) (S := Γ(YT, UY)) (YT.presheaf.stalk y') (Z.ideal W) hf hgen
  · intro f hspan hreg
    have : Module.Flat Γ(B, VB.1) (Γ(Y, W.1) ⧸ Ideal.span {f}) := hspan ▸ hQ
    exact CommutativeAlgebra.CartierLocusDescent.exists_mul_eq_zero_of_isSMulRegular (A := Γ(B, VB.1))
      (A' := Γ(T, VT.1)) (S := Γ(YT, UY)) (YT.presheaf.stalk y') f hreg

include sq in
/-- **Descent of local equations (Kleiman, proof of Theorem 3.7).** If the pulled-back ideal
has a regular local equation at `y'`, then `Z` has a regular local equation at the image of `y'`
in `Y`. -/
theorem hasLocalEquation_of_comap [IsLocallyNoetherian Y] [Flat q] [Flat (Z.subschemeι ≫ q)]
    (y' : YT) (hZ : HasLocalEquation (Z.comap gY) y') : HasLocalEquation Z (gY.base y') := by
  obtain ⟨W', hy'W', s', hs', hreg'⟩ := hZ
  set t₀ := YT.presheaf.germ W'.1 y' hy'W' s' with ht₀
  have ht₀reg : IsSMulRegular (YT.presheaf.stalk y') t₀ :=
    isSMulRegular_map_of_flat _ (flat_germ y' W'.2 hy'W') hreg'
  have hw : q.base (gY.base y') = g.base (qT.base y') := by
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
  obtain ⟨VB, hVB, hbVB, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := g.base (qT.base y')) trivial
  obtain ⟨VT, hVT, htVT, hVTle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ VB) (x := qT.base y') hbVB
  have hbVB' : q.base (gY.base y') ∈ VB := hw ▸ hbVB
  obtain ⟨W, hW, hyW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := q ⁻¹ᵁ VB) (x := gY.base y') hbVB'
  have hVTB : VT ≤ g ⁻¹ᵁ VB := hVTle
  have hWB : W ≤ q ⁻¹ᵁ VB := hWle
  -- Step A: on `W`, the ideal is generated by one element after multiplying by a unit at `y'`.
  obtain ⟨K₁, -⟩ := chart sq Z ⟨VB, hVB⟩ ⟨VT, hVT⟩ hVTB y' htVT ⟨W, hW⟩ hWB hyW
  have hmap := map_stalkHom_eq gY y' Z hy'W' hs' ⟨W, hW⟩ hyW
  obtain ⟨f, hf, hfgen, -⟩ := CommutativeAlgebra.CartierLocusDescent.exists_mem_map_eq_span
    (stalkHom gY y' W hyW) (Z.ideal ⟨W, hW⟩) hmap ht₀reg
  obtain ⟨a, ha, hmul⟩ := K₁ f hf hfgen
  -- Step B: on the basic open `D(a)`, the ideal is principal.
  have hW₁ : IsAffineOpen (Y.basicOpen a) := hW.basicOpen a
  have hyW₁ : gY.base y' ∈ Y.basicOpen a := (isUnit_stalkHom_iff gY y' W hyW a).1 ha
  have hW₁B : Y.basicOpen a ≤ q ⁻¹ᵁ VB := (Y.basicOpen_le a).trans hWB
  have : IsLocalization.Away a Γ(Y, Y.basicOpen a) := hW.isLocalization_basicOpen a
  set f₁ : Γ(Y, Y.basicOpen a) := algebraMap Γ(Y, W) Γ(Y, Y.basicOpen a) f with hf₁
  have hZW₁ : Z.ideal ⟨Y.basicOpen a, hW₁⟩ = Ideal.span {f₁} := by
    rw [hf₁, ← CommutativeAlgebra.CartierLocusDescent.map_eq_span_of_mul_eq a _ hf hmul]
    exact (Z.map_ideal_basicOpen ⟨W, hW⟩ a).symm
  -- Step C: on `D(a)`, the generator is killed only by elements vanishing near `y`.
  obtain ⟨-, K₂⟩ := chart sq Z ⟨VB, hVB⟩ ⟨VT, hVT⟩ hVTB y' htVT ⟨Y.basicOpen a, hW₁⟩ hW₁B hyW₁
  have hreg₁ : IsSMulRegular (YT.presheaf.stalk y') (stalkHom gY y' (Y.basicOpen a) hyW₁ f₁) := by
    have hmap₁ := map_stalkHom_eq gY y' Z hy'W' hs' ⟨Y.basicOpen a, hW₁⟩ hyW₁
    rw [hZW₁, Ideal.map_span, Set.image_singleton] at hmap₁
    apply CommutativeAlgebra.CartierLocusDescent.isSMulRegular_of_mem_span _ ht₀reg
    rw [hmap₁]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨a₂, ha₂, hann⟩ := K₂ f₁ hZW₁ hreg₁
  -- Step D: on the basic open `D(a₂)` the generator is regular.
  have hW₂ : IsAffineOpen (Y.basicOpen a₂) := hW₁.basicOpen a₂
  have hyW₂ : gY.base y' ∈ Y.basicOpen a₂ :=
    (isUnit_stalkHom_iff gY y' (Y.basicOpen a) hyW₁ a₂).1 ha₂
  have : IsLocalization.Away a₂ Γ(Y, Y.basicOpen a₂) := hW₁.isLocalization_basicOpen a₂
  refine ⟨⟨Y.basicOpen a₂, hW₂⟩, hyW₂,
    algebraMap Γ(Y, Y.basicOpen a) Γ(Y, Y.basicOpen a₂) f₁, ?_, ?_⟩
  · have h := Z.map_ideal_basicOpen ⟨Y.basicOpen a, hW₁⟩ a₂
    rw [hZW₁, Ideal.map_span, Set.image_singleton] at h
    exact h.symm
  · exact CommutativeAlgebra.CartierLocusDescent.isSMulRegular_of_mul_eq_zero a₂ hann

end Chart

section Main

variable {B Y : Scheme.{u}} (q : Y ⟶ B) (Z : Y.IdealSheafData)

/-- The open set of points of `B` over which `Z` has a local equation at every point of the
fibre. It is open because `q` is a closed map. -/
def cartierLocus [UniversallyClosed q] : B.Opens :=
  ⟨(q.base '' {y | HasLocalEquation Z y}ᶜ)ᶜ,
    (q.isClosedMap _ (isOpen_setOf_hasLocalEquation Z).isClosed_compl).isOpen_compl⟩

lemma hasLocalEquation_of_mem_cartierLocus [UniversallyClosed q] {y : Y}
    (hy : q.base y ∈ cartierLocus q Z) : HasLocalEquation Z y := by
  by_contra h
  exact hy ⟨y, h, rfl⟩

lemma mem_cartierLocus [UniversallyClosed q] {b : B}
    (h : ∀ y : Y, q.base y = b → HasLocalEquation Z y) : b ∈ cartierLocus q Z := by
  rintro ⟨y, hy, rfl⟩
  exact hy (h y rfl)

/-- Over `cartierLocus q Z`, the restriction of `Z` is a relative effective Cartier ideal. -/
lemma isRelativeEffectiveCartierIdeal_restrict [UniversallyClosed q] [Flat (Z.subschemeι ≫ q)] :
    IsRelativeEffectiveCartierIdeal (q ∣_ cartierLocus q Z)
      (Z.comap (q ⁻¹ᵁ cartierLocus q Z).ι) := by
  constructor
  · apply LocalEquationCartier.isEffectiveCartierIdeal_of_local
    intro x
    apply hasLocalEquation_comap
    exact hasLocalEquation_of_mem_cartierLocus q Z x.2
  · have h := (PicardHilbertPiecesReduction.isPullback_comap (q ⁻¹ᵁ cartierLocus q Z).ι Z).paste_vert
      (isPullback_morphismRestrict q (cartierLocus q Z)).flip
    exact MorphismProperty.of_isPullback (P := @Flat) h ‹_›

end Main

/-- **The relative effective Cartier locus** (Kleiman, Lemma 3.4 and the proof of Theorem 3.7).
-/
theorem relativeEffectiveCartierLocus : RelativeEffectiveCartierLocusStatement.{u} := by
  intro B Y q Z hB hq hflat hZflat
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  refine ⟨cartierLocus q Z, ?_⟩
  intro T YT g qT gY sq
  constructor
  · intro hZ
    rintro _ ⟨t, rfl⟩
    apply mem_cartierLocus
    intro y hy
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := g) y t hy
    have h1 : gY.base (sq.isoPullback.inv.base z) = y := by
      rw [← hz1, ← sq.isoPullback_inv_fst]
      rfl
    rw [← h1]
    exact hasLocalEquation_of_comap sq Z _ (hasLocalEquation_of_isEffectiveCartierIdeal hZ.1 _)
  · intro hrange
    have hrange' : Set.range g.base ⊆ Set.range (cartierLocus q Z).ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hrange
    let g' : T ⟶ cartierLocus q Z := IsOpenImmersion.lift (cartierLocus q Z).ι g hrange'
    have hg : g' ≫ (cartierLocus q Z).ι = g := IsOpenImmersion.lift_fac _ _ _
    have t := (isPullback_morphismRestrict q (cartierLocus q Z)).flip
    have s : IsPullback gY qT q (g' ≫ (cartierLocus q Z).ι) := by
      rw [hg]
      exact sq
    obtain ⟨hJ, -⟩ := PicardHilbertPiecesReduction.bc_comap
      RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange
      (IsPullback.of_right' s t) _ (isRelativeEffectiveCartierIdeal_restrict q Z)
    rwa [← Scheme.IdealSheafData.comap_comp, t.lift_fst] at hJ

end Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocus
