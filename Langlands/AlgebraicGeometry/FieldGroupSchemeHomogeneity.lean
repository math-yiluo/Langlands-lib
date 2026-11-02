import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Translations of a group scheme over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/-- Over an algebraically closed field, the automorphisms over the base of a locally finite
type group scheme act transitively on its closed points: right translation by the
rational point `x⁻¹ y` maps `x` to `y`. -/
lemma GrpObj.exists_iso_apply_closedPoint (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] (x y : G.left) (hx : IsClosed ({x} : Set G.left))
    (hy : IsClosed ({y} : Set G.left)) :
    ∃ α : G.left ≅ G.left, α.hom ≫ G.hom = G.hom ∧ α.hom x = y := by
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hy⟩).2
  let α := (GrpObj.mulRight (A := G) x').symm ≪≫ (GrpObj.mulRight (A := G) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  exact ⟨(Over.forget _).mapIso α, Over.w α.hom, hα'⟩

/-- Reducedness of stalks passes to generizations: if `y ⤳ x` and the stalk at `x` is
reduced, then so is the stalk at `y`. -/
lemma isReduced_stalk_of_specializes (X : Scheme.{u}) {x y : X} (h : y ⤳ x)
    [_root_.IsReduced (X.presheaf.stalk x)] : _root_.IsReduced (X.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.isOpen hxU
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  refine ⟨fun a ⟨n, ha⟩ => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl a
  rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at ha
  obtain ⟨m, hm⟩ := ha
  have hnil : IsNilpotent (X.presheaf.germ U x hxU (m * r)) := by
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, show ((m : Γ(X, U)) * r) ^ (n + 1) = (m : Γ(X, U)) ^ n * r * (m * r ^ n) by
      ring, hm, mul_zero, map_zero]
  have h0 : X.presheaf.germ U y hyU (m * r) = 0 := by
    rw [← X.presheaf.germ_stalkSpecializes hxU h, CommRingCat.comp_apply,
      IsReduced.eq_zero _ hnil, map_zero]
  rw [IsLocalization.mk'_eq_iff_eq_mul, zero_mul]
  rw [map_mul] at h0
  exact (IsLocalization.map_units (X.presheaf.stalk y) m).mul_right_eq_zero.mp h0

/-- A scheme with a Jacobson underlying space is reduced as soon as its stalks at closed
points are reduced: every point generizes a closed point. -/
lemma isReduced_of_isReduced_stalk_closedPoint (X : Scheme.{u}) [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) :
    IsReduced X := by
  have (y : X) : _root_.IsReduced (X.presheaf.stalk y) := by
    obtain ⟨x, hxy, hx⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty y).closure
      isClosed_closure.isLocallyClosed
    have := h x hx
    exact isReduced_stalk_of_specializes X (specializes_iff_mem_closure.mpr hxy)
  exact isReduced_of_isReduced_stalk X

/-- A smooth scheme over a field whose stalks at all closed points have Krull dimension `g`
is smooth of relative dimension `g`: each standard-smooth chart contains a closed point,
at which the stalk dimension equals the relative dimension of the chart. -/
lemma smoothOfRelativeDimension_of_ringKrullDim_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (g : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨I, J, hJ, hI, ⟨P⟩⟩ := hs.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have hres : SmoothOfRelativeDimension n (f.resLE U V e) := by
    have : IsAffine U := hU
    have : IsAffine V := hV
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    have hP := RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)
    exact ((RingHom.locally_respectsIso hP).arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of hP _ hn)
  have hV' : SmoothOfRelativeDimension n (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    simpa using (inferInstance : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι))
  obtain ⟨z, hzV, hz⟩ := nonempty_inter_closedPoints (Z := (V : Set X)) ⟨x, hxV⟩
    V.isOpen.isLocallyClosed
  have hz' : IsClosed ({⟨z, hzV⟩} : Set V.toScheme) := by
    have : ({⟨z, hzV⟩} : Set V.toScheme) = (Subtype.val : V → X) ⁻¹' {z} :=
      Set.ext fun _ => Subtype.ext_iff
    rw [this]
    exact hz.preimage V.isOpenEmbedding'.continuous
  have hdim := fieldSmoothClosedPointStalkDimension k V.toScheme (V.ι ≫ f) n hV' _ hz'
  rw [ringKrullDim_eq_of_ringEquiv (V.stalkIso ⟨z, hzV⟩).commRingCatIsoToRingEquiv,
    h z hz] at hdim
  have hng : n = g := by exact_mod_cast hdim.symm
  exact ⟨U, hU, V, hV, hxV, e, hng ▸ hn⟩

end Langlands.AlgebraicGeometry
