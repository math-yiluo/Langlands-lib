import Langlands.GroupScheme.Reductive.RootKernelLieAction
import Langlands.GroupScheme.Reductive.RelativeCenterCentrality
import Langlands.GroupScheme.Torus.MaximalSelfCentralizingDescent
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Reductive.AffinePinnedAtlas
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality

/-! # The full centre on a split reductive chart -/

noncomputable section

universe u v

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

/-- All spectrum tests detect containment in a monomorphically represented subgroup. -/
theorem SubgroupFunctor.le_range_of_all_spectrum_tests
    {S : Scheme.{u}} {G H : GroupScheme S} (F : SubgroupFunctor G)
    (i : H ⟶ G) [Mono i.hom.hom]
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S)
      (x : Over.mk f ⟶ G.X), x ∈ F.carrier (Over.mk f) →
        x ∈ (SubgroupFunctor.range i).carrier (Over.mk f)) :
    F ≤ SubgroupFunctor.range i := by
  intro U x hx
  apply (SubgroupFunctor.mem_range_iff_openCover i U.left.affineCover x).mpr
  intro k
  let V := SubgroupFunctor.coverObj U.left.affineCover k
  let a : Over.mk (V.left.isoSpec.inv ≫ V.hom) ⟶ V :=
    Over.homMk V.left.isoSpec.inv rfl
  let b : V ⟶ Over.mk (V.left.isoSpec.inv ≫ V.hom) :=
    Over.homMk V.left.isoSpec.hom (by simp only [Over.mk_hom, Iso.hom_inv_id_assoc])
  have ha : a ≫ (SubgroupFunctor.coverMap U.left.affineCover k ≫ x) ∈
      (SubgroupFunctor.range i).carrier (Over.mk (V.left.isoSpec.inv ≫ V.hom)) :=
    h _ _ _ (F.comp_mem a (F.comp_mem _ hx))
  have hb := (SubgroupFunctor.range i).comp_mem b ha
  have hba : b ≫ a = 𝟙 V := by
    apply Over.OverMorphism.ext
    exact V.left.isoSpec.hom_inv_id
  simpa only [← Category.assoc, hba, Category.id_comp] using hb

namespace Lie

/-- A point of the full scheme centre fixes the actual Lie kernel over its algebra. -/
theorem adjoint_eq_self_of_mem_scheme_center
    {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    {A : Type u} [CommRing A] [Algebra R A] (g : AffinePoints G A)
    (hg : g ∈ (center G).carrier ((algSpec R).obj (op (CommAlgCat.of R A))))
    (X : Additive (lieKernel G A)) : adjoint G A g X = X := by
  have hc := hg _ ((algSpec R).map
    (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R A A)).op) X.toMul.val
  change Commute (constant G g) X.toMul.val at hc
  apply Additive.toMul.injective
  apply Subtype.ext
  change constant G g * X.toMul.val * (constant G g)⁻¹ = X.toMul.val
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

end Lie

namespace splitTorus

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  [Smooth G.X.hom] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- A free rank-one actual exponent summand detects its character value
from triviality of the adjoint action, over every coefficient algebra. -/
theorem exponentValue_eq_one_of_adjoint_eq_on_line
    (m : I → ℤ) (e : exponentWeightSpace I G i m ≃ₗ[R] R)
    {A : Type u} [CommRing A] [Algebra R A] (t : I → Aˣ)
    (ht : ∀ X : Additive (lieKernel G A),
      adjoint G A ((algebraPointsEquiv I A).symm t ≫ i.hom.hom) X = X) :
    exponentValue I t (.ofAdd m) = 1 := by
  let X := e.symm 1
  let l : Additive (lieKernel G (CommRingCat.of R)) →ₗ[R] R :=
    e.toLinearMap.comp (exponentProjection I G i m)
  have hl : l X.val = 1 := by
    change e (exponentProjection I G i m X.val) = 1
    rw [exponentProjection_subtype, LinearEquiv.apply_symm_apply]
  let p : Additive (lieKernel G A) →ₗ[A] A :=
    (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap.comp
      ((l.baseChange A).comp (Lie.smoothKernelScalarExtension G A).symm.toLinearMap)
  have hp : p (lieKernelMapLinear G (Algebra.ofId (CommRingCat.of R) A) X.val) = 1 := by
    have hX := Lie.smoothKernelScalarExtension_tmul G A (1 : A) X.val
    rw [one_smul] at hX
    rw [← hX]
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
      TensorProduct.AlgebraTensorModule.rid_tmul, hl, one_smul]
  have hw := X.property A t
  rw [ht] at hw
  have h := congrArg p hw
  rw [map_smul, hp, smul_eq_mul, mul_one] at h
  exact Units.ext h.symm

/-- Over any coefficient algebra, a torus point whose image is central
kills all the root relations if the actual root lines are free of rank one. -/
theorem mem_exponentKernel_of_mem_center
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hlines : ∀ α : J, Nonempty (exponentWeightSpace I G i (P.root α) ≃ₗ[R] R))
    {A : Type u} [CommRing A] [Algebra R A]
    (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of R)) I) A)
    (ht : t ≫ i.hom.hom ∈ (center G).carrier
      ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)))) :
    t ∈ (SubgroupFunctor.range (Diagonalizable.exponentKernelHom (CommRingCat.of R) I
      (CoordinateRootDatum.rootExponentSpan P))).carrier _ := by
  apply (Diagonalizable.mem_range_exponentKernelHom_iff t).mpr
  have hroot (α : J) :
      exponentValue I (pointsEquiv I _ t) (.ofAdd (P.root α)) = 1 := by
    have h := exponentValue_eq_one_of_adjoint_eq_on_line I G i (P.root α)
      (Classical.choice (hlines α)) (algebraPointsEquiv I A t) (by
        intro X
        rw [MulEquiv.symm_apply_apply]
        exact Lie.adjoint_eq_self_of_mem_scheme_center G _ ht X)
    rw [← characterValue_exponentCharacter] at h
    let q := Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv
    change q (Gm.pointsEquiv _ _ (t ≫
      (CommGroupScheme.groupHom
        (exponentCharacter (Spec (CommRingCat.of R)) I (P.root α))).hom.hom)) = 1 at h
    rw [pointsEquiv_exponentCharacter] at h
    exact q.injective (h.trans (map_one q).symm)
  intro m hm
  induction hm using AddSubgroup.closure_induction with
  | mem m hm =>
    obtain ⟨α, rfl⟩ := hm
    exact hroot α
  | zero => exact map_one _
  | add m n hm hn ih_m ih_n =>
    change exponentValue I (pointsEquiv I _ t) (.ofAdd m * .ofAdd n) = 1
    rw [map_mul, ih_m, ih_n, mul_one]
  | neg m hm ih =>
    change exponentValue I (pointsEquiv I _ t) ((.ofAdd m)⁻¹) = 1
    rw [map_inv, ih, inv_one]

/-- The full root-character kernel is the full scheme-theoretic centre
on a split chart with a fibrewise maximal torus and trivialized root lines. -/
theorem isSchemeTheoreticCenter_rootKernelHom
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := commGroupScheme (Spec (CommRingCat.of R)) I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hlines : ∀ α : J, Nonempty (exponentWeightSpace I G i (P.root α) ≃ₗ[R] R)) :
    IsSchemeTheoreticCenter (rootKernelHom I G i P) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hk := Diagonalizable.isClosedSubgroup_exponentKernelHom (CommRingCat.of R) I
    (CoordinateRootDatum.rootExponentSpan P)
  have hclosed : IsClosedSubgroup (rootKernelHom I G i P) := by
    let : IsClosedImmersion
        (Diagonalizable.exponentKernelHom (CommRingCat.of R) I
          (CoordinateRootDatum.rootExponentSpan P)).hom.hom.left := hk
    let : IsClosedImmersion i.hom.hom.left := hi
    change IsClosedImmersion
      ((Diagonalizable.exponentKernelHom (CommRingCat.of R) I
        (CoordinateRootDatum.rootExponentSpan P)).hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have hct : center G ≤ SubgroupFunctor.range i :=
    center_le_range_relativeMaximalTorus (T := commGroupScheme (Spec (CommRingCat.of R)) I)
      hG (RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)) i hi hmax
  refine ⟨hclosed, le_antisymm ?_ ?_⟩
  · apply (isCentral_iff_range_le_center _).mp
    exact Diagonalizable.isCentral_of_adjoint_eq (rootKernelHom I G i P) hG
      (fun A _ _ x X => adjoint_rootKernelHom_eq_self I G i P hP x X)
  · let : IsClosedImmersion (rootKernelHom I G i P).hom.hom.left := hclosed
    let : Mono (rootKernelHom I G i P).hom.hom := Over.mono_of_mono_left _
    apply SubgroupFunctor.le_range_of_all_spectrum_tests
    intro A f x hx
    obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective f
    let : Algebra R A := φ.hom.toAlgebra
    subst f
    change Lie.AffinePoints G A at x
    obtain ⟨t, ht⟩ := hct _ hx
    change t ≫ i.hom.hom = x at ht
    have htc : t ≫ i.hom.hom ∈ (center G).carrier _ := by
      rw [ht]
      exact hx
    obtain ⟨z, hz⟩ := mem_exponentKernel_of_mem_center I G i P hlines t htc
    change z ≫ (Diagonalizable.exponentKernelHom (CommRingCat.of R) I
      (CoordinateRootDatum.rootExponentSpan P)).hom.hom = t at hz
    refine ⟨z, ?_⟩
    change z ≫ ((Diagonalizable.exponentKernelHom (CommRingCat.of R) I
      (CoordinateRootDatum.rootExponentSpan P)).hom.hom ≫ i.hom.hom) = x
    rw [← Category.assoc, hz, ht]

omit [DecidableEq I] in
/-- The full root-character kernel is relatively diagonalizable, including
its finite and non-smooth factors. -/
theorem isDiagonalizable_rootKernel {J : Type v}
    (P : RootDatum J (I → ℤ) (I → ℤ)) :
    RelativeMultiplicativeType.IsDiagonalizable (rootKernel (R := R) I P).toGrp :=
  Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of R)
    (Diagonalizable.exponentKernelLattice I (CoordinateRootDatum.rootExponentSpan P))

end splitTorus

namespace AffinePinnedModel

/-- The explicit full root-character kernel of a supplied affine pinned model. -/
abbrev centerKernel (M : AffinePinnedModel.{u}) : GroupScheme M.base :=
  (splitTorus.rootKernel (R := M.ring) M.coordinates M.rootDatum).toGrp

/-- The inclusion of the full root-character kernel of a pinned model. -/
def centerKernelHom (M : AffinePinnedModel.{u}) : M.centerKernel ⟶ M.group := by
  classical
  exact splitTorus.rootKernelHom M.coordinates M.group M.inclusion M.rootDatum

/-- The explicit kernel represents the full centre of a pinned model. -/
theorem centerKernel_isSchemeTheoreticCenter (M : AffinePinnedModel.{u}) :
    IsSchemeTheoreticCenter M.centerKernelHom := by
  classical
  let : Smooth M.group.X.hom := M.reductive.smooth
  exact splitTorus.isSchemeTheoreticCenter_rootKernelHom M.coordinates M.group M.inclusion
    M.reductive M.closed M.maximal M.rootDatum M.fibrewiseRootDatum M.rootLines

/-- The pinned-model centre is relatively diagonalizable. -/
theorem centerKernel_isDiagonalizable (M : AffinePinnedModel.{u}) :
    RelativeMultiplicativeType.IsDiagonalizable M.centerKernel :=
  splitTorus.isDiagonalizable_rootKernel M.coordinates M.rootDatum

end AffinePinnedModel

end Langlands.GroupScheme
