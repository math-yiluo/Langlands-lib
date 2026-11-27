import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Global.LocalModularCharacter.ChartLie
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! # Identity tangent vectors of `G(F_∞)` as dual-number points

For an affine group scheme `G` over a number field `F` with a smooth structure, a tangent vector
`X` at the identity of the real Lie group `G(F_∞)` differentiates every global regular function
`a` of `G`: at each infinite place `v` the value `a(x)_v ∈ F_v` is a smooth function of `x`, and
`D_X a ∈ F_∞` collects the derivatives at the identity along `X`. The map
`a ↦ a(1) + ε D_X a` is an algebra map into the dual numbers over `F_∞`, that is, a point of
`G(F_∞[ε])` reducing to the identity. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- The value at the infinite place `v` of a global regular function `a` at a point of
`G(F_∞)`. -/
def placeValue (v : InfinitePlace F) (a : AffineCoordinateRing F G.X) (x : InfiniteAdelicGroupPoints F G) :
    v.Completion :=
  G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v

omit [NumberField F] [IsAffine G.X.left] in
theorem placeValue_add (v : InfinitePlace F) (a b : AffineCoordinateRing F G.X) :
    placeValue F v (a + b) = placeValue F v a + placeValue F v b := by
  funext x
  exact congrFun (map_add (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x)
    a b) v

omit [NumberField F] [IsAffine G.X.left] in
theorem placeValue_mul (v : InfinitePlace F) (a b : AffineCoordinateRing F G.X) :
    placeValue F v (a * b) = placeValue F v a * placeValue F v b := by
  funext x
  exact congrFun (map_mul (G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x)
    a b) v

omit [NumberField F] in
theorem placeValue_algebraMap (v : InfinitePlace F) (r : F) :
    placeValue F v (algebraMap F (AffineCoordinateRing F G.X) r) =
      fun _ => (algebraMap F (InfiniteAdeleRing F) r) v := by
  funext x
  have h := (affineSchemePointEquiv F G.X (CommAlgCat.of F (InfiniteAdeleRing F)) x).commutes r
  change G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x _ v = _
  rw [← G.affineSchemePointEquiv_evaluation]
  exact congrFun h v

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

theorem contMDiff_placeValue (v : InfinitePlace F) (a : AffineCoordinateRing F G.X) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞ (placeValue F v a) :=
  contMDiff_completionEvaluation F G hsmooth v a

/-- The derivatives at the identity, along a tangent vector, of the place values of a global
regular function. -/
def regularDerivative
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (a : AffineCoordinateRing F G.X) : InfiniteAdeleRing F := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact fun v => (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 X :
    v.Completion)


/-- The value of a global regular function at the identity of `G(F_∞)`. -/
abbrev identityValue (a : AffineCoordinateRing F G.X) : InfiniteAdeleRing F :=
  G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) 1 a

section Derivative

variable (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))

theorem regularDerivative_add (a b : AffineCoordinateRing F G.X) :
    regularDerivative F hsmooth X (a + b) =
      regularDerivative F hsmooth X a + regularDerivative F hsmooth X b := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  funext v
  have ha := ((contMDiff_placeValue F hsmooth v a) 1).mdifferentiableAt (by simp)
  have hb := ((contMDiff_placeValue F hsmooth v b) 1).mdifferentiableAt (by simp)
  change mfderiv _ _ (placeValue F v (a + b)) 1 X =
    mfderiv _ _ (placeValue F v a) 1 X + mfderiv _ _ (placeValue F v b) 1 X
  rw [placeValue_add, mfderiv_add ha hb]
  rfl

theorem regularDerivative_mul (a b : AffineCoordinateRing F G.X) :
    regularDerivative F hsmooth X (a * b) =
      identityValue F a * regularDerivative F hsmooth X b +
        identityValue F b * regularDerivative F hsmooth X a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  funext v
  have ha := ((contMDiff_placeValue F hsmooth v a) 1).mdifferentiableAt (by simp)
  have hb := ((contMDiff_placeValue F hsmooth v b) 1).mdifferentiableAt (by simp)
  have h := (ha.hasMFDerivAt.mul hb.hasMFDerivAt).mfderiv
  change mfderiv _ _ (placeValue F v (a * b)) 1 X = _
  rw [placeValue_mul, h]
  rfl

theorem regularDerivative_algebraMap (r : F) :
    regularDerivative F hsmooth X (algebraMap F (AffineCoordinateRing F G.X) r) = 0 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  funext v
  change mfderiv _ _ (placeValue F v (algebraMap F (AffineCoordinateRing F G.X) r)) 1 X = 0
  rw [placeValue_algebraMap, mfderiv_const]
  rfl

omit [NumberField F] in
theorem identityValue_algebraMap (r : F) :
    identityValue F (G := G) (algebraMap F (AffineCoordinateRing F G.X) r) =
      algebraMap F (InfiniteAdeleRing F) r := by
  funext v
  exact congrFun (placeValue_algebraMap F v r) 1

theorem regularDerivative_one :
    regularDerivative F hsmooth X (1 : AffineCoordinateRing F G.X) = 0 := by
  have h := regularDerivative_algebraMap F hsmooth X 1
  rwa [map_one] at h

theorem regularDerivative_zero :
    regularDerivative F hsmooth X (0 : AffineCoordinateRing F G.X) = 0 := by
  have h := regularDerivative_algebraMap F hsmooth X 0
  rwa [map_zero] at h

/-- The algebra map `a ↦ a(1) + ε D_X a` into the dual numbers over `F_∞`. -/
def tangentAlgHom : AffineCoordinateRing F G.X →ₐ[F] DualNumber (InfiniteAdeleRing F) where
  toFun a := TrivSqZeroExt.inl (identityValue F a) +
    TrivSqZeroExt.inr (regularDerivative F hsmooth X a)
  map_one' := by
    have h1 : identityValue F (G := G) (1 : AffineCoordinateRing F G.X) = 1 := map_one _
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, h1,
        TrivSqZeroExt.fst_one]
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        regularDerivative_one, TrivSqZeroExt.snd_one]
  map_mul' a b := by
    have h1 : identityValue F (G := G) (a * b) = identityValue F a * identityValue F b :=
      map_mul _ a b
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.fst_mul, h1]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      rw [regularDerivative_mul]
      ring
  map_zero' := by
    have h1 : identityValue F (G := G) (0 : AffineCoordinateRing F G.X) = 0 := map_zero _
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, h1,
        TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        regularDerivative_zero, TrivSqZeroExt.snd_zero]
  map_add' a b := by
    have h1 : identityValue F (G := G) (a + b) = identityValue F a + identityValue F b :=
      map_add _ a b
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        h1]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rw [regularDerivative_add]
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.fst_inl, identityValue_algebraMap]
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_inl, regularDerivative_algebraMap]

theorem tangentAlgHom_fst (a : AffineCoordinateRing F G.X) :
    (tangentAlgHom F hsmooth X a).fst = identityValue F a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber (InfiniteAdeleRing F)).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

theorem tangentAlgHom_snd (a : AffineCoordinateRing F G.X) :
    (tangentAlgHom F hsmooth X a).snd = regularDerivative F hsmooth X a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber (InfiniteAdeleRing F)).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The dual-number point `a ↦ a(1) + ε D_X a` of `G` over `F_∞`. -/
def tangentPoint : Lie.AffinePoints G (DualNumber (InfiniteAdeleRing F)) :=
  (affineSchemePointEquiv F G.X (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))).symm
    (AlgPoint.ofAlgHom (tangentAlgHom F hsmooth X))

theorem affinePointEvaluation_tangentPoint (a : AffineCoordinateRing F G.X) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentPoint F hsmooth X) a = tangentAlgHom F hsmooth X a := by
  rw [← G.affineSchemePointEquiv_evaluation, tangentPoint, Equiv.apply_symm_apply]
  rfl

theorem reduction_tangentPoint : Lie.reduction G (tangentPoint F hsmooth X) = 1 := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (InfiniteAdeleRing F))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F))
    (Lie.affineMap G (TrivSqZeroExt.fstHom F (InfiniteAdeleRing F) (InfiniteAdeleRing F))
      (tangentPoint F hsmooth X)) a = identityValue F a
  rw [LocalModularCharacter.affinePointEvaluation_affineMap]
  have h := affinePointEvaluation_tangentPoint F hsmooth X a
  exact (congrArg (TrivSqZeroExt.fstHom F (InfiniteAdeleRing F) (InfiniteAdeleRing F)) h).trans
    (tangentAlgHom_fst F hsmooth X a)

/-- The tangent vector `X` as an element of the dual-number identity kernel of `G` over
`F_∞`. -/
def tangentKernel : lieKernel G (InfiniteAdeleRing F) :=
  ⟨tangentPoint F hsmooth X, reduction_tangentPoint F hsmooth X⟩

/-- The infinitesimal part of the value of a regular function at the tangent point is its
derivative along `X`. -/
theorem affinePointEvaluation_tangentPoint_snd (a : AffineCoordinateRing F G.X) :
    (G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentPoint F hsmooth X) a).snd = regularDerivative F hsmooth X a :=
  (congrArg TrivSqZeroExt.snd (affinePointEvaluation_tangentPoint F hsmooth X a)).trans
    (tangentAlgHom_snd F hsmooth X a)

/-- For a morphism `j : G ⟶ H` and a regular function `b` of `H`, the derivative along `X` of
`b ∘ j` is the infinitesimal part of the value of `b` at the image of the tangent point. -/
theorem regularDerivative_comp {H : GroupScheme (Spec (CommRingCat.of F))} (j : G ⟶ H)
    (b : AffineCoordinateRing F H.X) :
    regularDerivative F hsmooth X (j.hom.hom.left.appTop b) =
      (H.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentPoint F hsmooth X ≫ j.hom.hom) b).snd := by
  exact (affinePointEvaluation_tangentPoint_snd F hsmooth X _).symm

end Derivative

section Linear

attribute [local instance] Lie.coordinateOriginAlgebra

omit [NumberField F] in
/-- A dual-number kernel point evaluates a regular function to its value at the identity plus
`ε` times the corresponding identity derivation. -/
theorem affinePointEvaluation_lieKernel (x : lieKernel G (InfiniteAdeleRing F))
    (a : AffineCoordinateRing F G.X) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F))) x.val a =
      TrivSqZeroExt.inl (identityValue F a) + TrivSqZeroExt.inr
        (Lie.kernelDerivationEquiv G x (LocalModularCharacter.coordinateComparison G a)) := by
  refine (LocalModularCharacter.affinePointEvaluation_eq_pointCoordinates G x.val a).trans ?_
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    have h := congrArg (fun f => f (LocalModularCharacter.coordinateComparison G a))
      (Lie.pointCoordinates_kernel G x)
    have h1 : identityValue F (G := G) a =
        Lie.pointCoordinates G (1 : Lie.AffinePoints G (InfiniteAdeleRing F))
          (LocalModularCharacter.coordinateComparison G a) :=
      LocalModularCharacter.affinePointEvaluation_eq_pointCoordinates G 1 a
    rw [h1, Lie.pointCoordinates_one]
    exact h
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

variable (X Y : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))

/-- The identity derivation of `tangentKernel X` is `D_X` on global regular functions. -/
theorem kernelDerivationEquiv_tangentKernel (a : AffineCoordinateRing F G.X) :
    Lie.kernelDerivationEquiv G (tangentKernel F hsmooth X)
        (LocalModularCharacter.coordinateComparison G a) =
      regularDerivative F hsmooth X a := by
  have h := affinePointEvaluation_lieKernel F (tangentKernel F hsmooth X) a
  have h2 := affinePointEvaluation_tangentPoint_snd F hsmooth X a
  have h3 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h3
  exact h3.symm.trans h2

theorem regularDerivative_add_left (a : AffineCoordinateRing F G.X) :
    regularDerivative F hsmooth (X + Y) a =
      regularDerivative F hsmooth X a + regularDerivative F hsmooth Y a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  funext v
  change mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 (X + Y) =
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 X +
      mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 Y
  exact map_add _ X Y

theorem affinePointEvaluation_tangentKernel_add (a : AffineCoordinateRing F G.X) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentKernel F hsmooth (X + Y)).val a =
      G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentKernel F hsmooth X * tangentKernel F hsmooth Y).val a := by
  refine (affinePointEvaluation_lieKernel F _ a).trans
    (Eq.trans ?_ (affinePointEvaluation_lieKernel F _ a).symm)
  rw [Lie.kernelDerivationEquiv_mul, Derivation.add_apply, kernelDerivationEquiv_tangentKernel,
    kernelDerivationEquiv_tangentKernel, kernelDerivationEquiv_tangentKernel,
    regularDerivative_add_left]

/-- `X ↦ tangentKernel X` turns addition of tangent vectors into the group law of the
kernel. -/
theorem tangentKernel_add :
    tangentKernel F hsmooth (X + Y) = tangentKernel F hsmooth X * tangentKernel F hsmooth Y := by
  apply Subtype.ext
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
  exact funext fun a : AffineCoordinateRing F G.X =>
    affinePointEvaluation_tangentKernel_add F hsmooth X Y a

/-- The diagonal image of a real number in `F_∞`. -/
def realAdele (r : ℝ) : InfiniteAdeleRing F := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact fun v => ((r : ℝ) : v.Completion)

theorem regularDerivative_smul_left (r : ℝ) (a : AffineCoordinateRing F G.X) :
    regularDerivative F hsmooth (r • X) a = realAdele F r * regularDerivative F hsmooth X a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  funext v
  change mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 (r • X) =
    ((r : ℝ) : v.Completion) *
      (show v.Completion from
        mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 X)
  rw [map_smul]
  exact RCLike.real_smul_eq_coe_mul (K := v.Completion) r _

theorem affinePointEvaluation_tangentKernel_smul (r : ℝ) (a : AffineCoordinateRing F G.X) :
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (tangentKernel F hsmooth (r • X)).val a =
      G.affinePointEvaluation (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
        (lieKernelScale G (realAdele F r) (tangentKernel F hsmooth X)).val a := by
  refine (affinePointEvaluation_lieKernel F _ a).trans
    (Eq.trans ?_ (affinePointEvaluation_lieKernel F _ a).symm)
  rw [Lie.kernelDerivationEquiv_scale, Derivation.smul_apply,
    kernelDerivationEquiv_tangentKernel, kernelDerivationEquiv_tangentKernel,
    regularDerivative_smul_left, smul_eq_mul]

/-- Real multiples of tangent vectors correspond to `ε`-scaling by the diagonal real adele. -/
theorem tangentKernel_smul (r : ℝ) :
    tangentKernel F hsmooth (r • X) =
      lieKernelScale G (realAdele F r) (tangentKernel F hsmooth X) := by
  apply Subtype.ext
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
  exact funext fun a : AffineCoordinateRing F G.X =>
    affinePointEvaluation_tangentKernel_smul F hsmooth X r a

end Linear

end Langlands.Global.InfiniteAdelicGroupPoints
