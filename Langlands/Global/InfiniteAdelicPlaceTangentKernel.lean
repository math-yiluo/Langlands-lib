import Langlands.Global.InfiniteAdelicChartFormula
import Langlands.Global.LocalModularCharacter.ChartLie
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.ClosedRepresentationEvaluation
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Lie.AdjointDominance
import Langlands.GroupScheme.Lie.AffineBracketMatrix
import Langlands.GroupScheme.Lie.FieldAlgebraLie
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.Global.InfiniteAdelicLeviEnveloping

/-! # Tangent vectors of the infinite adelic points as dual-number points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.Global.LocalModularCharacter
open Langlands.AlgebraicGeometry.PointTopology

section KernelEvaluation

variable {F : Type u} [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [IsAffineHom G.X.hom] {K : Type u} [CommRing K] [Algebra F K]

local instance tangentKernelCommGroup : CommGroup (lieKernel G K) := lieKernelCommGroup G

local instance tangentKernelModule : Module K (Additive (lieKernel G K)) := lieKernelModule G

attribute [local instance] Lie.coordinateOriginAlgebra

/-- The infinitesimal parts of the values of all global regular functions at an identity-kernel
point. -/
def kernelEvaluation : Additive (lieKernel G K) →ₗ[K] (Γ(G.X.left, ⊤) → K) where
  toFun y a := Lie.kernelDerivationEquiv G y.toMul (coordinateComparison G a)
  map_add' y z := by
    funext a
    change Lie.kernelDerivationEquiv G (y.toMul * z.toMul) _ = _
    rw [Lie.kernelDerivationEquiv_mul]
    rfl
  map_smul' r y := by
    funext a
    change Lie.kernelDerivationEquiv G (lieKernelScale G r y.toMul) _ = _
    rw [Lie.kernelDerivationEquiv_scale]
    rfl

theorem kernelEvaluation_apply (y : Additive (lieKernel G K)) (a : Γ(G.X.left, ⊤)) :
    kernelEvaluation G y a =
      (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a).snd := by
  change Lie.kernelDerivationEquiv G y.toMul (coordinateComparison G a) = _
  rw [affinePointEvaluation_eq_pointCoordinates]
  rfl

/-- An identity-kernel point is determined by the infinitesimal parts of its values. -/
theorem kernelEvaluation_injective : Function.Injective (kernelEvaluation G (K := K)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hfst (a : Γ(G.X.left, ⊤)) :
      (G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a).fst =
        G.affinePointEvaluation (CommAlgCat.of F K) 1 a := by
    rw [← affinePointEvaluation_reduction, y.toMul.property]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber K))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) y.toMul.val a =
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber K)) (1 : Lie.AffinePoints G _) a
  rw [← (Lie.constant G).map_one, affinePointEvaluation_constant]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfst]
    rfl
  · rw [← kernelEvaluation_apply, hy]
    rfl

end KernelEvaluation

section ManifoldJet

variable (F : Type*) [CommSemiring F] {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
  [Algebra F K] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

omit [Algebra F K] in
private theorem smul_add_smul_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : K) (L₁ L₂ : V →L[ℝ] K) (X : V) :
    (a • L₂ + b • L₁) X = a * L₂ X + L₁ X * b := by
  simp [mul_comm]

/-- Functions on a real manifold that are differentiable at a point, as an algebra. -/
def mdiffSubalgebra (x₀ : M) : Subalgebra F (M → K) where
  carrier := {h | MDifferentiableAt I 𝓘(ℝ, K) h x₀}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' _ := mdifferentiableAt_const

/-- The first-order jet at `x₀` in the direction `X`, with values in the dual numbers. -/
def manifoldJet (x₀ : M) (X : TangentSpace I x₀) : mdiffSubalgebra F (K := K) I x₀ →ₐ[F] DualNumber K where
  toFun h := TrivSqZeroExt.inl ((h : M → K) x₀) +
    TrivSqZeroExt.inr (mfderiv I 𝓘(ℝ, K) (h : M → K) x₀ X)
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Pi.one_def, mfderiv_const]
      rfl
  map_mul' h₁ h₂ := by
    have e : ((h₁ * h₂ : mdiffSubalgebra F (K := K) I x₀) : M → K) = (h₁ : M → K) * h₂ := rfl
    have hd := ((h₁.2 : MDifferentiableAt I 𝓘(ℝ, K) (h₁ : M → K) x₀).hasMFDerivAt.mul
      (h₂.2 : MDifferentiableAt I 𝓘(ℝ, K) (h₂ : M → K) x₀).hasMFDerivAt).mfderiv
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [e]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        zero_add, add_zero]
      rw [e, hd]
      exact smul_add_smul_apply (V := E) _ _ _ _ X
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Pi.zero_def, mfderiv_const]
      rfl
  map_add' h₁ h₂ := by
    have e : ((h₁ + h₂ : mdiffSubalgebra F (K := K) I x₀) : M → K) = (h₁ : M → K) + h₂ := rfl
    have hd := mfderiv_add (h₁.2 : MDifferentiableAt I 𝓘(ℝ, K) (h₁ : M → K) x₀)
      (h₂.2 : MDifferentiableAt I 𝓘(ℝ, K) (h₂ : M → K) x₀)
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [e]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rw [e, hd]
      rfl
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [Pi.algebraMap_def, mfderiv_const, TrivSqZeroExt.algebraMap_eq_inl']
      rfl

variable {F I}

@[simp] theorem manifoldJet_fst (x₀ : M) (X : TangentSpace I x₀) (h : mdiffSubalgebra F (K := K) I x₀) :
    (manifoldJet F I x₀ X h).fst = (h : M → K) x₀ := by
  simp [manifoldJet]

@[simp] theorem manifoldJet_snd (x₀ : M) (X : TangentSpace I x₀) (h : mdiffSubalgebra F (K := K) I x₀) :
    (manifoldJet F I x₀ X h).snd = mfderiv I 𝓘(ℝ, K) (h : M → K) x₀ X := by
  simp [manifoldJet]

end ManifoldJet

section Tangent

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] {d : ℕ}

/-- The values of a regular function at the points over a completion are differentiable at the
identity of the infinite adelic group. -/
theorem isRegularFamily_atPlace (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    IsRegularFamily G
      (mdiffSubalgebra F (K := v.Completion) 𝓘(ℝ, smoothModel F d)
        (1 : InfiniteAdelicGroupPoints F G))
      (fun g => atPlace F G v g) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  intro a
  have h := contMDiff_completionEvaluation F G hsmooth v a
  have heq : familyValue G (fun g => atPlace F G v g) a =
      fun x : InfiniteAdelicGroupPoints F G =>
        G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v := by
    funext x
    exact atPlace_evaluation F G x a v
  change MDifferentiableAt _ _ (familyValue G (fun g => atPlace F G v g) a) 1
  rw [heq]
  exact h.mdifferentiableAt (by simp)

/-- The value of a regular function at a point over a completion. -/
def placePointValue (v : InfinitePlace F) (a : Γ(G.X.left, ⊤)) (g : InfiniteAdelicGroupPoints F G) :
    v.Completion :=
  G.affinePointEvaluation (CommAlgCat.of F v.Completion) (atPlace F G v g) a

/-- The dual-number point at a completion of the infinitesimal motion of the identity of
`G(F ⊗ ℝ)` in the direction of a tangent vector. -/
def tangentKernelPoint (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F)
    (X : smoothModel F d) : lieKernel G v.Completion := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact ⟨Lie.affineMap G (manifoldJet F 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G) X)
      (liftFamily G _ (fun g => atPlace F G v g) (isRegularFamily_atPlace F G hsmooth v)), by
    apply G.affinePointEvaluation_injective (CommAlgCat.of F v.Completion)
    funext a
    change G.affinePointEvaluation (CommAlgCat.of F v.Completion) (Lie.reduction G _) a =
      G.affinePointEvaluation (CommAlgCat.of F v.Completion) 1 a
    rw [affinePointEvaluation_reduction, affinePointEvaluation_affineMap,
      affinePointEvaluation_liftFamily, manifoldJet_fst]
    change G.affinePointEvaluation (CommAlgCat.of F v.Completion) (atPlace F G v 1) a = _
    rw [map_one]⟩

theorem affinePointEvaluation_tangentKernelPoint
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F) (X : smoothModel F d)
    (a : Γ(G.X.left, ⊤)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    G.affinePointEvaluation (CommAlgCat.of F (DualNumber v.Completion))
        (tangentKernelPoint F G hsmooth v X).val a =
      TrivSqZeroExt.inl (placePointValue F G v a 1) +
        TrivSqZeroExt.inr (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion)
          (placePointValue F G v a) 1 X) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  change G.affinePointEvaluation (CommAlgCat.of F (DualNumber v.Completion))
    (Lie.affineMap G _ _) a = _
  rw [affinePointEvaluation_affineMap, affinePointEvaluation_liftFamily]
  rfl

variable [IsAffineHom G.X.hom]

theorem kernelEvaluation_tangentKernelPoint (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) (X : smoothModel F d) (a : Γ(G.X.left, ⊤)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    kernelEvaluation G (Additive.ofMul (tangentKernelPoint F G hsmooth v X)) a =
      mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placePointValue F G v a) 1 X := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  rw [kernelEvaluation_apply]
  change (G.affinePointEvaluation (CommAlgCat.of F (DualNumber v.Completion))
    (tangentKernelPoint F G hsmooth v X).val a).snd = _
  rw [affinePointEvaluation_tangentKernelPoint]
  simp

omit [IsAffineHom G.X.hom] in
/-- The value of a regular function at a completion is differentiable at the identity. -/
theorem mdifferentiableAt_placeValue (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) (a : Γ(G.X.left, ⊤)) (x : InfiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    MDifferentiableAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placePointValue F G v a) x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have h := contMDiff_completionEvaluation F G hsmooth v a
  have heq : placePointValue F G v a = fun x : InfiniteAdelicGroupPoints F G =>
      G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v := by
    funext x
    exact atPlace_evaluation F G x a v
  rw [heq]
  exact h.mdifferentiableAt (by simp)

/-- The tangent map at a completion, as a real-linear map into the dual-number Lie kernel. -/
def tangentKernelMap (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    smoothModel F d →ₗ[ℝ] RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion)) :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  { toFun := fun X => Additive.ofMul (tangentKernelPoint F G hsmooth v X)
    map_add' := fun X Y => by
      let := smoothChartedSpace F G hsmooth
      apply kernelEvaluation_injective G (K := v.Completion)
      funext a
      change kernelEvaluation G (Additive.ofMul (tangentKernelPoint F G hsmooth v (X + Y))) a =
        kernelEvaluation G (Additive.ofMul (tangentKernelPoint F G hsmooth v X) +
          Additive.ofMul (tangentKernelPoint F G hsmooth v Y)) a
      rw [map_add, Pi.add_apply, kernelEvaluation_tangentKernelPoint,
        kernelEvaluation_tangentKernelPoint, kernelEvaluation_tangentKernelPoint, map_add]
    map_smul' := fun r X => by
      let := smoothChartedSpace F G hsmooth
      apply kernelEvaluation_injective G (K := v.Completion)
      funext a
      change kernelEvaluation G (Additive.ofMul (tangentKernelPoint F G hsmooth v (r • X))) a =
        kernelEvaluation G (algebraMap ℝ v.Completion r •
          Additive.ofMul (tangentKernelPoint F G hsmooth v X)) a
      rw [map_smul, Pi.smul_apply, kernelEvaluation_tangentKernelPoint,
        kernelEvaluation_tangentKernelPoint, map_smul]
      exact (algebraMap_smul v.Completion r _).symm }

theorem kernelEvaluation_tangentKernelMap (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) (X : smoothModel F d) (a : Γ(G.X.left, ⊤)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    kernelEvaluation G (tangentKernelMap F G hsmooth v X : Additive (lieKernel G v.Completion)) a =
      mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placePointValue F G v a) 1 X :=
  kernelEvaluation_tangentKernelPoint F G hsmooth v X a

end Tangent

section Realization

open Langlands.GroupScheme.GeneralLinear

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n]

omit [IsAffine G.X.left] in
/-- Evaluating the pullback of a polynomial in the coordinates of `GL_n` at a point is evaluating
the polynomial at the matrix of the point. -/
theorem affinePointEvaluation_pullback_quotient (ρ : MatrixRepresentation G n)
    (P : MvPolynomial (Coordinate n) k) (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : G.affinePoints S) :
    G.affinePointEvaluation S x (ρ.hom.hom.left.appTop
        ((spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm (quotient n k P))) =
      MvPolynomial.aeval (values (ρ.affineMatrix S x)) P := by
  let c : Γ((GeneralLinear.groupScheme n (CommRingCat.of k)).X.left, ⊤) :=
    (spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm (quotient n k P)
  change G.affinePointEvaluation S x (ρ.hom.hom.left.appTop c) = _
  rw [← affinePointEvaluation_postcomp]
  have hy : x ≫ ρ.hom.hom = (affinePointsEquiv n (CommRingCat.of k) S).symm
      (ρ.affineMatrix S x) := by
    rw [MatrixRepresentation.affineMatrix_apply, MulEquiv.symm_apply_apply]
  rw [hy, affinePointsEquiv_symm_apply, affinePointEvaluation_map_classify]
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n (CommRingCat.of k)))).hom c =
      quotient n k P :=
    (spectrumCoordinateAlgEquiv k (CoordinateRing n k)).apply_symm_apply _
  rw [hc, classify_quotient]

omit [IsAffine G.X.left] in
/-- Every matrix coefficient of a representation is the value of a global regular function. -/
theorem exists_affineMatrix_entry_eq (ρ : MatrixRepresentation G n) (i j : n) :
    ∃ m : Γ(G.X.left, ⊤), ∀ (S : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints S),
      (ρ.affineMatrix S x : Matrix n n S) i j = G.affinePointEvaluation S x m := by
  refine ⟨ρ.hom.hom.left.appTop ((spectrumCoordinateAlgEquiv k (CoordinateRing n k)).symm
    (quotient n k (MvPolynomial.X (Coordinate.entry i j)))), fun S x => ?_⟩
  rw [affinePointEvaluation_pullback_quotient, MvPolynomial.aeval_X]
  rfl

end Realization

section Injectivity

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] {d : ℕ}

omit [NumberField F] in
omit [IsAffine G.X.left] in
/-- The matrices of the base change of a representation to a completion are the original
matrices of the points over the completion. -/
theorem realizationMatrix_baseChange {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (v : InfinitePlace F) (y : InfinitePlaceGroupPoints F G v) :
    ((InfinitePlaceGroupPoints.realizationMatrix F G v
        (ρ.baseChange (algebraBaseMap F v.Completion)) y : GL (Fin N) v.Completion) :
        Matrix (Fin N) (Fin N) v.Completion) =
      ρ.affineMatrix (CommAlgCat.of F v.Completion) y := by
  change (((ρ.baseChange (algebraBaseMap F v.Completion)).affineMatrix
      (CommAlgCat.of (CommRingCat.of v.Completion) v.Completion)
      (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G y) :
        GL (Fin N) v.Completion) : Matrix (Fin N) (Fin N) v.Completion) = _
  rw [MatrixRepresentation.affineMatrix_baseChange]
  congr 2
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left]
  exact affinePointsBaseChangeMulEquiv_symm_left F v.Completion v.Completion G
    (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G y) |>.symm.trans
    (by rw [MulEquiv.symm_apply_apply])

omit [NumberField F] [IsAffine G.X.left] in
/-- Base change of a closed matrix representation is closed. -/
theorem isClosedSubgroup_baseChange {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) (v : InfinitePlace F) :
    IsClosedSubgroup (ρ.baseChange (algebraBaseMap F v.Completion)) := by
  have h₁ : IsClosedImmersion
      ((GroupScheme.baseChange (algebraBaseMap F v.Completion)).map ρ).hom.hom.left :=
    hρ.baseChange (algebraBaseMap F v.Completion)
  have : IsIso (GeneralLinear.baseChangeIso (Fin N)
      (algebraBaseMap F v.Completion)).hom.hom.hom :=
    (Grp.forget (Over _)).map_isIso (GeneralLinear.baseChangeIso (Fin N)
      (algebraBaseMap F v.Completion)).hom
  have : IsIso (GeneralLinear.baseChangeIso (Fin N)
      (algebraBaseMap F v.Completion)).hom.hom.hom.left :=
    (Over.forget _).map_isIso (GeneralLinear.baseChangeIso (Fin N)
      (algebraBaseMap F v.Completion)).hom.hom.hom
  change IsClosedImmersion
    (((GroupScheme.baseChange (algebraBaseMap F v.Completion)).map ρ).hom.hom.left ≫
      (GeneralLinear.baseChangeIso (Fin N) (algebraBaseMap F v.Completion)).hom.hom.hom.left)
  infer_instance

variable [IsAffineHom G.X.hom]

/-- **Injectivity.** A tangent vector at the identity of `G(F ⊗ ℝ)` whose dual-number points
at all completions are trivial is zero. -/
theorem eq_zero_of_tangentKernelMap_eq_zero [LocallyOfFiniteType G.X.hom]
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (hX : ∀ v, tangentKernelMap F G hsmooth v X = 0) : X = 0 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  have hder (v : InfinitePlace F) (a : Γ(G.X.left, ⊤)) :
      mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placePointValue F G v a) 1 X = 0 := by
    rw [← kernelEvaluation_tangentKernelMap F G hsmooth v X a, hX v]
    exact congrFun (map_zero (kernelEvaluation G (K := v.Completion))) a
  refine eq_zero_of_zeroDeriv_realization F G hsmooth (N := fun _ => N)
    (fun v => ρ.baseChange (algebraBaseMap F v.Completion))
    (fun v => isClosedSubgroup_baseChange F G ρ hρ v) X ?_
  intro v i j
  obtain ⟨m, hm⟩ := exists_affineMatrix_entry_eq ρ i j
  have heq : (fun g => (InfinitePlaceGroupPoints.realizationMatrix F G v
      (ρ.baseChange (algebraBaseMap F v.Completion)) (atPlace F G v g)).val i j) =
      placePointValue F G v m := by
    funext g
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) v.Completion => M i j)
      (realizationMatrix_baseChange F G ρ v (atPlace F G v g))
    exact h.trans (hm _ _)
  rw [heq]
  exact ⟨_, (mdifferentiableAt_placeValue F G hsmooth v m 1).hasMFDerivAt, hder v m⟩

end Injectivity

section Bracket

open scoped Langlands.GroupScheme.Lie.FieldLie

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [IsAffineHom G.X.hom] {d : ℕ}

/-- A global regular function giving a matrix coefficient of a representation. -/
def entryFunction {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (a b : Fin N) : Γ(G.X.left, ⊤) :=
  (exists_affineMatrix_entry_eq ρ a b).choose

omit [NumberField F] [IsAffine G.X.left] [IsAffineHom G.X.hom] in
theorem affineMatrix_entry {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (a b : Fin N)
    (S : CommAlgCat.{u} (CommRingCat.of F)) (x : G.affinePoints S) :
    (ρ.affineMatrix S x : Matrix (Fin N) (Fin N) S) a b =
      G.affinePointEvaluation S x (entryFunction F G ρ a b) :=
  (exists_affineMatrix_entry_eq ρ a b).choose_spec S x

/-- The matrices of a representation at the points over a completion, as a function on the
infinite adelic points. -/
def placeMatrix {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (v : InfinitePlace F) :
    InfiniteAdelicGroupPoints F G →* Matrix (Fin N) (Fin N) v.Completion :=
  (Units.coeHom _).comp ((ρ.affineMatrix (CommAlgCat.of F v.Completion)).comp
    (atPlace F G v).toMonoidHom)

omit [NumberField F] [IsAffineHom G.X.hom] in
theorem placeMatrix_apply {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (v : InfinitePlace F)
    (g : InfiniteAdelicGroupPoints F G) (a b : Fin N) :
    placeMatrix F G ρ v g a b = placePointValue F G v (entryFunction F G ρ a b) g :=
  affineMatrix_entry F G ρ a b _ (atPlace F G v g)

omit [IsAffineHom G.X.hom] in
theorem contMDiff_placePointValue (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) (a : Γ(G.X.left, ⊤)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞ (placePointValue F G v a) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have h := contMDiff_completionEvaluation F G hsmooth v a
  have heq : placePointValue F G v a = fun x : InfiniteAdelicGroupPoints F G =>
      G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v := by
    funext x
    exact atPlace_evaluation F G x a v
  rw [heq]
  exact h

/-- The tangent matrix of a dual-number point at a completion is the matrix differential of the
corresponding representation of the infinite adelic group. -/
theorem kernelDifferential_tangentKernelMap {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F) (X : smoothModel F d) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ρ.kernelDifferential v.Completion
        (tangentKernelMap F G hsmooth v X : Additive (lieKernel G v.Completion)) =
      Langlands.Geometry.Manifold.MatrixCoefficientLie.matrixDifferential
        𝓘(ℝ, smoothModel F d) (placeMatrix F G ρ v) X := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  refine Matrix.ext fun a b => ?_
  rw [Langlands.Geometry.Manifold.MatrixCoefficientLie.matrixDifferential_apply]
  have hfun : (fun g => placeMatrix F G ρ v g a b) =
      placePointValue F G v (entryFunction F G ρ a b) := funext fun g => placeMatrix_apply F G ρ v g a b
  rw [hfun]
  have hk := kernelEvaluation_tangentKernelMap F G hsmooth v X (entryFunction F G ρ a b)
  rw [kernelEvaluation_apply] at hk
  rw [MatrixRepresentation.kernelDifferential_apply]
  change ((ρ.affineMatrix (CommAlgCat.of F (DualNumber v.Completion))
    (tangentKernelPoint F G hsmooth v X).val :
      Matrix (Fin N) (Fin N) (DualNumber v.Completion)) a b).snd = _
  rw [affineMatrix_entry]
  exact hk

set_option maxHeartbeats 1000000 in
/-- **Brackets.** The dual-number point at a completion of the Lie bracket of two tangent vectors
of `G(F ⊗ ℝ)` is the bracket of their dual-number points. -/
theorem tangentKernelMap_lie [LocallyOfFiniteType G.X.hom]
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G),
      RestrictScalars.addEquiv ℝ v.Completion _ (tangentKernelMap F G hsmooth v
          (⁅X, Y⁆ : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) =
        ⁅RestrictScalars.addEquiv ℝ v.Completion _ (tangentKernelMap F G hsmooth v X),
          RestrictScalars.addEquiv ℝ v.Completion _ (tangentKernelMap F G hsmooth v Y)⁆ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : LieGroup 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothLieGroup F G hsmooth
  intro X Y
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  have hent : ∀ a b, ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
      (fun g => placeMatrix F G ρ v g a b) := by
    intro a b
    have hfun : (fun g => placeMatrix F G ρ v g a b) =
        placePointValue F G v (entryFunction F G ρ a b) :=
      funext fun g => placeMatrix_apply F G ρ v g a b
    rw [hfun]
    exact contMDiff_placePointValue F G hsmooth v _
  have hX := kernelDifferential_tangentKernelMap F G ρ hsmooth v X
  have hY := kernelDifferential_tangentKernelMap F G ρ hsmooth v Y
  have hXY := kernelDifferential_tangentKernelMap F G ρ hsmooth v
    (⁅X, Y⁆ : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
  have hlie := Langlands.Geometry.Manifold.MatrixCoefficientLie.matrixDifferential_lie
    (placeMatrix F G ρ v) hent X Y
  apply Lie.kernelDifferential_injective (A := v.Completion) ρ (IsClosedSubgroup.mono_overHom hρ)
  rw [MatrixRepresentation.kernelDifferential_commutator]
  refine hXY.trans (hlie.trans ?_)
  rw [← hX, ← hY]
  rfl

end Bracket

section Naturality

variable (F : Type u) [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left] {d e : ℕ}

omit [NumberField F] in
theorem placeValue_affinePointsTarget (f : H ⟶ G) (v : InfinitePlace F) (a : Γ(G.X.left, ⊤))
    (x : InfiniteAdelicGroupPoints F H) :
    placePointValue F G v a (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)) x) =
      placePointValue F H v (f.hom.hom.left.appTop a) x := by
  unfold placePointValue
  rw [atPlace_evaluation, atPlace_evaluation, affinePointsTarget_apply,
    affinePointEvaluation_postcomp]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- **Naturality.** The derivative of the map of infinite adelic points induced by a
homomorphism corresponds to the tangent map of the homomorphism on dual-number points. -/
theorem tangentKernelMap_naturality (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom) (f : H ⟶ G) (v : InfinitePlace F)
    (X : smoothModel F e) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothChartedSpace F H hH
    (tangentKernelMap F G hG v (mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
        (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F))) 1 X) :
        Additive (lieKernel G v.Completion)) =
      Lie.targetMapLinear f v.Completion
        (tangentKernelMap F H hH v X : Additive (lieKernel H v.Completion)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothChartedSpace F H hH
  apply kernelEvaluation_injective G (K := v.Completion)
  funext a
  have hR : kernelEvaluation G (Lie.targetMapLinear f v.Completion
      (tangentKernelMap F H hH v X : Additive (lieKernel H v.Completion))) a =
      mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, v.Completion)
        (placePointValue F H v (f.hom.hom.left.appTop a)) 1 X := by
    rw [kernelEvaluation_apply]
    change (G.affinePointEvaluation (CommAlgCat.of F (DualNumber v.Completion))
      ((tangentKernelPoint F H hH v X).val ≫ f.hom.hom) a).snd = _
    rw [affinePointEvaluation_postcomp]
    exact (kernelEvaluation_apply H
      (tangentKernelMap F H hH v X : Additive (lieKernel H v.Completion)) _).symm.trans
      (kernelEvaluation_tangentKernelMap F H hH v X _)
  have hL := kernelEvaluation_tangentKernelMap F G hG v (mfderiv 𝓘(ℝ, smoothModel F e)
    𝓘(ℝ, smoothModel F d) (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F))) 1 X) a
  have hcomp : placePointValue F H v (f.hom.hom.left.appTop a) =
      placePointValue F G v a ∘ H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F)) :=
    funext fun x => (placeValue_affinePointsTarget F f v a x).symm
  have hC : mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, v.Completion)
      (placePointValue F H v (f.hom.hom.left.appTop a)) 1 X =
      mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placePointValue F G v a) 1
        (mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
          (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F))) 1 X) := by
    rw [hcomp]
    exact mfderiv_comp_apply_of_eq (1 : InfiniteAdelicGroupPoints F H)
      (mdifferentiableAt_placeValue F G hG v a 1)
      ((contMDiff_affinePointsTarget F hH hG f).mdifferentiableAt (by simp)) (map_one _) X
  exact hL.trans (hC.symm.trans hR.symm)

end Naturality

end Langlands.Global.InfiniteAdelicGroupPoints
