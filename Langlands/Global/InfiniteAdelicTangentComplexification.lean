import Langlands.Global.InfiniteAdelicPlaceTangentKernel
import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # The complexified tangent Lie algebra of the infinite adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme

section Dimension

variable (F : Type u) [Field F]

/-- The real dimension of an archimedean completion is the multiplicity of its place. -/
theorem finrank_completion (v : InfinitePlace F) :
    letI := InfinitePlaceGroupPoints.completionRCLike F v
    Module.finrank ℝ v.Completion = v.mult := by
  let := InfinitePlaceGroupPoints.completionRCLike F v
  rcases v.isReal_or_isComplex with hv | hv
  · let e : v.Completion ≃L[ℝ] ℝ :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toAddEquiv.toRealLinearEquiv
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self, InfinitePlace.mult]
    simp [hv]
  · let e : v.Completion ≃L[ℝ] ℂ :=
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toAddEquiv.toRealLinearEquiv
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
    rw [e.toLinearEquiv.finrank_eq, Complex.finrank_real_complex, InfinitePlace.mult]
    simp [InfinitePlace.not_isReal_iff_isComplex.mpr hv]

variable [NumberField F]

/-- The real dimensions of the archimedean completions add up to the degree. -/
theorem sum_finrank_completion :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∑ v : InfinitePlace F, Module.finrank ℝ v.Completion = Module.finrank ℚ F := by
  simp_rw [finrank_completion]
  exact InfinitePlace.sum_mult_eq

/-- The real dimension of the model space of the infinite adelic manifold. -/
theorem finrank_smoothModel (d : ℕ) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Module.finrank ℝ (smoothModel F d) = d * Module.finrank ℚ F := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  rw [Module.finrank_pi_fintype]
  simp_rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [← Finset.mul_sum, sum_finrank_completion]

/-- The diagonal embedding of the number field into the product of its archimedean
completions. -/
def diagonalMap (f : F) : (v : InfinitePlace F) → v.Completion := fun v => algebraMap F v.Completion f

/-- The diagonal image of the number field spans the product of its archimedean completions
over the reals: it is dense, and finite-dimensional subspaces are closed. -/
theorem span_range_diagonalMap :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Submodule.span ℝ (Set.range (diagonalMap F)) = ⊤ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  set S := Submodule.span ℝ (Set.range (diagonalMap F))
  have hclosed : IsClosed (S : Set ((v : InfinitePlace F) → v.Completion)) :=
    S.closed_of_finiteDimensional
  have hdense : DenseRange (diagonalMap F) :=
    InfiniteAdeleRing.denseRange_algebraMap F
  rw [eq_top_iff]
  intro a _
  have ha : a ∈ closure (Set.range (diagonalMap F)) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal Submodule.subset_span hclosed ha

end Dimension

section Kernel

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ}

omit [NumberField F] [IsAffine G.X.left] in
/-- The dual-number Lie kernel over any field extension has the relative dimension. -/
theorem finrank_lieKernel_of_smooth (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (K : Type u) [Field K] [Algebra F K] :
    Module.finrank K (Additive (lieKernel G K)) = d := by
  rw [← (Lie.kernelScalarExtension G K).finrank_eq, Module.finrank_baseChange]
  exact Lie.dimension_eq_of_smoothOfRelativeDimension G hsmooth

/-- The product over the archimedean places of the dual-number Lie kernels at the completions,
as a real vector space. -/
abbrev PlaceKernels :=
  (v : InfinitePlace F) → RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion))

/-- The dual-number Lie kernel at a completion is a coordinate space of the relative
dimension. -/
def placeKernelCoordinates (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion)) ≃ₗ[ℝ]
      (Fin d → v.Completion) := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := RestrictScalars.moduleOrig ℝ v.Completion (Additive (lieKernel G v.Completion))
  have : FiniteDimensional v.Completion
      (RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion))) :=
    (Lie.kernelScalarExtension G v.Completion).finiteDimensional
  have hfin : Module.finrank v.Completion
      (RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion))) =
        Module.finrank v.Completion (Fin d → v.Completion) := by
    rw [Module.finrank_fin_fun]
    exact finrank_lieKernel_of_smooth F G hsmooth v.Completion
  exact (LinearEquiv.ofFinrankEq _ _ hfin).restrictScalars ℝ

/-- The product of the dual-number Lie kernels is the model space of the manifold. -/
def placeKernelsEquiv (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    PlaceKernels F G ≃ₗ[ℝ] smoothModel F d :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  LinearEquiv.piCongrRight fun v => placeKernelCoordinates F G hsmooth v

/-- The joint tangent map to the dual-number Lie kernels at all completions. -/
def tangentKernelPi (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    smoothModel F d →ₗ[ℝ] PlaceKernels F G :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  LinearMap.pi fun v => tangentKernelMap F G hsmooth v

theorem tangentKernelPi_injective (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Function.Injective (tangentKernelPi F G hsmooth) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  exact eq_zero_of_tangentKernelMap_eq_zero F G hsmooth X fun v => congrFun hX v

/-- **The tangent space at the identity of `G(F ⊗ ℝ)` is the product of the dual-number Lie
kernels at the completions.** -/
def tangentKernelEquiv (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    smoothModel F d ≃ₗ[ℝ] PlaceKernels F G := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  have hV : FiniteDimensional ℝ (smoothModel F d) := inferInstance
  have hinj := tangentKernelPi_injective F G hsmooth
  let e := placeKernelsEquiv F G hsmooth
  have h1 : Function.Injective (e.toLinearMap ∘ₗ tangentKernelPi F G hsmooth) :=
    e.injective.comp hinj
  have h2 := LinearMap.injective_iff_surjective.mp h1
  have hsurj : Function.Surjective (tangentKernelPi F G hsmooth) := by
    intro w
    obtain ⟨X, hX⟩ := h2 (e w)
    exact ⟨X, e.injective hX⟩
  exact LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩

theorem tangentKernelEquiv_apply (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (X : smoothModel F d) (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    tangentKernelEquiv F G hsmooth X v = tangentKernelMap F G hsmooth v X := rfl

end Kernel

section Realization

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ}

/-- The images of a tangent vector over `F` in the dual-number Lie kernels at all completions. -/
def placeKernelVector (x : Additive (lieKernel G F)) : PlaceKernels F G := fun v =>
  (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).symm
    (lieKernelMapLinear G (Algebra.ofId F v.Completion) x)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem placeKernelVector_add (x y : Additive (lieKernel G F)) :
    placeKernelVector F G (x + y) = placeKernelVector F G x + placeKernelVector F G y := by
  funext v
  exact congrArg _ (map_add (lieKernelMapLinear G (Algebra.ofId F v.Completion)) x y)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem placeKernelVector_smul (c : F) (x : Additive (lieKernel G F)) (v : InfinitePlace F) :
    placeKernelVector F G (c • x) v =
      (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).symm
        (algebraMap F v.Completion c • lieKernelMapLinear G (Algebra.ofId F v.Completion) x) :=
  congrArg _ ((lieKernelMapLinear G (Algebra.ofId F v.Completion)).map_smulₛₗ c x)

/-- The real tangent vector at the identity of `G(F ⊗ ℝ)` realizing a tangent vector of `G`
over `F` at all completions. -/
def tangentVector (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x : Additive (lieKernel G F)) : smoothModel F d :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  (tangentKernelEquiv F G hsmooth).symm (placeKernelVector F G x)

theorem tangentKernelMap_tangentVector (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x : Additive (lieKernel G F)) (v : InfinitePlace F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    tangentKernelMap F G hsmooth v (tangentVector F G hsmooth x) = placeKernelVector F G x v := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  rw [← tangentKernelEquiv_apply, tangentVector, LinearEquiv.apply_symm_apply]

theorem tangentVector_add (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x y : Additive (lieKernel G F)) :
    tangentVector F G hsmooth (x + y) = tangentVector F G hsmooth x + tangentVector F G hsmooth y := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact (congrArg (tangentKernelEquiv F G hsmooth).symm (placeKernelVector_add F G x y)).trans
    ((tangentKernelEquiv F G hsmooth).symm.map_add _ _)

theorem tangentVector_ratCast_smul (hsmooth : SmoothOfRelativeDimension d G.X.hom) (q : ℚ)
    (x : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    tangentVector F G hsmooth ((q : F) • x) = (q : ℝ) • tangentVector F G hsmooth x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  have h : placeKernelVector F G ((q : F) • x) = (q : ℝ) • placeKernelVector F G x := by
    funext v
    rw [placeKernelVector_smul]
    have hq : algebraMap F v.Completion (q : F) = algebraMap ℝ v.Completion (q : ℝ) := by
      rw [map_ratCast, map_ratCast]
    rw [hq, RestrictScalars.addEquiv_symm_map_algebraMap_smul]
    rfl
  exact (congrArg (tangentKernelEquiv F G hsmooth).symm h).trans
    ((tangentKernelEquiv F G hsmooth).symm.map_smul _ _)

section Span

set_option backward.isDefEq.respectTransparency true

/-- The images of a tangent vector over `F` in the dual-number Lie kernels at the completions,
scaled by an element of the product of the completions. -/
def scaledKernelVector (a : (v : InfinitePlace F) → v.Completion)
    (x : Additive (lieKernel G F)) : PlaceKernels F G := fun v =>
  (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).symm
    (a v • lieKernelMapLinear G (Algebra.ofId F v.Completion) x)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem scaledKernelVector_diagonalMap (f : F) (x : Additive (lieKernel G F)) :
    scaledKernelVector F G (diagonalMap F f) x = placeKernelVector F G (f • x) := by
  funext v
  exact (placeKernelVector_smul F G f x v).symm

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem scaledKernelVector_add (a b : (v : InfinitePlace F) → v.Completion)
    (x : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    scaledKernelVector F G (a + b) x = scaledKernelVector F G a x + scaledKernelVector F G b x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  funext v
  exact (congrArg (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).symm
    (add_smul (a v) (b v) _)).trans (map_add _ _ _)

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem scaledKernelVector_smul (r : ℝ) (a : (v : InfinitePlace F) → v.Completion)
    (x : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    scaledKernelVector F G (r • a) x = r • scaledKernelVector F G a x := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  funext v
  exact (congrArg (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).symm
    ((congrArg (· • lieKernelMapLinear G (Algebra.ofId F v.Completion) x)
      (Algebra.smul_def r (a v))).trans (mul_smul _ _ _))).trans
    (RestrictScalars.addEquiv_symm_map_algebraMap_smul (R := ℝ) (S := v.Completion)
      (M := Additive (lieKernel G v.Completion)) r _)

/-- Scaling the images of a fixed tangent vector over `F`, as a real-linear map on the product
of the completions. -/
def scaledKernelMap (x : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ((v : InfinitePlace F) → v.Completion) →ₗ[ℝ] PlaceKernels F G :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  { toFun := fun a => scaledKernelVector F G a x
    map_add' := fun a b => scaledKernelVector_add F G a b x
    map_smul' := fun r a => scaledKernelVector_smul F G r a x }

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Scalar multiples of the images of a tangent vector over `F`, with arbitrary coefficients at
the completions, lie in the real span of the images of tangent vectors over `F`. -/
theorem scaledKernelVector_mem_span (a : (v : InfinitePlace F) → v.Completion)
    (x : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    scaledKernelVector F G a x ∈ Submodule.span ℝ (Set.range (placeKernelVector F G)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  have ha : a ∈ Submodule.span ℝ (Set.range (diagonalMap F)) := by
    rw [span_range_diagonalMap]
    exact Submodule.mem_top
  have hle : Submodule.span ℝ (Set.range (diagonalMap F)) ≤
      (Submodule.span ℝ (Set.range (placeKernelVector F G))).comap (scaledKernelMap F G x) := by
    rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    change scaledKernelVector F G (diagonalMap F f) x ∈
      Submodule.span ℝ (Set.range (placeKernelVector F G))
    rw [scaledKernelVector_diagonalMap]
    exact Submodule.subset_span ⟨f • x, rfl⟩
  exact hle ha

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem scaledKernelVector_apply_of_eq_zero (a : (v : InfinitePlace F) → v.Completion)
    (x : Additive (lieKernel G F)) (w : InfinitePlace F) (h : a w = 0) :
    scaledKernelVector F G a x w = 0 := by
  change (RestrictScalars.addEquiv ℝ w.Completion (Additive (lieKernel G w.Completion))).symm
    (a w • lieKernelMapLinear G (Algebra.ofId F w.Completion) x) = (0 : PlaceKernels F G) w
  rw [h, zero_smul, map_zero]
  rfl

omit [NumberField F] [IsAffine G.X.left] in
theorem single_eq_scaledKernelVector [DecidableEq (InfinitePlace F)] (v : InfinitePlace F)
    (c : v.Completion) (x : Additive (lieKernel G F)) :
    (Pi.single v ((RestrictScalars.addEquiv ℝ v.Completion _).symm
        (Lie.kernelScalarExtension G v.Completion (c ⊗ₜ x))) : PlaceKernels F G) =
      scaledKernelVector F G (Pi.single v c) x := by
  funext w
  by_cases hw : w = v
  · subst hw
    rw [Pi.single_eq_same, Lie.kernelScalarExtension_tmul]
    change _ = (RestrictScalars.addEquiv ℝ w.Completion (Additive (lieKernel G w.Completion))).symm
      ((Pi.single w c : (v : InfinitePlace F) → v.Completion) w •
        lieKernelMapLinear G (Algebra.ofId F w.Completion) x)
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw]
    exact (scaledKernelVector_apply_of_eq_zero F G _ x w (Pi.single_eq_of_ne hw c)).symm

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem single_add_mem_span [DecidableEq (InfinitePlace F)] (v : InfinitePlace F)
    (A B : RestrictScalars ℝ v.Completion (Additive (lieKernel G v.Completion)))
    (hA : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v;
      (Pi.single v A : PlaceKernels F G) ∈ Submodule.span ℝ (Set.range (placeKernelVector F G)))
    (hB : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v;
      (Pi.single v B : PlaceKernels F G) ∈ Submodule.span ℝ (Set.range (placeKernelVector F G))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v;
    (Pi.single v (A + B) : PlaceKernels F G) ∈
      Submodule.span ℝ (Set.range (placeKernelVector F G)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  rw [Pi.single_add]
  exact Submodule.add_mem _ hA hB

omit [IsAffine G.X.left] in
/-- The dual-number Lie kernel at a single completion lies in the real span of the images of
tangent vectors over `F`. -/
theorem single_mem_span_placeKernelVector [DecidableEq (InfinitePlace F)] (v : InfinitePlace F)
    (y : Additive (lieKernel G v.Completion)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    (Pi.single v ((RestrictScalars.addEquiv ℝ v.Completion _).symm y) : PlaceKernels F G) ∈
      Submodule.span ℝ (Set.range (placeKernelVector F G)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  obtain ⟨t, rfl⟩ := (Lie.kernelScalarExtension G v.Completion).surjective y
  induction t with
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact single_add_mem_span F G v _ _ h₁ h₂
  | tmul c x =>
    rw [single_eq_scaledKernelVector]
    exact scaledKernelVector_mem_span F G _ x

omit [IsAffine G.X.left] in
/-- The images of tangent vectors over `F` span the product of the dual-number Lie kernels at the
completions over the reals. -/
theorem span_range_placeKernelVector :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Submodule.span ℝ (Set.range (placeKernelVector F G)) = ⊤ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  classical
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun v _ => ?_
  have h := single_mem_span_placeKernelVector F G v
    (RestrictScalars.addEquiv ℝ v.Completion _ (w v))
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- The realizations of tangent vectors over `F` span the real tangent space at the identity. -/
theorem span_range_tangentVector (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Submodule.span ℝ (Set.range (tangentVector F G hsmooth)) = ⊤ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  have h := Submodule.map_span (tangentKernelEquiv F G hsmooth).symm.toLinearMap
    (Set.range (placeKernelVector F G))
  rw [span_range_placeKernelVector, Submodule.map_top, LinearEquiv.range,
    ← Set.range_comp] at h
  exact h.symm

end Span

section Bracket

open scoped Langlands.GroupScheme.Lie.FieldLie

set_option maxHeartbeats 1000000 in
/-- The realization of tangent vectors over `F` preserves brackets. -/
theorem tangentVector_lie (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x y : Additive (lieKernel G F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
        tangentVector F G hsmooth ⁅x, y⁆) =
      ⁅(show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
          tangentVector F G hsmooth x),
        (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
          tangentVector F G hsmooth y)⁆ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : LieGroup 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothLieGroup F G hsmooth
  apply (tangentKernelEquiv F G hsmooth).injective
  funext v
  rw [tangentKernelEquiv_apply, tangentKernelEquiv_apply, tangentKernelMap_tangentVector]
  apply (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).injective
  have h := tangentKernelMap_lie F G hsmooth v (tangentVector F G hsmooth x)
    (tangentVector F G hsmooth y)
  have hx := congrArg (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion)))
    (tangentKernelMap_tangentVector F G hsmooth x v)
  have hy := congrArg (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion)))
    (tangentKernelMap_tangentVector F G hsmooth y v)
  unfold placeKernelVector at hx hy ⊢
  simp only [AddEquiv.apply_symm_apply] at hx hy ⊢
  refine Eq.trans ?_ h.symm
  rw [hx, hy]
  exact @Lie.lieKernelMapLinear_lie (CommRingCat.of F) G _ F _ _ v.Completion _ _
    (Algebra.ofId F v.Completion) x y

end Bracket

section Naturality

variable {G} {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] {e : ℕ}

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
/-- Coefficient change commutes with the tangent map of a homomorphism. -/
theorem targetMapLinear_placeKernelVector (f : H ⟶ G) (x : Additive (lieKernel H F))
    (v : InfinitePlace F) :
    Lie.targetMapLinear f v.Completion (lieKernelMapLinear H (Algebra.ofId F v.Completion) x) =
      lieKernelMapLinear G (Algebra.ofId F v.Completion) (Lie.targetMapLinear f F x) :=
  congrArg Additive.ofMul (lieKernelTarget_map f (Algebra.ofId F v.Completion) x.toMul)

/-- **Naturality of the realization.** The derivative of the map of infinite adelic points
induced by a homomorphism sends the realization of a tangent vector to the realization of its
image. -/
theorem tangentVector_naturality (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom) (f : H ⟶ G) (x : Additive (lieKernel H F)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothChartedSpace F H hH
    mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
        (H.affinePointsTarget f (CommAlgCat.of F (InfiniteAdeleRing F))) 1
        (tangentVector F H hH x) =
      tangentVector F G hG (Lie.targetMapLinear f F x) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothChartedSpace F H hH
  apply (tangentKernelEquiv F G hG).injective
  funext v
  rw [tangentKernelEquiv_apply, tangentKernelEquiv_apply, tangentKernelMap_tangentVector]
  apply (RestrictScalars.addEquiv ℝ v.Completion (Additive (lieKernel G v.Completion))).injective
  have h := tangentKernelMap_naturality F hH hG f v (tangentVector F H hH x)
  rw [tangentKernelMap_tangentVector] at h
  refine h.trans ?_
  unfold placeKernelVector
  simp only [AddEquiv.apply_symm_apply]
  exact targetMapLinear_placeKernelVector F f x v

end Naturality

end Realization

end Langlands.Global.InfiniteAdelicGroupPoints
