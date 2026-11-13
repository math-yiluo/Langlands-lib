import Langlands.Automorphic.CuspidalArchimedeanPlaceComponent
import Langlands.Automorphic.ArchimedeanParameterReduction
import Langlands.Automorphic.PlaceCompactCovariance
import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation
import Langlands.Automorphic.OperatorCompactCompletion

/-! # Generic components from irreducible admissible components and Whittaker functionals

The global premise `CuspidalArchimedeanGenericComponentStatement` of the archimedean parameter
reduction asks, at every infinite place of every actual cuspidal realization, for an
irreducible admissible generic `(𝔤, K)`-module that embeds into the realization compatibly
with the place actions. This module proves that it follows from the two subspace statements
`CuspidalArchimedeanIrreducibleAdmissibleComponentStatement` and
`CuspidalArchimedeanWhittakerFunctionalStatement`:
`CuspidalArchimedeanGenericComponentBridgeStatement`, proved by
`cuspidalArchimedeanGenericComponentBridge`.

The steps are:

* the place actions restrict to every stable subspace (`PlaceComponent.restrictCompact`,
  `PlaceComponent.restrictLie`), and the restriction keeps finite vectors, irreducibility,
  admissibility, genericity and the axioms of `Archimedean.IsRealGKModule` and
  `Archimedean.IsComplexGKModule`;
* on a whole actual realization, the place actions at one infinite place satisfy those
  axioms: continuity and differentiation along curves are tested against every linear
  functional through the Library's point-evaluation and compact-curve results, and the
  covariance is the Library's same-place covariance.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

namespace PlaceComponent

section Restrict

variable {K : Type*} [Group K] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {κ : Representation ℂ K V} {π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}

/-- The compact action restricted to a stable subspace. -/
def restrictCompact (hW : IsStable κ π W) : Representation ℂ K W :=
  (⟨W, fun k _ hx => hW.1 k _ hx⟩ : Subrepresentation κ).toRepresentation

@[simp] theorem restrictCompact_apply (hW : IsStable κ π W) (k : K) (x : W) :
    ((restrictCompact hW k x : W) : V) = κ k x := rfl

/-- The Lie action restricted to a stable subspace. -/
def restrictLie (hW : IsStable κ π W) : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W where
  toFun X := (π X).restrict (fun x hx => hW.2 X x hx)
  map_add' X Y := by
    ext x
    simp
  map_smul' c X := by
    ext x
    simp
  map_lie' := by
    intro X Y
    ext x
    simp [LieRing.of_associative_ring_bracket, Module.End.mul_apply]

@[simp] theorem restrictLie_apply (hW : IsStable κ π W) (X : 𝔤) (x : W) :
    ((restrictLie hW X x : W) : V) = π X x := rfl

/-- Finite vectors of the ambient compact action stay finite for the restriction. -/
theorem isFiniteVector_restrictCompact (hW : IsStable κ π W) (x : W)
    (hx : FiniteVectors.IsFiniteVector κ (x : V)) :
    FiniteVectors.IsFiniteVector (restrictCompact hW) x := by
  have : Module.Finite ℂ (FiniteVectors.orbitSpan κ (x : V)) := hx
  have hle : FiniteVectors.orbitSpan (restrictCompact hW) x ≤
      (FiniteVectors.orbitSpan κ (x : V)).comap W.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact FiniteVectors.action_mem_orbitSpan κ k (x : V)
  let f : FiniteVectors.orbitSpan (restrictCompact hW) x →ₗ[ℂ]
      FiniteVectors.orbitSpan κ (x : V) := W.subtype.restrict hle
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : FiniteVectors.orbitSpan κ (x : V) => (y : V)) h
  exact Module.Finite.of_injective f hf

/-- An irreducible stable subspace is an irreducible `(𝔤, K)`-module. -/
theorem isIrreducibleGKModule_restrict (h : IsIrreducible κ π W) :
    Archimedean.IsIrreducibleGKModule (restrictCompact h.2.1) (restrictLie h.2.1) := by
  obtain ⟨hne, hW, hmin⟩ := h
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hne, fun U hUk hUX => ?_⟩
  have hstab : IsStable κ π (U.map W.subtype) := by
    refine ⟨?_, ?_⟩
    · rintro k _ ⟨y, hy, rfl⟩
      exact ⟨restrictCompact hW k y, hUk k y hy, rfl⟩
    · rintro X _ ⟨y, hy, rfl⟩
      exact ⟨restrictLie hW X y, hUX X y hy, rfl⟩
  have hle : U.map W.subtype ≤ W := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  rcases hmin _ hle hstab with h0 | hT
  · left
    rw [eq_bot_iff]
    intro y hy
    have : (y : V) ∈ U.map W.subtype := ⟨y, hy, rfl⟩
    rw [h0] at this
    simp only [Submodule.mem_bot] at this ⊢
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro y _
    have : (y : V) ∈ U.map W.subtype := by
      rw [hT]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    have : z = y := Subtype.ext hzy
    exact this ▸ hz

/-- Admissibility of a stable subspace is admissibility of the restricted action. -/
theorem isAdmissibleGKModule_restrict [TopologicalSpace K] (hW : IsStable κ π W)
    (h : IsAdmissible κ W) : Archimedean.IsAdmissibleGKModule (restrictCompact hW) := by
  intro d τ hτ
  have : FiniteDimensional ℂ (intertwiners κ W d τ) := h d τ hτ
  let f : Archimedean.gkIntertwiners (restrictCompact hW) d τ →ₗ[ℂ] intertwiners κ W d τ :=
    { toFun := fun T => ⟨W.subtype ∘ₗ T.val, fun x => (T.val x).2, fun k x => by
        have := congrArg (fun y : W => (y : V)) (T.2 k x)
        simpa using this⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro S T hST
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun U : intertwiners κ W d τ => (U : (Fin d → ℂ) →ₗ[ℂ] V) x) hST
  exact Module.Finite.of_injective f hf

end Restrict

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {K : Type*} [Group K]
  {κ : Representation ℂ K V}

/-- A real-place Whittaker functional nonzero on a stable subspace makes the restricted
module generic. -/
theorem isRealGenericGKModule_restrict
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}
    (hW : IsStable κ π W) (h : IsRealGeneric π W) :
    Archimedean.IsRealGenericGKModule n (restrictLie hW) := by
  obtain ⟨a, ha, ℓ, ⟨x, hxW, hx⟩, hℓ⟩ := h
  refine ⟨ℓ ∘ₗ W.subtype, fun h0 => hx ?_, a, ha, fun X hX y => ?_⟩
  · simpa using congrArg (fun μ : W →ₗ[ℂ] ℂ => μ ⟨x, hxW⟩) h0
  · exact hℓ X hX y y.2

/-- A complex-place Whittaker functional nonzero on a stable subspace makes the restricted
module generic. -/
theorem isComplexGenericGKModule_restrict
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}
    (hW : IsStable κ π W) (h : IsComplexGeneric π W) :
    Archimedean.IsComplexGenericGKModule n (restrictLie hW) := by
  obtain ⟨a, ha, ℓ, ⟨x, hxW, hx⟩, hℓ⟩ := h
  refine ⟨ℓ ∘ₗ W.subtype, fun h0 => hx ?_, a, ha, fun X hX y => ?_⟩
  · simpa using congrArg (fun μ : W →ₗ[ℂ] ℂ => μ ⟨x, hxW⟩) h0
  · exact hℓ X hX y y.2

end Generic

end PlaceComponent

open Langlands.Global Langlands.Global.ArchimedeanGL

/-! ## Gluing an arbitrary `(𝔤, K)`-structure to a stable subspace -/

namespace PlaceComponent

section RestrictGK

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- A stable subspace of a real-place `(𝔤𝔩_n(ℝ), O(n))`-structure is again one. -/
theorem isRealGKModule_restrict
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}
    (hW : IsStable κ π W) (h : Archimedean.IsRealGKModule n κ π) :
    Archimedean.IsRealGKModule n (restrictCompact hW) (restrictLie hW) := by
  obtain ⟨hfin, hcont, hder, hcov⟩ := h
  refine ⟨fun x => isFiniteVector_restrictCompact hW x (hfin x), fun x ℓ => ?_,
    fun γ X hγ0 hγ x ℓ => ?_, fun k X x => Subtype.ext (hcov k X x)⟩
  · obtain ⟨μ, rfl⟩ := LinearMap.exists_extend ℓ
    exact hcont x μ
  · obtain ⟨μ, rfl⟩ := LinearMap.exists_extend ℓ
    exact hder γ X hγ0 hγ x μ

/-- A stable subspace of a complex-place `(𝔤𝔩_n(ℂ), U(n))`-structure is again one. -/
theorem isComplexGKModule_restrict
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V} {W : Submodule ℂ V}
    (hW : IsStable κ π W) (h : Archimedean.IsComplexGKModule n κ π) :
    Archimedean.IsComplexGKModule n (restrictCompact hW) (restrictLie hW) := by
  obtain ⟨hfin, hcont, hder, hcov⟩ := h
  refine ⟨fun x => isFiniteVector_restrictCompact hW x (hfin x), fun x ℓ => ?_,
    fun γ X hγ0 hγ x ℓ => ?_, fun k X x => Subtype.ext (hcov k X x)⟩
  · obtain ⟨μ, rfl⟩ := LinearMap.exists_extend ℓ
    exact hcont x μ
  · obtain ⟨μ, rfl⟩ := LinearMap.exists_extend ℓ
    exact hder γ X hγ0 hγ x μ

end RestrictGK

end PlaceComponent

/-! ## Curves at one place in archimedean matrix coordinates -/

section PlaceCurves

open scoped Classical Matrix.Norms.Operator

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- Real-linear insertion of a real matrix at one real place of the archimedean matrix
coordinates, with zero at every other place. -/
def realPlaceMatrixInsertion (v : RP) : (Fin n → Fin n → ℝ) →ₗ[ℝ] ArchimedeanMatrix F n where
  toFun M := Matrix.of fun i j => ((Pi.single v (M i j) : RP → ℝ), (0 : CP → ℂ))
  map_add' M N := by
    ext i j <;> simp [Pi.single_add]
  map_smul' c M := by
    refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · by_cases hw : w = v
      · subst hw
        simp
      · simp [hw]
    · simp

/-- Real-linear insertion of a complex matrix at one complex place of the archimedean
matrix coordinates, with zero at every other place. -/
def complexPlaceMatrixInsertion (v : CP) : (Fin n → Fin n → ℂ) →ₗ[ℝ] ArchimedeanMatrix F n where
  toFun M := Matrix.of fun i j => ((0 : RP → ℝ), (Pi.single v (M i j) : CP → ℂ))
  map_add' M N := by
    ext i j <;> simp [Pi.single_add]
  map_smul' c M := by
    refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp
    · by_cases hw : w = v
      · subst hw
        simp
      · simp [hw]

/-- The archimedean coordinates of the identity with the entries at one real place
replaced by zero. -/
def realPlaceMatrixBase (v : RP) : ArchimedeanMatrix F n :=
  Matrix.of fun i j => ((fun w => if w = v then 0 else (1 : RM) i j), fun _ => (1 : CM) i j)

/-- The archimedean coordinates of the identity with the entries at one complex place
replaced by zero. -/
def complexPlaceMatrixBase (v : CP) : ArchimedeanMatrix F n :=
  Matrix.of fun i j => ((fun _ => (1 : RM) i j), fun w => if w = v then 0 else (1 : CM) i j)

omit [NumberField F] in
theorem coordinates_realPlaceCompactInclusion (v : RP) (k : RK) :
    (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v k).val :
        ArchimedeanMatrix F n) =
      realPlaceMatrixInsertion v (Matrix.of.symm (k : RM)) +
        realPlaceMatrixBase v := by
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrFun (congrFun (realMatrix_realPlaceCompactInclusion F n v w k) i) j
    change ArchimedeanGL.realMatrix F n _ w i j = _
    rw [h]
    by_cases hw : w = v
    · subst hw
      simp [realPlaceMatrixInsertion, realPlaceMatrixBase]
    · simp [realPlaceMatrixInsertion, realPlaceMatrixBase, hw]
  · have h := congrFun (congrFun (complexMatrix_realPlaceCompactInclusion F n v w k) i) j
    change ArchimedeanGL.complexMatrix F n _ w i j = _
    rw [h]
    simp [realPlaceMatrixInsertion, realPlaceMatrixBase]

omit [NumberField F] in
theorem coordinates_complexPlaceCompactInclusion (v : CP) (k : CK) :
    (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v k).val :
        ArchimedeanMatrix F n) =
      complexPlaceMatrixInsertion v (Matrix.of.symm (k : CM)) +
        complexPlaceMatrixBase v := by
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrFun (congrFun (realMatrix_complexPlaceCompactInclusion F n v w k) i) j
    change ArchimedeanGL.realMatrix F n _ w i j = _
    rw [h]
    simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase]
  · have h := congrFun (congrFun (complexMatrix_complexPlaceCompactInclusion F n v w k) i) j
    change ArchimedeanGL.complexMatrix F n _ w i j = _
    rw [h]
    by_cases hw : w = v
    · subst hw
      simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase]
    · simp [complexPlaceMatrixInsertion, complexPlaceMatrixBase, hw]

omit [NumberField F] in
theorem realLieAlgebraToMatrix_realPlaceLieInclusion (v : RP) (X : RM) :
    realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X) =
      realPlaceMatrixInsertion v (Matrix.of.symm X) := by
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrFun (congrFun (realProjection_realInclusion F n w v X) i) j
    rw [show ((realLieAlgebraToMatrix F n) ((realPlaceLieInclusion F n v) X) i j).1 w =
      realPlaceLieProjection F n w (realPlaceLieInclusion F n v X) i j from rfl, h]
    by_cases hw : w = v
    · subst hw
      simp [realPlaceMatrixInsertion]
    · simp [realPlaceMatrixInsertion, hw]
  · have h := congrFun (congrFun (complexProjection_realInclusion F n w v X) i) j
    rw [show ((realLieAlgebraToMatrix F n) ((realPlaceLieInclusion F n v) X) i j).2 w =
      complexPlaceLieProjection F n w (realPlaceLieInclusion F n v X) i j from rfl, h]
    simp [realPlaceMatrixInsertion]

omit [NumberField F] in
theorem realLieAlgebraToMatrix_complexPlaceLieInclusion (v : CP) (X : CM) :
    realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X) =
      complexPlaceMatrixInsertion v (Matrix.of.symm X) := by
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrFun (congrFun (realProjection_complexInclusion F n w v X) i) j
    rw [show ((realLieAlgebraToMatrix F n) ((complexPlaceLieInclusion F n v) X) i j).1 w =
      realPlaceLieProjection F n w (complexPlaceLieInclusion F n v X) i j from rfl, h]
    simp [complexPlaceMatrixInsertion]
  · have h := congrFun (congrFun (complexProjection_complexInclusion F n w v X) i) j
    rw [show ((realLieAlgebraToMatrix F n) ((complexPlaceLieInclusion F n v) X) i j).2 w =
      complexPlaceLieProjection F n w (complexPlaceLieInclusion F n v X) i j from rfl, h]
    by_cases hw : w = v
    · subst hw
      simp [complexPlaceMatrixInsertion]
    · simp [complexPlaceMatrixInsertion, hw]

/-- An entrywise differentiable curve in the orthogonal group at a real place is a
differentiable curve in archimedean matrix coordinates, with the inserted tangent. -/
theorem hasDerivAt_coordinates_realPlaceCompactInclusion (v : RP) (γ : ℝ → RK) (X : RM)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : RM) i j) (X i j) 0) :
    HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v (γ t)).val :
        ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => (Matrix.of.symm (γ t : RM)))
      (Matrix.of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact hγ i j
  have h := ((LinearMap.toContinuousLinearMap
    (realPlaceMatrixInsertion (F := F) (n := n) v)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hg).add_const (realPlaceMatrixBase v)
  have hfun : (fun t : ℝ => (archimedeanGLCoordinates F n
      (realPlaceCompactInclusion F n v (γ t)).val : ArchimedeanMatrix F n)) =
      fun t => realPlaceMatrixInsertion v (Matrix.of.symm (γ t : RM)) +
        realPlaceMatrixBase v :=
    funext fun t => coordinates_realPlaceCompactInclusion v (γ t)
  rw [hfun, realLieAlgebraToMatrix_realPlaceLieInclusion]
  exact h

/-- An entrywise differentiable curve in the unitary group at a complex place is a
differentiable curve in archimedean matrix coordinates, with the inserted tangent. -/
theorem hasDerivAt_coordinates_complexPlaceCompactInclusion (v : CP) (γ : ℝ → CK) (X : CM)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : CM) i j) (X i j) 0) :
    HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v (γ t)).val :
        ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => (Matrix.of.symm (γ t : CM)))
      (Matrix.of.symm X) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact hγ i j
  have h := ((LinearMap.toContinuousLinearMap
    (complexPlaceMatrixInsertion (F := F) (n := n) v)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hg).add_const (complexPlaceMatrixBase v)
  have hfun : (fun t : ℝ => (archimedeanGLCoordinates F n
      (complexPlaceCompactInclusion F n v (γ t)).val : ArchimedeanMatrix F n)) =
      fun t => complexPlaceMatrixInsertion v (Matrix.of.symm (γ t : CM)) +
        complexPlaceMatrixBase v :=
    funext fun t => coordinates_complexPlaceCompactInclusion v (γ t)
  rw [hfun, realLieAlgebraToMatrix_complexPlaceLieInclusion]
  exact h

end PlaceCurves

local instance gkComponentRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance gkComponentContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance gkComponentSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance gkComponentFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance gkComponentStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance gkComponentSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

set_option maxHeartbeats 800000 in
/-- On a finite-dimensional subspace, continuity of all point evaluations of a map gives
continuity of every complex linear functional of that map. -/
theorem continuous_dual_of_pointEvaluation {X : Type*} [TopologicalSpace X]
    (W : Submodule ℂ S.Space) [FiniteDimensional ℂ W] (g : X → W)
    (hg : ∀ x : AdelicGL F n, Continuous (fun k : X => S.pointEvaluation x (g k)))
    (μ : S.Space →ₗ[ℂ] ℂ) :
    Continuous (fun k : X => μ (g k)) := by
  have key : ∀ φ ∈ Submodule.span ℂ (Set.range fun x : AdelicGL F n =>
      (S.pointEvaluation x).comp W.subtype),
      Continuous (fun k : X => φ (g k)) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨x, rfl⟩ := hφ
      exact hg x
    | zero =>
      exact continuous_const
    | add φ ψ _ _ hφ hψ =>
      exact hφ.add hψ
    | smul a φ _ hφ =>
      exact hφ.const_smul a
  exact key (μ.comp W.subtype) ((S.span_pointEvaluation_eq_top W).symm ▸ Submodule.mem_top)

/-- Every linear functional of a full compact orbit is continuous. -/
theorem continuous_dual_compactOrbit (μ : S.Space →ₗ[ℂ] ℂ) (f : S.Space) :
    Continuous (fun k : standardInfiniteCompact F n => μ (S.compactRepresentation k f)) := by
  have hfin : Module.Finite ℂ (FiniteVectors.orbitSpan S.compactRepresentation f) :=
    S.compactRepresentation_isFiniteVector f
  exact S.continuous_dual_of_pointEvaluation (FiniteVectors.orbitSpan S.compactRepresentation f)
    (fun k => ⟨_, FiniteVectors.action_mem_orbitSpan _ k f⟩)
    (fun x => S.continuous_functionRealization_compactOrbit f x) μ

/-- Every linear functional of a real-place compact orbit is continuous. -/
theorem continuous_dual_realPlaceCompactRepresentation (v : RP) (μ : S.Space →ₗ[ℂ] ℂ)
    (f : S.Space) :
    Continuous (fun k : RK => μ (S.realPlaceCompactRepresentation v k f)) :=
  (S.continuous_dual_compactOrbit μ f).comp (realPlaceCompactInclusion F n v).continuous

/-- Every linear functional of a complex-place compact orbit is continuous. -/
theorem continuous_dual_complexPlaceCompactRepresentation (v : CP) (μ : S.Space →ₗ[ℂ] ℂ)
    (f : S.Space) :
    Continuous (fun k : CK => μ (S.complexPlaceCompactRepresentation v k f)) :=
  (S.continuous_dual_compactOrbit μ f).comp (complexPlaceCompactInclusion F n v).continuous

/-- Real-place compact translation along an entrywise differentiable curve is
differentiated against every linear functional by the real-place Lie action. -/
theorem hasDerivAt_dual_realPlaceCompactRepresentation (v : RP) (γ : ℝ → RK) (X : RM)
    (hγ0 : γ 0 = 1) (hγ : ∀ i j, HasDerivAt (fun t => (γ t : RM) i j) (X i j) 0)
    (μ : S.Space →ₗ[ℂ] ℂ) (f : S.Space) :
    HasDerivAt (fun t => μ (S.realPlaceCompactRepresentation v (γ t) f))
      (μ (S.realPlaceLieAction v (1 ⊗ₜ X) f)) 0 :=
  S.compactCurve_dual_deriv (realPlaceLieInclusion F n v X)
    (fun t => realPlaceCompactInclusion F n v (γ t)) (by simp [hγ0])
    (hasDerivAt_coordinates_realPlaceCompactInclusion v γ X hγ) μ f

/-- Complex-place compact translation along an entrywise differentiable curve is
differentiated against every linear functional by the complex-place Lie action. -/
theorem hasDerivAt_dual_complexPlaceCompactRepresentation (v : CP) (γ : ℝ → CK) (X : CM)
    (hγ0 : γ 0 = 1) (hγ : ∀ i j, HasDerivAt (fun t => (γ t : CM) i j) (X i j) 0)
    (μ : S.Space →ₗ[ℂ] ℂ) (f : S.Space) :
    HasDerivAt (fun t => μ (S.complexPlaceCompactRepresentation v (γ t) f))
      (μ (S.complexPlaceLieAction v (1 ⊗ₜ X) f)) 0 :=
  S.compactCurve_dual_deriv (complexPlaceLieInclusion F n v X)
    (fun t => complexPlaceCompactInclusion F n v (γ t)) (by simp [hγ0])
    (hasDerivAt_coordinates_complexPlaceCompactInclusion v γ X hγ) μ f

set_option maxHeartbeats 400000 in
/-- Same-place covariance in the matrix form of the `(𝔤, K)`-module predicates. -/
theorem realPlaceCompactRepresentation_realPlaceLieAction_tmul (v : RP) (k : RK) (X : RM)
    (f : S.Space) :
    S.realPlaceCompactRepresentation v k (S.realPlaceLieAction v (1 ⊗ₜ X) f) =
      S.realPlaceLieAction v (1 ⊗ₜ ((k : RM) * X * (star k : RM)))
        (S.realPlaceCompactRepresentation v k f) := by
  exact S.realPlaceCompactRepresentation_realPlaceLieAction v k (1 ⊗ₜ X) f

set_option maxHeartbeats 400000 in
theorem complexPlaceCompactRepresentation_complexPlaceLieAction_tmul (v : CP) (k : CK)
    (X : CM) (f : S.Space) :
    S.complexPlaceCompactRepresentation v k (S.complexPlaceLieAction v (1 ⊗ₜ X) f) =
      S.complexPlaceLieAction v (1 ⊗ₜ ((k : CM) * X * (star k : CM)))
        (S.complexPlaceCompactRepresentation v k f) := by
  exact S.complexPlaceCompactRepresentation_complexPlaceLieAction v k (1 ⊗ₜ X) f

/-- The real-place actions on an actual automorphic realization form a real-place
`(𝔤, K)`-structure in the sense of `Archimedean.IsRealGKModule`. -/
theorem isRealGKModule_realPlace (v : RP) :
    Archimedean.IsRealGKModule n (S.realPlaceCompactRepresentation v)
      (S.realPlaceLieAction v) :=
  ⟨S.realPlaceCompactRepresentation_isFiniteVector v,
    fun f μ => S.continuous_dual_realPlaceCompactRepresentation v μ f,
    fun γ X hγ0 hγ f μ => S.hasDerivAt_dual_realPlaceCompactRepresentation v γ X hγ0 hγ μ f,
    fun k X f => S.realPlaceCompactRepresentation_realPlaceLieAction_tmul v k X f⟩

/-- The complex-place actions on an actual automorphic realization form a complex-place
`(𝔤, K)`-structure in the sense of `Archimedean.IsComplexGKModule`. -/
theorem isComplexGKModule_complexPlace (v : CP) :
    Archimedean.IsComplexGKModule n (S.complexPlaceCompactRepresentation v)
      (S.complexPlaceLieAction v) :=
  ⟨S.complexPlaceCompactRepresentation_isFiniteVector v,
    fun f μ => S.continuous_dual_complexPlaceCompactRepresentation v μ f,
    fun γ X hγ0 hγ f μ =>
      S.hasDerivAt_dual_complexPlaceCompactRepresentation v γ X hγ0 hγ μ f,
    fun k X f => S.complexPlaceCompactRepresentation_complexPlaceLieAction_tmul v k X f⟩

/-- An irreducible, admissible, generic real-place component gives a real-place generic
component in the sense of `HasRealPlaceGenericComponent`. -/
theorem hasRealPlaceGenericComponent_of_component (v : RP) {W : Submodule ℂ S.Space}
    (hI : PlaceComponent.IsIrreducible (S.realPlaceCompactRepresentation v)
      (S.realPlaceLieAction v) W)
    (hA : PlaceComponent.IsAdmissible (S.realPlaceCompactRepresentation v) W)
    (hG : PlaceComponent.IsRealGeneric (S.realPlaceLieAction v) W) :
    S.HasRealPlaceGenericComponent v :=
  ⟨W, inferInstance, inferInstance, PlaceComponent.restrictCompact hI.2.1,
    PlaceComponent.restrictLie hI.2.1, W.subtype, Subtype.val_injective,
    fun _ _ => rfl, fun _ _ => rfl,
    PlaceComponent.isRealGKModule_restrict hI.2.1 (S.isRealGKModule_realPlace v),
    PlaceComponent.isIrreducibleGKModule_restrict hI,
    PlaceComponent.isAdmissibleGKModule_restrict hI.2.1 hA,
    PlaceComponent.isRealGenericGKModule_restrict hI.2.1 hG⟩

/-- An irreducible, admissible, generic complex-place component gives a complex-place
generic component in the sense of `HasComplexPlaceGenericComponent`. -/
theorem hasComplexPlaceGenericComponent_of_component (v : CP) {W : Submodule ℂ S.Space}
    (hI : PlaceComponent.IsIrreducible (S.complexPlaceCompactRepresentation v)
      (S.complexPlaceLieAction v) W)
    (hA : PlaceComponent.IsAdmissible (S.complexPlaceCompactRepresentation v) W)
    (hG : PlaceComponent.IsComplexGeneric (S.complexPlaceLieAction v) W) :
    S.HasComplexPlaceGenericComponent v :=
  ⟨W, inferInstance, inferInstance, PlaceComponent.restrictCompact hI.2.1,
    PlaceComponent.restrictLie hI.2.1, W.subtype, Subtype.val_injective,
    fun _ _ => rfl, fun _ _ => rfl,
    PlaceComponent.isComplexGKModule_restrict hI.2.1 (S.isComplexGKModule_complexPlace v),
    PlaceComponent.isIrreducibleGKModule_restrict hI,
    PlaceComponent.isAdmissibleGKModule_restrict hI.2.1 hA,
    PlaceComponent.isComplexGenericGKModule_restrict hI.2.1 hG⟩

end OperatorRealization

/-- **Generic place components from irreducible admissible components and place
Whittaker functionals.** The irreducible admissible component statement and the place
Whittaker functional statement together give the archimedean generic component
statement `CuspidalArchimedeanGenericComponentStatement`. -/
def CuspidalArchimedeanGenericComponentBridgeStatement : Prop :=
  CuspidalArchimedeanIrreducibleAdmissibleComponentStatement.{u} →
    CuspidalArchimedeanWhittakerFunctionalStatement.{u} →
      CuspidalArchimedeanGenericComponentStatement.{u}

/-- Proof of `CuspidalArchimedeanGenericComponentBridgeStatement`. -/
theorem cuspidalArchimedeanGenericComponentBridge :
    CuspidalArchimedeanGenericComponentBridgeStatement.{u} := by
  intro h₁ h₂ F _ _ _ r T
  have hW := h₂ F r T.realization T.cuspidal
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have hv := (h₁ F r T).1 v
    rcases hv with ⟨W, hI, hA⟩
    exact T.realization.hasRealPlaceGenericComponent_of_component v hI hA
      (hW.1 v W hI.1 hI.2.1)
  · have hv := (h₁ F r T).2 v
    rcases hv with ⟨W, hI, hA⟩
    exact T.realization.hasComplexPlaceGenericComponent_of_component v hI hA
      (hW.2 v W hI.1 hI.2.1)

end Langlands.Automorphic
