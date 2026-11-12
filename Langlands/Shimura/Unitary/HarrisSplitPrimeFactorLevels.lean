import Langlands.Shimura.Unitary.HarrisSplitPrimeFactors
import Langlands.Shimura.Unitary.HarrisSplitPrimeLevels
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Harris's levels at a split prime in product form

At a degree-one place `𝔭` of the imaginary quadratic field above `v`, the decomposition
`(ℚ_v ⊗[F] A)ˣ ≅ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ` is an isomorphism of topological groups for the
module topologies. Hence a family of compact open subgroups `C_w ⊂ (K_w ⊗[K] A)ˣ` gives
Harris's level `K_p = Π_w C_w × ℤ_pˣ` of (4.1).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global AdelicFunctoriality

namespace CompactOpenLevel

variable {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- The product of compact open levels over a finite index set. -/
def pi (C : ∀ i, CompactOpenLevel (G i)) : CompactOpenLevel (∀ i, G i) where
  openSubgroup :=
    { toSubgroup := Subgroup.pi Set.univ fun i => (C i).subgroup
      isOpen' := isOpen_set_pi Set.finite_univ fun i _ => (C i).openSubgroup.isOpen }
  isCompact := isCompact_univ_pi fun i => (C i).isCompact

theorem mem_pi (C : ∀ i, CompactOpenLevel (G i)) (g : ∀ i, G i) :
    g ∈ (pi C).subgroup ↔ ∀ i, g i ∈ (C i).subgroup := by
  change (∀ i ∈ Set.univ, g i ∈ (C i).subgroup) ↔ _
  simp

end CompactOpenLevel

section FiniteDimensional

variable {S : Type*} [NontriviallyNormedField S] [CompleteSpace S]
variable {M : Type*} [AddCommGroup M] [Module S M] [TopologicalSpace M] [IsModuleTopology S M]
variable {N : Type*} [AddCommGroup N] [Module S N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousSMul S N] [T2Space N] [FiniteDimensional S N]

/-- A linear isomorphism from a module with the module topology onto a finite-dimensional
Hausdorff topological vector space over a complete nontrivially normed field is a
homeomorphism. -/
def linearEquivHomeomorph (φ : M ≃ₗ[S] N) : M ≃ₜ N where
  toEquiv := φ.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
  continuous_invFun :=
    haveI : IsModuleTopology S N := isModuleTopologyOfFiniteDimensional
    haveI := IsModuleTopology.toContinuousAdd S M
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap

end FiniteDimensional

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  [Module.Finite ℚ A]

variable (ι : F →+* K) (v : Global.FinitePlace ℚ) (𝔭 : FinitePlacesAbove F v)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v 𝔭.1))

/-- The coefficient map `ℚ_v → F_𝔭 → K_w` at a place `w` of `K` above `𝔭`. -/
def splitPlaceCoefficient (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    FiniteCompletion ℚ v →+* w.1.adicCompletion K :=
  letI := ι.toAlgebra
  (FiniteExtension.completionMap 𝔭.1 w.1).comp (FiniteExtension.completionMap v 𝔭.1)

omit [IsTotallyComplex K] [IsCMField F] [Algebra ℚ A] [IsScalarTower ℚ K A] [Module.Finite ℚ A] in
theorem continuous_splitPlaceCoefficient (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    Continuous (splitPlaceCoefficient ι v 𝔭 w) :=
  letI := ι.toAlgebra
  (FiniteExtension.continuous_completionMap 𝔭.1 w.1).comp
    (FiniteExtension.continuous_completionMap v 𝔭.1)

omit [IsTotallyComplex K] [IsCMField F] [Algebra ℚ A] [IsScalarTower ℚ K A] [Module.Finite ℚ A] in
theorem splitPlaceFactorEquiv_smul (c s : FiniteCompletion ℚ v) (a : A)
    (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    splitPlaceFactorEquiv A ι v 𝔭 h𝔭 ((c * s) ⊗ₜ[F] a) w =
      splitPlaceCoefficient ι v 𝔭 w c • splitPlaceFactorEquiv A ι v 𝔭 h𝔭 (s ⊗ₜ[F] a) w := by
  let := ι.toAlgebra
  let := imaginaryQuadraticAlgebra (A := A) ι
  let := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  rw [splitPlaceFactorEquiv_tmul, splitPlaceFactorEquiv_tmul, TensorProduct.smul_tmul',
    smul_eq_mul]
  change ((splitPlaceCoefficient ι v 𝔭 w) (c * s)) ⊗ₜ[K] a = _
  rw [map_mul]
  rfl

/-- The component of `splitPlaceFactorEquiv` at `w`, as a semilinear map over
`splitPlaceCoefficient`. -/
def splitPlaceComponent (w : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    FiniteCompletion ℚ v ⊗[F] A →ₛₗ[splitPlaceCoefficient ι v 𝔭 w]
      w.1.adicCompletion K ⊗[K] A :=
  letI := ι.toAlgebra
  letI := imaginaryQuadraticAlgebra (A := A) ι
  letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  { toFun := fun x => splitPlaceFactorEquiv A ι v 𝔭 h𝔭 x w
    map_add' := fun x y => by rw [map_add, Pi.add_apply]
    map_smul' := fun c x => by
      induction x using TensorProduct.inductionOn with
      | tmul s a =>
        change splitPlaceFactorEquiv A ι v 𝔭 h𝔭 (c • (s ⊗ₜ[F] a)) w = _
        rw [TensorProduct.smul_tmul', smul_eq_mul]
        exact splitPlaceFactorEquiv_smul ι v 𝔭 h𝔭 c s a w
      | add x y hx hy =>
        simp only [smul_add, map_add, Pi.add_apply] at hx hy ⊢
        rw [hx, hy] }

omit [IsTotallyComplex K] [IsCMField F] [Algebra ℚ A] [IsScalarTower ℚ K A] [Module.Finite ℚ A] in
/-- The decomposition is continuous for the module topologies. -/
theorem continuous_splitPlaceFactorEquiv :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    letI : TopologicalSpace (FiniteCompletion ℚ v ⊗[F] A) :=
      moduleTopology (FiniteCompletion ℚ v) _
    letI : ∀ w : FinitePlacesAbove K 𝔭.1, TopologicalSpace (w.1.adicCompletion K ⊗[K] A) :=
      fun w => moduleTopology (w.1.adicCompletion K) _
    Continuous (splitPlaceFactorEquiv A ι v 𝔭 h𝔭) := by
  let := ι.toAlgebra
  let := imaginaryQuadraticAlgebra (A := A) ι
  let := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  let : TopologicalSpace (FiniteCompletion ℚ v ⊗[F] A) := moduleTopology (FiniteCompletion ℚ v) _
  let : ∀ w : FinitePlacesAbove K 𝔭.1, TopologicalSpace (w.1.adicCompletion K ⊗[K] A) :=
    fun w => moduleTopology (w.1.adicCompletion K) _
  refine continuous_pi fun w => ?_
  have := ModuleTopology.continuousAdd (w.1.adicCompletion K) (w.1.adicCompletion K ⊗[K] A)
  have := ModuleTopology.continuousSMul (w.1.adicCompletion K) (w.1.adicCompletion K ⊗[K] A)
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_splitPlaceCoefficient ι v 𝔭 w)
    (splitPlaceComponent ι v 𝔭 h𝔭 w)

omit [IsTotallyComplex K] [IsCMField F] in
/-- The inverse of the decomposition is continuous: the product of the `K_w ⊗[K] A`, with
`ℚ_v` acting through `splitPlaceCoefficient`, is a finite-dimensional Hausdorff topological
`ℚ_v`-vector space, so it carries the `ℚ_v`-module topology. -/
theorem continuous_splitPlaceFactorEquiv_symm :
    letI := ι.toAlgebra
    letI := imaginaryQuadraticAlgebra (A := A) ι
    letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
    letI : TopologicalSpace (FiniteCompletion ℚ v ⊗[F] A) :=
      moduleTopology (FiniteCompletion ℚ v) _
    letI : ∀ w : FinitePlacesAbove K 𝔭.1, TopologicalSpace (w.1.adicCompletion K ⊗[K] A) :=
      fun w => moduleTopology (w.1.adicCompletion K) _
    Continuous (splitPlaceFactorEquiv A ι v 𝔭 h𝔭).symm := by
  let := ι.toAlgebra
  let := imaginaryQuadraticAlgebra (A := A) ι
  let := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  let : TopologicalSpace (FiniteCompletion ℚ v ⊗[F] A) := moduleTopology (FiniteCompletion ℚ v) _
  let : ∀ w : FinitePlacesAbove K 𝔭.1, TopologicalSpace (w.1.adicCompletion K ⊗[K] A) :=
    fun w => moduleTopology (w.1.adicCompletion K) _
  have := imaginaryQuadraticAlgebra_isScalarTower (A := A) ι
  have : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast ι q).symm
  have : Module.Finite K A := Module.Finite.of_restrictScalars_finite ℚ K A
  have : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have : Module.Finite F A := Module.Finite.trans K A
  let : ∀ w : FinitePlacesAbove K 𝔭.1,
      Module (FiniteCompletion ℚ v) (w.1.adicCompletion K ⊗[K] A) :=
    fun w => Module.compHom _ (splitPlaceCoefficient ι v 𝔭 w)
  have : ∀ w : FinitePlacesAbove K 𝔭.1, IsTopologicalAddGroup (w.1.adicCompletion K ⊗[K] A) :=
    fun w => IsModuleTopology.isTopologicalAddGroup (w.1.adicCompletion K) _
  have : ∀ w : FinitePlacesAbove K 𝔭.1,
      ContinuousSMul (FiniteCompletion ℚ v) (w.1.adicCompletion K ⊗[K] A) := fun w =>
    have := ModuleTopology.continuousSMul (w.1.adicCompletion K) (w.1.adicCompletion K ⊗[K] A)
    MulAction.continuousSMul_compHom (M := w.1.adicCompletion K)
      (X := w.1.adicCompletion K ⊗[K] A)
      (f := (splitPlaceCoefficient ι v 𝔭 w).toMonoidHom) (continuous_splitPlaceCoefficient ι v 𝔭 w)
  have : ∀ w : FinitePlacesAbove K 𝔭.1, T2Space (w.1.adicCompletion K ⊗[K] A) := fun w =>
    (AlgebraInvolution.coordinateEquiv (w.1.adicCompletion K)
      (Module.Free.chooseBasis K A)).toHomeomorph.isEmbedding.t2Space
  let Φℓ : (FiniteCompletion ℚ v ⊗[F] A) ≃ₗ[FiniteCompletion ℚ v]
      (Π w : FinitePlacesAbove K 𝔭.1, w.1.adicCompletion K ⊗[K] A) :=
    { (splitPlaceFactorEquiv A ι v 𝔭 h𝔭).toAddEquiv with
      map_smul' := fun c x => funext fun w => (splitPlaceComponent ι v 𝔭 h𝔭 w).map_smulₛₗ c x }
  have : FiniteDimensional (FiniteCompletion ℚ v)
      (Π w : FinitePlacesAbove K 𝔭.1, w.1.adicCompletion K ⊗[K] A) :=
    Φℓ.finiteDimensional
  let : NontriviallyNormedField (FiniteCompletion ℚ v) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact (linearEquivHomeomorph Φℓ).continuous_invFun

omit [IsTotallyComplex K] [IsCMField F] in
/-- The decomposition `(ℚ_v ⊗[F] A)ˣ ≃ Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ` as an isomorphism of topological
groups: `ℚ_v ⊗[F] A` carries the `ℚ_v`-module topology, each `K_w ⊗[K] A` the `K_w`-module
topology, and the units the units topology. -/
def splitPlaceUnitsHomeomorph :
    letI := ι.toAlgebra
    SplitPrimeUnits A ι v (splitPlaceEmbedding v 𝔭 h𝔭) ≃ₜ*
      (Π w : FinitePlacesAbove K 𝔭.1,
        ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)) :=
  letI := ι.toAlgebra
  letI := imaginaryQuadraticAlgebra (A := A) ι
  letI := (splitPlaceEmbedding v 𝔭 h𝔭).toAlgebra
  letI : TopologicalSpace (FiniteCompletion ℚ v ⊗[F] A) :=
    moduleTopology (FiniteCompletion ℚ v) _
  letI : ∀ w : FinitePlacesAbove K 𝔭.1, TopologicalSpace (w.1.adicCompletion K ⊗[K] A) :=
    fun w => moduleTopology (w.1.adicCompletion K) _
  { toMulEquiv :=
      (Units.mapEquiv (splitPlaceFactorEquiv A ι v 𝔭 h𝔭).toMulEquiv).trans MulEquiv.piUnits
    continuous_toFun := continuous_pi fun w => Units.continuous_iff.mpr
      ⟨(continuous_apply w).comp
          ((continuous_splitPlaceFactorEquiv ι v 𝔭 h𝔭).comp Units.continuous_val),
        (continuous_apply w).comp
          ((continuous_splitPlaceFactorEquiv ι v 𝔭 h𝔭).comp Units.continuous_coe_inv)⟩
    continuous_invFun := Units.continuous_iff.mpr
      ⟨(continuous_splitPlaceFactorEquiv_symm ι v 𝔭 h𝔭).comp
          (continuous_pi fun w => Units.continuous_val.comp (continuous_apply w)),
        (continuous_splitPlaceFactorEquiv_symm ι v 𝔭 h𝔭).comp
          (continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w))⟩ }

variable [Algebra E A] [IsScalarTower E K A] [IsScalarTower ℚ E A]
variable [Algebra.IsQuadraticExtension ℚ F]

omit [IsScalarTower E K A] in
/-- `splitPlaceUnitsHomeomorph` recovers the first coordinate of `splitPlacePoints`. -/
theorem splitPlaceUnitsHomeomorph_splitPrimeHomeomorph (σ : SecondKindInvolution E K A)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    splitPlaceUnitsHomeomorph ι v 𝔭 h𝔭
        (σ.splitPrimeHomeomorph ι v (splitPlaceEmbedding v 𝔭 h𝔭) g).1 =
      (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 :=
  rfl

/-- Harris's level `K_p = Π_{w ∣ 𝔭} C_w × ℤ_vˣ` of (4.1), for compact open subgroups
`C_w ⊂ (K_w ⊗[K] A)ˣ`: the points whose component at every `w` lies in `C_w` and whose
multiplier lies in `ℤ_vˣ`. -/
def SecondKindInvolution.splitPlaceLevel (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K))) :
    CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :=
  σ.splitPrimeLevel ι v (splitPlaceEmbedding v 𝔭 h𝔭)
    (CompactOpenLevel.transport (splitPlaceUnitsHomeomorph ι v 𝔭 h𝔭).symm
      (CompactOpenLevel.pi C))

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.mem_splitPlaceLevel (σ : SecondKindInvolution E K A)
    (C : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K)))
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ v)) :
    g ∈ (σ.splitPlaceLevel ι v 𝔭 h𝔭 C).subgroup ↔
      (∀ w, (σ.splitPlacePoints ι v 𝔭 h𝔭 g).1 w ∈ (C w).subgroup) ∧
        AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g ∈
          (integerUnitsLevel v).subgroup :=
  and_congr_left' (CompactOpenLevel.mem_pi C _)

omit [IsScalarTower E K A] in
theorem SecondKindInvolution.splitPlaceLevel_mono (σ : SecondKindInvolution E K A)
    {C C' : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1),
      CompactOpenLevel (ImaginaryQuadraticSplit.FactorUnits K A (w.1.adicCompletion K))}
    (h : ∀ w, (C w).subgroup ≤ (C' w).subgroup) :
    (σ.splitPlaceLevel ι v 𝔭 h𝔭 C).subgroup ≤ (σ.splitPlaceLevel ι v 𝔭 h𝔭 C').subgroup := by
  intro g hg
  rw [SecondKindInvolution.mem_splitPlaceLevel] at hg ⊢
  exact ⟨fun w => h w (hg.1 w), hg.2⟩

end Harris

end Langlands.Shimura
