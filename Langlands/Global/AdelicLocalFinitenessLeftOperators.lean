import Langlands.Global.AdelicLocalFinitenessResidualOperators
import Langlands.Global.AdelicLocalFinitenessSmoothing
import Langlands.Analysis.Meromorphic.PiOperatorAssembly

/-! # The left-hand operator family of the boundary model

On the weighted Hilbert space of the Siegel region, the left-hand operator `μ_s` of the
Fredholm system assembles, for every Harish-Chandra component and central orthant, the
restriction of the component to its box and the restrictions of its difference residuals to the
positive region. It is a weakly holomorphic family when the coefficients are holomorphic, and a
topological embedding at a parameter where the strict norm bound holds.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal Manifold

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints AdelicSiegelFactors
  Langlands.Analysis.Meromorphic
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

private instance : IsClosedImmersion (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom 𝓕.i 𝓕.ν ∅

private instance : IsAffine (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K)
  [Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν)] [DecidableEq (simpleRelativeRoots 𝓕.i 𝓕.ν)] {r : ℕ}
  (e : RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅) ≃L[ℝ]
    ((simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) × (Fin r → ℝ)))

/-- The directions of a component `P`: the simple roots outside its Levi index and the central
indices. -/
abbrev BoundaryDirection (P : Finset (characterLattice 𝓕.T)) (r : ℕ) :=
  {β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r

/-- The index of the coordinates of the boundary operators: a component `P ⊆ Δ`, an orthant `ε`,
and either the box (`none`) or a direction (`some k`). -/
abbrev BoundaryIndex (r : ℕ) :=
  (P : {P // P ∈ 𝓕.simpleRootFinset.powerset}) × (Fin r → Bool) ×
    Option (𝓕.BoundaryDirection P.1 r)

/-- The region of a coordinate: the box `orthantBox` of the component and orthant for `none`,
the positive region `orthantPos` for `some k`. -/
def boundaryRegion (τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    (ω : 𝓕.BoundaryIndex r) : Set (AdelicGroupPoints F G) :=
  match ω.2.2 with
  | none => orthantBox (chamberCoords hK e) τ
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex ω.1.1).1) ω.2.1 (m ω.1.1 ω.2.1)
  | some _ => orthantPos (chamberCoords hK e) τ
      (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex ω.1.1).1) ω.2.1

theorem siegelHeightRegion_eq (τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) :
    WeightedSiegel.siegelHeightRegion (⇑e) τ = ⇑e ⁻¹' siegelRegion τ := rfl

/-- The weighted Hilbert space of the Siegel region of heights. -/
abbrev siegelHilbert (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ) :=
  WeightedSiegel.HilbertSpace F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK
    (localFinitenessLogWeight ra rb ∘ e)
    (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ⁻¹'
      WeightedSiegel.siegelHeightRegion (⇑e) τ)

theorem measurableSet_siegelHeightRegion (τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) :
    @MeasurableSet _ (borel _) (WeightedSiegel.siegelHeightRegion (⇑e) τ) := by
  let : MeasurableSpace (RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := borel _
  have : BorelSpace (RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := ⟨rfl⟩
  exact (WeightedSiegel.isOpen_siegelHeightRegion e.continuous τ).measurableSet

theorem continuous_siegelLogWeight (ra : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ) :
    Continuous (localFinitenessLogWeight ra rb ∘ e) :=
  (continuous_localFinitenessLogWeight ra rb).comp e.continuous

/-- The Siegel measure is the frame measure of the Siegel region. -/
theorem measurePreserving_id_siegelHaar (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (rb : Fin r → ℝ) :
    MeasurePreserving id (𝓕.siegelHaar hK e ra τ rb)
      (WeightedSiegel.frameMeasure hK (localFinitenessLogWeight ra rb ∘ e)
        (WeightedSiegel.siegelHeightRegion (⇑e) τ)) := by
  rw [siegelHeightRegion_eq, frameMeasure_eq_domainWeightedHaar hK e ra τ rb]
  exact MeasurePreserving.id _

/-- The isometric embedding of the weighted Siegel Hilbert space into `L²` of the Siegel weight
on `G(𝔸)`: composition with `G(𝔸) → G(F) \ G(𝔸)`. -/
def siegelEmbedding (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ) :
    𝓕.siegelHilbert hK e ra τ rb →ₗᵢ[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) :=
  (Lp.compMeasurePreservingₗᵢ ℂ id (𝓕.measurePreserving_id_siegelHaar hK e ra τ rb)).comp
    (WeightedSiegel.frameEmbedding hK _ (𝓕.continuous_siegelLogWeight e ra rb) _
      (𝓕.measurableSet_siegelHeightRegion e τ))

/-- The embedding is composition with the quotient map on representatives. -/
theorem siegelEmbedding_ae (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ)
    (b : 𝓕.siegelHilbert hK e ra τ rb) :
    𝓕.siegelEmbedding hK e ra τ rb b =ᵐ[𝓕.siegelHaar hK e ra τ rb]
      fun g => b (LeftCosetSpace.mk (rationalSubgroup F G) g) := by
  have hmp := 𝓕.measurePreserving_id_siegelHaar hK e ra τ rb
  have h1 := Lp.coeFn_compMeasurePreserving (WeightedSiegel.frameEmbedding hK _
    (𝓕.continuous_siegelLogWeight e ra rb) _ (𝓕.measurableSet_siegelHeightRegion e τ) b) hmp
  have h2 := hmp.quasiMeasurePreserving.ae_eq_comp (WeightedSiegel.frameEmbedding_ae hK _
    (𝓕.continuous_siegelLogWeight e ra rb) _ (𝓕.measurableSet_siegelHeightRegion e τ) b)
  exact h1.trans h2

/-- The core operator of a coordinate before restriction: the Harish-Chandra component `E P` for
the box, the residual operator `L m + ∑_q p_q L q` of the direction for a positive region. -/
def boundaryLhsCore {μ₀ : Measure (AdelicGroupPoints F G)}
    (E : Finset (characterLattice 𝓕.T) → (Lp ℂ 2 μ₀ →L[ℂ] Lp ℂ 2 μ₀))
    (Lsh : ∀ (P : Finset (characterLattice 𝓕.T)), (Fin r → Bool) → 𝓕.BoundaryDirection P r → ℕ →
      (Lp ℂ 2 μ₀ →L[ℂ] Lp ℂ 2 μ₀))
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    (p : ∀ P ε k, Fin (m P ε k) → ℂ) (ω : 𝓕.BoundaryIndex r) : Lp ℂ 2 μ₀ →L[ℂ] Lp ℂ 2 μ₀ :=
  match ω.2.2 with
  | none => E ω.1.1
  | some k => residualOperator (Lsh ω.1.1 ω.2.1 k) (p ω.1.1 ω.2.1 k)

open scoped Classical in
/-- **The left-hand operator family.** For each parameter `s`, the assembly over all coordinates
`ω = (P, ε, ·)` of the restriction to `boundaryRegion ω` of the core operator applied to the
embedding of the weighted Siegel Hilbert space: the Harish-Chandra component `E P` on the box and
the residual operators with coefficients `p s P ε k` on the positive region. -/
def boundaryLhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ)
    (E : Finset (characterLattice 𝓕.T) →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (Lsh : ∀ (P : Finset (characterLattice 𝓕.T)), (Fin r → Bool) → 𝓕.BoundaryDirection P r → ℕ →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {Par : Type*} (p : Par → ∀ P ε k, Fin (m P ε k) → ℂ) (s : Par) :
    𝓕.siegelHilbert hK e ra τ rb →L[ℂ] PiLp 2 (fun ω : 𝓕.BoundaryIndex r =>
      Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict (𝓕.boundaryRegion hK e τ m ω))) :=
  piAssemble fun ω => LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ
    (𝓕.siegelHaar hK e ra τ rb) 2 (𝓕.boundaryRegion hK e τ m ω) ∘L
      𝓕.boundaryLhsCore E Lsh m (p s) ω ∘L (𝓕.siegelEmbedding hK e ra τ rb).toContinuousLinearMap

section Holomorphy

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E' H)
  {Par : Type*} [TopologicalSpace Par] [ChartedSpace H Par]

open scoped Classical in
/-- With coefficients complex differentiable on `S`, the left-hand family is weakly holomorphic
on `S`. -/
theorem isHolomorphicOperatorFamilyOn_boundaryLhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (rb : Fin r → ℝ)
    (E : Finset (characterLattice 𝓕.T) →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (Lsh : ∀ (P : Finset (characterLattice 𝓕.T)), (Fin r → Bool) → 𝓕.BoundaryDirection P r → ℕ →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    (p : Par → ∀ P ε k, Fin (m P ε k) → ℂ) (S : Set Par)
    (hp : ∀ P ε k q, MDifferentiableOn I 𝓘(ℂ, ℂ) (fun s => p s P ε k q) S) :
    IsHolomorphicOperatorFamilyOn I (fun s => 𝓕.boundaryLhs hK e ra τ rb E Lsh m p s) S := by
  refine IsHolomorphicOperatorFamilyOn.piAssemble fun ω => ?_
  have hcore : IsHolomorphicOperatorFamilyOn I
      (fun s => 𝓕.boundaryLhsCore E Lsh m (p s) ω) S := by
    rcases ω with ⟨P, ε, _ | k⟩
    · exact isHolomorphicOperatorFamilyOn_const _
    · change IsHolomorphicOperatorFamilyOn I (fun s => Lsh P.1 ε k (m P.1 ε k) +
        ∑ q, p s P.1 ε k q • Lsh P.1 ε k (q : ℕ)) S
      exact (isHolomorphicOperatorFamilyOn_const _).add
        (isHolomorphicOperatorFamilyOn_sum_smul Finset.univ _ fun q _ => hp P.1 ε k q)
  exact (hcore.comp_clm (𝓕.siegelEmbedding hK e ra τ rb).toContinuousLinearMap).clm_comp
    (LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2
      (𝓕.boundaryRegion hK e τ m ω))

end Holomorphy

open scoped Classical in
/-- **The left-hand family is an embedding** at a parameter where the strict norm bound of
`exists_residualOperators` holds for its coefficients. -/
theorem isEmbedding_boundaryLhs (ra τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ)
    (E : Finset (characterLattice 𝓕.T) →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (Lsh : ∀ (P : Finset (characterLattice 𝓕.T)), (Fin r → Bool) → 𝓕.BoundaryDirection P r → ℕ →
      (Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb) →L[ℂ] Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb)))
    (m : ∀ (P : Finset (characterLattice 𝓕.T)) (_ε : Fin r → Bool), 𝓕.BoundaryDirection P r → ℕ)
    {Par : Type*} (p : Par → ∀ P ε k, Fin (m P ε k) → ℂ) (s₀ : Par) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ Fn : Lp ℂ 2 (𝓕.siegelHaar hK e ra τ rb),
      ‖Fn‖ ≤ C * ∑ P ∈ 𝓕.simpleRootFinset.powerset, ∑ ε : Fin r → Bool,
        (‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2
            (orthantBox (chamberCoords hK e) τ
              (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε (m P ε))
            (E P Fn)‖ +
          ∑ k, ‖LpToLpRestrictCLM (AdelicGroupPoints F G) ℂ ℂ (𝓕.siegelHaar hK e ra τ rb) 2
            (orthantPos (chamberCoords hK e) τ
              (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε)
            (residualOperator (Lsh P ε k) (p s₀ P ε k) Fn)‖)) :
    Topology.IsEmbedding (𝓕.boundaryLhs hK e ra τ rb E Lsh m p s₀) := by
  refine isEmbedding_piAssemble _ hC fun b => ?_
  rw [← (𝓕.siegelEmbedding hK e ra τ rb).norm_map b]
  refine (hbound _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.sum_coe_sort 𝓕.simpleRootFinset.powerset, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Fintype.sum_option]
  rfl

end Langlands.Global.StandardParabolicFamily
