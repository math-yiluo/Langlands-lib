import Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Plancherel.RationalCentralQuotient
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Positive forms from compact coefficients on the actual norm kernel -/

noncomputable section

open CategoryTheory MeasureTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

universe uG uV

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- Compact smooth-dual coefficients on a normal subgroup of finite index
modulo the full center give a positive form on the original carrier. -/
def compactRestrictionPositiveForm (c : UnitaryCentralCharacter ρ)
    (H : Subgroup G) [H.Normal] [(H ⊔ Subgroup.center G).FiniteIndex]
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (hcoeff : HasCompactSmoothDualCoefficients (ρ.comp H.subtype))
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) :
    InvariantPositiveForm ρ := by
  have : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  let hexists :=
    exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hρ hirr
  let ℓ : SmoothDual ρ := Classical.choose hexists
  have hℓ : ℓ.1 ≠ 0 := Classical.choose_spec hexists
  have hℓH : IsSmoothVector (Representation.dual (ρ.comp H.subtype)) ℓ.1 :=
    isSmoothVector_comp H.subtype continuous_subtype_val ℓ.2
  have hH : ∀ w : V, HasCompactSupport (matrixCoefficient (ρ.comp H.subtype) ℓ.1 w) :=
    fun w => hcoeff w ℓ.1 hℓH
  let Q := G ⧸ Subgroup.center G
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  have hL2 : ∀ v : V, MemLp (c.coefficientNorm ℓ.1 v) 2 (Measure.haar : Measure Q).inv :=
    fun v => (c.continuous_coefficientNorm ℓ.1 v (hρ v)).memLp_of_hasCompactSupport
      (c.hasCompactSupport_coefficientNorm_of_finiteIndex H ℓ.1 hH v)
  exact c.coefficientProductForm hρ hirr ℓ.1 hℓ (Measure.haar : Measure Q).inv hL2

end UnitaryCentralCharacter

namespace Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

local instance compactRestrictionPointAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance compactRestrictionPointTopology :
    TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- The actual central valuation index supplies finite index modulo the
full point-group center, so compact coefficients on the actual common
norm kernel give an invariant positive form. -/
def rationalNormKernelPositiveForm (s : T.toGrp ⟶ G) (hs : IsCentral s)
    (hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex)
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X))
    (hirr : A.IsIrreducible) (c : UnitaryCentralCharacter A.representation)
    (hcoeff : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation) :
    InvariantPositiveForm A.representation := by
  have := Plancherel.finite_rationalCentralQuotient s hs hindex
  have : (Plancherel.rationalCommonNormKernel G ⊔
      (rationalPoints.map s).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have : (Plancherel.rationalCommonNormKernel G ⊔
      Subgroup.center (RationalPoint k G.X)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (sup_le_sup_left hs.range_le_center _)
  apply c.compactRestrictionPositiveForm (Plancherel.rationalCommonNormKernel G)
    A.isSmooth hirr hcoeff
  intro K
  obtain ⟨L, hL, hLK⟩ := compactOpenSubgroupBasis (RationalPoint k G.X)
    (K : Set (RationalPoint k G.X)) K.mem_nhds_one
  exact ⟨L, hL, fun x hx => hLK hx⟩

/-- Unitarizability follows without an admissibility premise. -/
theorem isUnitarizable_of_compact_normKernel_restriction
    (s : T.toGrp ⟶ G) (hs : IsCentral s)
    (hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex)
    (A : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X))
    (hirr : A.IsIrreducible) (c : UnitaryCentralCharacter A.representation)
    (hcoeff : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation) :
    IsUnitarizable A.representation :=
  ⟨rationalNormKernelPositiveForm s hs hindex A hirr c hcoeff⟩

end Aubert.General.RationalPointFamily
end Langlands
