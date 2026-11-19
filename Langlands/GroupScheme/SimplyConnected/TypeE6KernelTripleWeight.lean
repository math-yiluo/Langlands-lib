import Langlands.GroupScheme.SimplyConnected.TypeE6KernelWeights
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Rational.FundamentalRepresentationsAssembly
import Langlands.LinearAlgebra.TypeE6FirstWeightRoot

/-! # The triple of the first actual E6 weight and its kernel restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 6)

/-- The triple of the first actual integral fundamental weight of the supplied
E6 numbering. -/
def e6TripleFirstWeight :
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
        d.pinning.torus) :=
  (3 : ℤ) • d.absoluteFundamentalCharacter hsc (e.symm 0)

private theorem absoluteFundamentalCharacter_eq_firstWeight :
    d.absoluteFundamentalCharacter hsc (e.symm 0) =
      Langlands.TypeANegationWeyl.firstWeight
        d.pinning.rootDatum d.pinning.base e (d.pinning_corootSpan_eq_top hsc)
        (by decide) := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc)
  intro a
  simp only [absoluteFundamentalCharacter, Langlands.RootDatum.fundamentalWeightBasis_pairing,
    Langlands.TypeANegationWeyl.pairing_firstWeight, Equiv.eq_symm_apply,
    Fin.ext_iff, Fin.val_zero]

/-- The triple is dominant for the actual absolute pinning. -/
theorem e6TripleFirstWeight_isDominant :
    d.pinning.toSplitPinning.IsDominantWeight (d.e6TripleFirstWeight hsc e) := by
  have h := d.pinning.toSplitPinning.fundamentalWeightBasis_isDominant
    (d.pinning_corootSpan_eq_top hsc) (e.symm 0)
  intro a
  change 0 ≤ d.pinning.rootDatum.toLinearMap
    ((3 : ℤ) • d.absoluteFundamentalCharacter hsc (e.symm 0)) (d.pinning.rootDatum.coroot a.val)
  rw [map_zsmul, LinearMap.smul_apply]
  exact smul_nonneg (by decide : 0 ≤ (3 : ℤ)) (h a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Triviality of the full vertex action gives fixedness of the triple under
the full star action on the actual integral lattice. -/
theorem e6TripleFirstWeight_isStarFixed (hstar : d.StarIsTrivial) :
    d.pinning.IsStarFixedWeight (d.e6TripleFirstWeight hsc e) := by
  intro σ
  change (d.pinning.starAction σ).val.weightEquiv (d.e6TripleFirstWeight hsc e) = _
  simp only [e6TripleFirstWeight, map_zsmul, d.absoluteFundamentalCharacter_star,
    hstar σ (e.symm 0)]

/-- The triple belongs to the actual integral root span. -/
theorem e6TripleFirstWeight_mem_rootSpan
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) :
    d.e6TripleFirstWeight hsc e ∈ d.pinning.rootDatum.rootSpan ℤ := by
  rw [e6TripleFirstWeight, d.absoluteFundamentalCharacter_eq_firstWeight hsc e,
    Langlands.TypeE6FirstWeightRoot.three_zsmul_firstWeight
      d.pinning.rootDatum d.pinning.base e (d.pinning_corootSpan_eq_top hsc) hE]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

/-- The ambient triple restricts to the triple of the first integral weight
of the actual anisotropic kernel in the induced A5 numbering. -/
theorem weightRestriction_e6TripleFirstWeight
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) :
    d.anisotropicKernelIndex.comparison.weightRestriction (d.e6TripleFirstWeight hsc e) =
      (3 : ℤ) • Langlands.TypeANegationWeyl.firstWeight
        d.anisotropicKernelIndex.index.pinning.rootDatum
        d.anisotropicKernelIndex.index.pinning.base
        (d.anisotropicKernelIndex.comparison.e6BranchNumbering e h)
        (d.anisotropicKernelIndex.index.pinning_corootSpan_eq_top
          (d.anisotropicKernelIndex.isSimplyConnected hsc)) (by decide) := by
  rw [e6TripleFirstWeight, d.absoluteFundamentalCharacter_eq_firstWeight hsc e, map_zsmul,
    d.anisotropicKernel_weightRestriction_e6_firstWeight e h hsc]

end Langlands.GroupScheme.TitsIndexData
