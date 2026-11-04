import Langlands.GroupScheme.Absolute.RegularRefinement
import Langlands.GroupScheme.Rational.RankOneCocharacterSymmetrization
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Regular integral symmetrization in semisimple rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Refine an actual cocharacter to be regular, then subtract its actual
normalizer translate in the integral cocharacter lattice. -/
def regularNormalizerSymmetrizedCocharacter
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (n : normalizerPoints i) (ν : cocharacterLattice T) : cocharacterLattice T :=
  normalizerSymmetrizedCocharacter i n (regularRefinement hT i ν)

variable (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i)

include hG hi hdep

/-- A nonidentity rank-one normalizer class doubles every refined root
pairing, in the integers and independently of the field characteristic. -/
theorem IsConnectedReductive.latticePairing_regularNormalizerSymmetrizedCocharacter
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T) {α : characterLattice T} (hα : α ∈ roots i) :
    latticePairing T α (regularNormalizerSymmetrizedCocharacter hT i n ν) =
      2 * latticePairing T α (regularRefinement hT i ν) :=
  hG.latticePairing_normalizerSymmetrizedCocharacter i hi hT hdep n hn α
    (regularRefinement hT i ν) hα

/-- Regularity survives symmetrization by a nonidentity rank-one normalizer
class, since twice a nonzero integer is nonzero. -/
theorem IsConnectedReductive.isGeneric_regularNormalizerSymmetrizedCocharacter
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T) :
    IsGenericCocharacter i (regularNormalizerSymmetrizedCocharacter hT i n ν) := by
  intro α hα hzero
  have hpair :=
    hG.latticePairing_regularNormalizerSymmetrizedCocharacter i hi hT hdep n hn ν hα
  have hne := regularRefinement_isRegular hT i ν α hα
  omega

/-- Every originally positive actual root remains positive after regular
refinement and integral rank-one symmetrization. -/
theorem IsConnectedReductive.regularNormalizerSymmetrizedCocharacter_pos
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T) {α : characterLattice T} (hα : α ∈ roots i)
    (hpos : 0 < latticePairing T α ν) :
    0 < latticePairing T α (regularNormalizerSymmetrizedCocharacter hT i n ν) := by
  rw [hG.latticePairing_regularNormalizerSymmetrizedCocharacter i hi hT hdep n hn ν hα]
  have := regularRefinement_pos hT i ν hα hpos
  omega

/-- The actual normalizer acts by exact negation on the regular symmetrized
cocharacter, including its central directions. -/
theorem IsConnectedReductive.cocharacterAut_regularNormalizerSymmetrizedCocharacter
    (ν : cocharacterLattice T) :
    cocharacterAut (normalizingAut i n)
        (regularNormalizerSymmetrizedCocharacter hT i n ν) =
      -regularNormalizerSymmetrizedCocharacter hT i n ν :=
  hG.cocharacterAut_normalizerSymmetrizedCocharacter i hi hT hdep n
    (regularRefinement hT i ν)

/-- The exact negation is also an equality of actual group-scheme
homomorphisms after conjugation by the supplied normalizer point. -/
theorem IsConnectedReductive.groupHom_regularNormalizerSymmetrizedCocharacter_comp_innerIso
    (ν : cocharacterLattice T) :
    (CommGroupScheme.groupHom (regularNormalizerSymmetrizedCocharacter hT i n ν) ≫ i) ≫
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom =
      CommGroupScheme.groupHom (-regularNormalizerSymmetrizedCocharacter hT i n ν) ≫ i :=
  hG.groupHom_normalizerSymmetrizedCocharacter_comp_innerIso i hi hT hdep n
    (regularRefinement hT i ν)

/-- The dynamic centralizer of the regular symmetrized cocharacter is the
centralizer of the whole torus, as subgroup functors on all relative tests. -/
theorem IsConnectedReductive.centralizer_regularNormalizerSymmetrizedCocharacter
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T) :
    Dynamic.centralizer
        (CommGroupScheme.groupHom (regularNormalizerSymmetrizedCocharacter hT i n ν) ≫ i) =
      torusCentralizer i :=
  genericCentralizer k G hG T i (hi.isMaximalSplitTorus hT)
    (regularNormalizerSymmetrizedCocharacter hT i n ν)
    (hG.isGeneric_regularNormalizerSymmetrizedCocharacter i hi hT hdep n hn ν)

end Langlands.GroupScheme
