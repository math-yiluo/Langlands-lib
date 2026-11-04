import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Absolute.NormalSolvableCentrality
import Langlands.GroupScheme.Dynamic.RootedSolvableQuotientNormalizer

/-! # Proper Borel subgroups through a split torus with a root -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- A smooth connected solvable closed subgroup containing a split torus
with an actual root cannot be normal in a pseudo-reductive ambient group. -/
theorem not_isNormal_range_of_relativeRoot_of_isSolvable
    (hG : IsPseudoReductive G) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    [Smooth B.X.hom] [ConnectedSpace B.X.left]
    (hB : IsSolvableGroupScheme B) (t : T.toGrp ⟶ B) (ht : t ≫ b = i) :
    ¬ (SubgroupFunctor.range b).IsNormal := by
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion b.hom.hom.left := hb
  let : IsAffineHom B.X.hom := by
    rw [← b.hom.hom.w]
    infer_instance
  intro hn
  have hc := hB.isCentral_of_normal_of_isPseudoReductive hG b hb hn
  apply not_isCentral_of_relativeRoot i hT hχ
  rw [← ht]
  exact hc.comp t

/-- A pseudo-reductive group with an actual root of a split torus is not
solvable. No maximality assumption on the torus is needed. -/
theorem not_isSolvableGroupScheme_of_relativeRoot
    (hG : IsPseudoReductive G) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) :
    ¬ IsSolvableGroupScheme G := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  intro hsolv
  have hid : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  apply not_isNormal_range_of_relativeRoot_of_isSolvable
    hG i hT hχ (𝟙 G) hid hsolv i (Category.comp_id i)
  intro Y g x _ _
  exact SubgroupFunctor.mem_range.mpr ⟨g * x * g⁻¹, by simp⟩

/-- Every morphism from a solvable group scheme to a pseudo-reductive
group with an actual root fails to be an isomorphism. -/
theorem not_isIso_of_relativeRoot_of_isSolvable
    (hG : IsPseudoReductive G) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (b : B ⟶ G) (hB : IsSolvableGroupScheme B) : ¬ IsIso b := by
  intro hb
  let : IsIso b := hb
  exact not_isSolvableGroupScheme_of_relativeRoot hG i hT hχ
    (hB.of_iso (asIso b).symm)

namespace BorelExistence

/-- An actual Borel through a prescribed subgroup, together with properness
of its inclusion in the ambient group. -/
structure ProperBorelContainingData (i : T.toGrp ⟶ G) extends BorelContainingData i where
  proper : ¬ IsIso inclusion

/-- A closed split torus with an actual root belongs to an actual proper
Borel in an algebraically closed pseudo-reductive group. -/
def properBorelContainingDataOfRelativeRoot
    (hG : IsPseudoReductive G) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) :
    ProperBorelContainingData i := by
  let : Smooth G.X.hom := hG.smooth
  let D := borelContainingData i
    ⟨hi, hT.smooth, hT.connectedSpace, isSolvableGroupScheme_of_commutative⟩
  exact ⟨D, not_isIso_of_relativeRoot_of_isSolvable hG i hT hχ
    D.inclusion D.isBorelSubgroup.isSolvableGroupScheme⟩

end BorelExistence

/-- A split maximal torus with an actual root lies in a proper Borel pair,
with the actual torus factorization retained. -/
theorem exists_proper_isBorelPair_of_relativeRoot
    (hG : IsPseudoReductive G) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
        (t : T.toGrp ⟶ B),
      IsBorelPair b i ∧ ¬ IsIso b ∧ t ≫ b = i := by
  let D := BorelExistence.properBorelContainingDataOfRelativeRoot hG i hT hi.2.1 hχ
  exact ⟨D.subgroup, D.inclusion, D.factor,
    ⟨D.isBorelSubgroup, hi, D.factor, D.factor_comp⟩, D.proper, D.factor_comp⟩

end Langlands.GroupScheme
