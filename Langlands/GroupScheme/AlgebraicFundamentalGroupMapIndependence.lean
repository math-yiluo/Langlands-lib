import Langlands.GroupScheme.AlgebraicFundamentalGroupMapCoroots
import Langlands.GroupScheme.AlgebraicFundamentalGroupFactorizationConjugacy
import Langlands.GroupScheme.AlgebraicFundamentalGroupStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Independence of geometric torus factorizations for fundamental-group maps -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k H) (b c : Choice k G) (f : H ⟶ G)
  (E : Type u) [Field E] [Algebra k E] [IsSepClosure k E]

omit [IsSepClosure k E] in
/-- The chosen maximal torus remains maximal over the field extension. -/
theorem geometric_isMaximalTorus :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion) := by
  let := b.isCover.isConnectedReductive.smooth
  let := b.isCover.isConnectedReductive.isAffineHom
  exact (maximalTorusBaseChange k E G b.torus b.inclusion
    b.isMaximal.1 b.isMaximal.2.1).mp b.isMaximal

/-- The geometric chosen torus is split. -/
theorem geometric_isSplitTorus :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus).toGrp := by
  let : IsSepClosed E := IsSepClosure.sep_closed k
  exact SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning _
    (b.geometric_isMaximalTorus E).1

/-- The geometric chosen torus is maximal split. -/
theorem geometric_isMaximalSplitTorus :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion) :=
  (b.geometric_isMaximalTorus E).isMaximalSplitTorus (b.geometric_isSplitTorus E)

variable
  (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
  (e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus)
  (he : a.IsTorusFactorization E b f e)
  (he' : a.IsTorusFactorization E c f e')

include he he' in
/-- Two geometric factorizations admit a conjugation comparison compatible with
their torus homomorphisms. -/
theorem exists_factorizationComparison :
    ∃ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (t : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus),
      b.IsConjugationComparison E c g t ∧ e ≫ t.hom = e' := by
  have hGE := b.isCover.isConnectedReductive.baseChange_of_algebraicExtension (K := E)
  let := hGE.smooth
  let := hGE.isAffineHom
  let := hGE.connectedSpace
  dsimp only [IsTorusFactorization] at he he'
  obtain ⟨g, t, ht, hq, _⟩ := exists_conjugacy_of_split_torus_factorizations
    (G := (GroupScheme.baseChange (algebraBaseMap k E)).obj G)
    (A := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus)
    (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
    (T' := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus)
    (a.geometric_isSplitTorus E)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion)
    (b.geometric_isMaximalSplitTorus E) (c.geometric_isMaximalSplitTorus E)
    (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom e')
    (he.symm.trans he')
  let tc : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus :=
    { hom := Additive.ofMul t.hom
      inv := Additive.ofMul t.inv
      hom_inv_id := congrArg Additive.ofMul t.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul t.inv_hom_id }
  exact ⟨g, tc, ht, congrArg Additive.ofMul hq⟩

variable (hcomparison : AlgebraicFundamentalGroupComparisonStatement.{u})

include hcomparison in
/-- Canonical comparison carries one elementary quotient map to every other one. -/
theorem factorizationMap_comparison :
    (b.comparison E c).comp (a.factorizationMap b f E e he) =
      a.factorizationMap c f E e' he' := by
  obtain ⟨g, t, ht, hq⟩ := a.exists_factorizationComparison b c f E e e' he he'
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  change b.comparison E c (b.projection E (ν ≫ e)) = c.projection E (ν ≫ e')
  rw [(hcomparison k E G b.isCover.isConnectedReductive).1 b c |>.2.2.2.2 g t ht,
    Category.assoc, hq]

/-- The map to any chosen target presentation obtained using one factorization. -/
def factorizationMapTo : a.atChoice E →ₗ[ℤ] c.atChoice E :=
  (b.comparison E c).comp (a.factorizationMap b f E e he)

include hcomparison in
/-- Every elementary construction satisfies the law for all factorizations. -/
theorem factorizationMapTo_isInducedMap :
    a.IsInducedMap E c f (a.factorizationMapTo b c f E e he) := by
  refine ⟨⟨b, e, he⟩, ?_⟩
  intro d q hq ν
  have hcomp := (hcomparison k E G b.isCover.isConnectedReductive).2.2 b d c
  have hind := a.factorizationMap_comparison b d f E e q he hq hcomparison
  have h := congrArg (fun m : a.atChoice E →ₗ[ℤ] c.atChoice E =>
      m (a.projection E ν))
    (show (d.comparison E c).comp (a.factorizationMap d f E q hq) =
        a.factorizationMapTo b c f E e he by
      rw [← hind, ← LinearMap.comp_assoc, hcomp]
      rfl)
  exact h.symm

include hcomparison in
/-- Existence of the induced map follows from canonical comparison. -/
theorem exists_isInducedMap_of_comparison :
    ∃ m, a.IsInducedMap E c f m := by
  obtain ⟨b, e, he⟩ := a.exists_isTorusFactorization c f E
  exact ⟨_, a.factorizationMapTo_isInducedMap b c f E e he hcomparison⟩

end Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice
