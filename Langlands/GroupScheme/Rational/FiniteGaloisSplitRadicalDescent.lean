import Langlands.GroupScheme.Rational.FiniteGaloisSplitUnipotentDescent
import Langlands.GroupScheme.Rational.TorusQuotientRadicalDescent

/-! # Split series on actual finite-Galois descended radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

include hstable

/-- A represented ground-field radical that becomes split over a finite Galois
extension is split, using the explicit stable-vector premise. -/
theorem IsUnipotentRadical.isSplitUnipotent_of_finiteGalois
    {U : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}
    (hi : IsUnipotentRadical i)
    (hsplit : RelativeRoot.IsSplitUnipotent
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj U)) :
    RelativeRoot.IsSplitUnipotent U := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hi.smooth
  let : ConnectedSpace U.X.left := hi.connectedSpace
  exact RelativeRoot.IsSplitUnipotent.of_finiteGalois_of_stableVector
    hstable L U hi.isUnipotent hsplit

/-- Descend a supplied split radical, retaining its exact inclusion comparison
and both ground-field radical predicates. -/
def IsUnipotentRadical.finiteGaloisSplitRadical
    {U : GroupScheme (Spec (CommRingCat.of L))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}
    (hi : IsUnipotentRadical i) (hsplit : RelativeRoot.IsSplitUnipotent U) :
    Σ U₀ : GroupScheme (Spec (CommRingCat.of k)),
      Σ j : U₀ ⟶ G,
        {e : (GroupScheme.baseChange (algebraBaseMap k L)).obj U₀ ≅ U //
          IsUnipotentRadical j ∧ IsSplitUnipotentRadical j ∧
            (GroupScheme.baseChange (algebraBaseMap k L)).map j = e.hom ≫ i} := by
  obtain ⟨U₀, j, e, hj, he⟩ := hi.finiteGaloisRadical
  have hsL : RelativeRoot.IsSplitUnipotent
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj U₀) :=
    hsplit.of_iso e.symm
  have hs₀ := hj.isSplitUnipotent_of_finiteGalois hstable hsL
  exact ⟨U₀, j, e, hj, hj.isSplitUnipotentRadical hs₀, he⟩

/-- Splitness attaches to the very same radical retained by actual torus-quotient
descent; it does not require a new choice of kernel or quotient. -/
theorem FiniteGaloisTorusQuotientDescent.isSplitUnipotent
    {U D : GroupScheme (Spec (CommRingCat.of L))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}
    {q : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶ D}
    (d : FiniteGaloisTorusQuotientDescent i q)
    (hsplit : RelativeRoot.IsSplitUnipotent U) :
    RelativeRoot.IsSplitUnipotent d.radical :=
  d.isGeometricUnipotentRadical.1.isSplitUnipotent_of_finiteGalois hstable
    (hsplit.of_iso d.sourceIso.symm)

/-- An actual finite-Galois torus-quotient descent, enhanced with splitness of its
own geometric radical, conditional on the stated stable-vector theorem. -/
def finiteGaloisSplitTorusQuotientDescent
    [Smooth G.X.hom]
    {U D : GroupScheme (Spec (CommRingCat.of L))}
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hsplit : RelativeRoot.IsSplitUnipotent U)
    (q : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsTorus D) :
    {d : FiniteGaloisTorusQuotientDescent i q //
      RelativeRoot.IsSplitUnipotent d.radical} :=
  let d := finiteGaloisTorusQuotientDescent i hi hs hc hu q hq hD
  ⟨d, d.isSplitUnipotent hstable hsplit⟩

end Langlands.GroupScheme
