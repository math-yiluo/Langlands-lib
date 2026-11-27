import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # A maximal torus split by the cubic field in an anisotropic trialitarian group

This module states, and does not prove, that an anisotropic simply connected group of type
`³D₄` or `⁶D₄` over a totally imaginary number field, split over a cyclic cubic extension,
has a maximal torus defined over the base field and split over that extension
(Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, §6.8, printed p. 372).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `F` be a totally complex number field and `K/F` a Galois extension of degree three. Let
`H` be an anisotropic, simply connected, absolutely almost-simple group over `F` with index data
`d` whose Cartan pairings are those of `CartanMatrix.D 4` under the numbering `q` (vertex `1` is
the centre), such that each of the three leaves is moved by some element of the absolute Galois
group under the star action. If `H` has a split maximal torus after base change to `K`, then `H`
has a maximal torus defined over `F` whose base change to `K` is split. -/
def TrialitarianCubicSplitMaximalTorusStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K], Module.finrank F K = 3 →
    ∀ (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom H.X.hom]
      [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H) (q : d.Vertex ≃ Fin 4),
      IsSimplyConnected H → IsAbsolutelyAlmostSimple H → IsAnisotropic H →
      (∀ a b, d.cartan a b = CartanMatrix.D 4 (q a) (q b)) →
      (∀ a : d.Vertex, q a ≠ 1 →
        ∃ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a ≠ a) →
      (∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
        (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj H),
          IsMaximalTorus s ∧ IsSplitTorus S.toGrp) →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ H),
        IsMaximalTorus t ∧
          IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj T).toGrp

end Langlands.GroupScheme
