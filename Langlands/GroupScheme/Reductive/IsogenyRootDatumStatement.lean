import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.LinearAlgebra.RootDatumIsogeny
import Mathlib.Algebra.CharP.Defs

/-! # Statement: the characteristic-power root-datum map of a split group isogeny -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **An isogeny induces an isogeny of root data** (the lattice and centrality assertions
of Milne Proposition 23.5, with Definitions 23.1–23.2). The exponent is the characteristic
exponent of the field. Both lattice maps are the actual maps of the specified torus
homomorphism. The isomorphism criterion includes centrality as well as bijectivity of
the weight map, as required by Definition 23.2. -/
def IsogenyRootDatumStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp),
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (φ : G ⟶ G') (t : T ⟶ T'), IsIsogeny φ →
      i ≫ φ = CommGroupScheme.groupHom t ≫ i' →
    ∀ (J J' : Type u) [Finite J] [Finite J']
      (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
      [P.IsReduced] [P'.IsReduced],
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
        IsIsogeny (CommGroupScheme.groupHom t) ∧
          ∃ f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P,
            (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
            (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) ∧
            (IsCentralIsogeny φ ↔ f.IsCentral) ∧
            (IsIso φ ↔ f.IsCentral ∧ Function.Bijective f.weightMap)

end Langlands.GroupScheme
