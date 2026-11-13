# Proof: existence of compatible actual Tits-index data

Author: Worker 148.

This module proves the published proposition
`Langlands.GroupScheme.TitsIndexExistenceStatement`
([`Reductive.TitsIndexChoiceStatement`](TitsIndexChoiceStatement.md)) at its
original universe `u`:

```
theorem titsIndexExistence : TitsIndexExistenceStatement.{u}
```

So let `k : Type u` be any field and `G` an affine group scheme over `Spec k`
that is locally of finite type and semisimple (`IsSemisimple G`). Then there is
a term of `TitsIndexData G` ([`Reductive.TitsIndex`](TitsIndex.md)). Such a term
bundles:

- Galois pinning data over the separable closure `k_s = SeparableClosure k`:
  a `k`-torus `T` with inclusion `i : T ⟶ G`, a realized reduced root datum of
  the split torus `T_{k_s}`, a base of it and a pinning;
- the fact that `i` is a maximal torus over `k`;
- a maximal split torus `j : S ⟶ G` over `k`;
- a torus map `S ⟶ T` through which `j` factors;
- an integral cocharacter `c₀` of `S` that is generic for the relative roots
  of `j`;
- the compatibility condition: every absolute root `a` whose restriction
  `absoluteRootRestriction … a` to `S` is nonzero is positive for the chosen
  base if and only if that restriction pairs positively with `c₀`.

The field, its characteristic and the universe are arbitrary. Characteristic
two and rank zero need no special argument. When `G` has no roots, or when
`S` is trivial, the set `s` that `c₀` must avoid (defined below) is simply
smaller or empty.

The interface comes from Tits, *Classification of algebraic semisimple groups*
(1966), §§2.1–2.3. The Lean proof uses its own route, built only from published
Library theorems. It uses neither `LocalRankOneClassificationStatement` nor any
local Kneser–Tits statement or result.

The module adds one helper lemma and the main theorem. It adds no definitions
and no axioms. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`. The file sets `backward.isDefEq.respectTransparency false`. The
main theorem runs with the finite limit `maxHeartbeats 400000`, because
elaborating the bundled structure needs more than the default limit.

## Helper lemma: pairing of a descended restriction

```
theorem TitsIndexExistence.latticePairing_restriction
    {S T : CommGroupScheme (Spec k)} (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
    (χ : characterLattice T_K) (c₀ : cocharacterLattice S) :
    latticePairing S ((characterLattice.baseChangeEquiv b S hS).symm (f_K ≫ χ)) c₀ =
      latticePairing T_K χ (cocharacterLattice.baseChange b S c₀ ≫ f_K)
```

Here `K` is any field extension of `k`, `b = algebraBaseMap k K`, `T_K` is the
base change of `T` and `f_K` is the base change of `f`.

The statement says that pairing a cocharacter `c₀` of `S` with the descent of
`f_K ≫ χ` gives the same integer as pairing `χ` with the base-changed
cocharacter pushed forward to `T_K`.

Proof. The pairing commutes with base change (`latticePairing_baseChange`,
[`Torus.SplitLatticeBaseChange`](../Torus/SplitLatticeBaseChange.md)), so the
left side equals the pairing over `K` of the base change of the descended
character with the base change of `c₀`. The base change of the descended
character is `f_K ≫ χ` again (`characterLattice.baseChangeEquiv_apply`,
`AddEquiv.apply_symm_apply`). `latticePairing_apply` unfolds both pairings to
the integer exponent of the composite `𝔾_m ⟶ 𝔾_m`. The two composites agree by
associativity.

## Main theorem

Fix `k`, `G` and `hG : IsSemisimple G`. Then `hG.isConnectedReductive` makes
`G` connected reductive, and its `smooth` component provides the `Smooth`
instance.

1. **Maximal split torus.** `exists_maximalSplitTorus G`
   ([`Rational.MinimalPseudoParabolicConjugacyAssembly`](../Rational/MinimalPseudoParabolicConjugacyAssembly.md))
   gives `S` and `j : S ⟶ G` with `hj : IsMaximalSplitTorus j`. Its first
   component gives `hS : IsSplitTorus S.toGrp` and the closed-subgroup property
   `hj.1.2`.

2. **Maximal torus containing it.**
   `EnvelopeInfiniteReduction.exists_isMaximalTorus_factor G j hS.isTorus hj.1.2`
   ([`Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction`](../Rational/TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction.md))
   gives a `k`-torus `T`, a maximal torus `i : T ⟶ G` (`hi`) and a group
   homomorphism `f : S ⟶ T` with `f ≫ i = j` (`hf`). The torus map in the data
   is `Additive.ofMul f`, the commutative-group-scheme morphism with underlying
   homomorphism `f`. Hence the `square` field is exactly `hf`.

3. **Root datum over the separable closure.** Put `K = SeparableClosure k`.
   Three published results give the inputs over `K`:
   - `connectedReductiveFieldExtensionStatement`
     ([`Reductive.FieldExtensionProof`](FieldExtensionProof.md)) gives `hGE`:
     the base change `G_K` is connected reductive.
   - `GaloisPinningData.isSplitTorus_separableClosure T hi.1`
     ([`Reductive.AbsoluteStarAction`](AbsoluteStarAction.md)) gives `hsplit`:
     the torus `T_K` is split.
   - `(maximalTorusBaseChange k K G T i hi.1 hi.2.1).mp hi`
     ([`Torus.MaximalBaseChangeProof`](../Torus/MaximalBaseChangeProof.md))
     gives `hiE`: the base change `i_K` is a maximal torus.

   Then `rootDatumExistence`
   ([`Reductive.RootDatumExistence`](RootDatumExistence.md)) gives a finite
   index type `J`, a root datum `P` on the character and cocharacter lattices
   of `T_K`, `hP : IsRootDatumOf i_K P` and reducedness `hred`.

4. **Generic cocharacter of `S`.** For `a : J`, define the restricted root
   `r a := (characterLattice.baseChangeEquiv b S hS).symm (f_K ≫ P.root a)`.
   This is definitionally `absoluteRootRestriction` for the pinning data built
   below. Let `s` be the union of the relative roots of `j` and the nonzero
   values of `r`. This set is finite: `IsSplitTorus.finite_relativeRoots`
   ([`Rational.RootSupportFiniteness`](../Rational/RootSupportFiniteness.md))
   covers the relative roots and `J` is finite. Every element of `s` is
   nonzero, since relative roots are nonzero by definition.
   `IsSplitTorus.exists_pairings_ne_zero`
   ([`Rational.GenericCocharacter`](../Rational/GenericCocharacter.md)) gives
   `c₀ : cocharacterLattice S` whose pairing with every element of `s` is
   nonzero. In particular `c₀` is generic for `j`, which is the `generic`
   field.

5. **Transfer to `K`.** Put `cK := cocharacterLattice.baseChange b S c₀ ≫ f_K`,
   a cocharacter of `T_K`. The helper lemma and `hP.1` (the pairing of `P` is
   the lattice pairing) give, for every `a`,
   `P.root' a cK = latticePairing S (r a) c₀`.

6. **Regular refinement and base.** `RootDatumCoweightFace.exists_regular_refinement P cK`
   ([`LinearAlgebra.RootDatumCoweightFace`](../../LinearAlgebra/RootDatumCoweightFace.md))
   gives a cocharacter `ν` of `T_K` that pairs nonzero with every root
   (`hν`). For each root that pairs nonzero with `cK`, `ν` gives the same sign
   (`hface`). With the reducedness instance, `B := IsRootDatumOf.regularCocharacterBase k K ν hν`
   ([`Reductive.RegularCocharacterPinning`](RegularCocharacterPinning.md)) is a
   base of `P`. By `regularCocharacterBase_isPos` and `hP.1`,
   `B.IsPos a ↔ 0 < P.root' a ν` for every `a`.

7. **Pinning data.** The `GaloisPinningData k K G` record consists of
   `T, i, hGE, hsplit, hiE, J, P, hP, hred, B` and the pinning
   `RootPinning.ofSplitMaximalTorus hGE hsplit i_K hiE P hP B`
   ([`Reductive.RootPinningFromSplitTorus`](RootPinningFromSplitTorus.md)).

8. **Compatibility.** The remaining fields are `hG`, `hi`, `S`, `j`, `hj`, the
   torus map, `hf`, `c₀` and its genericity. For the `compatible` field, let
   `a` be an absolute root with `r a ≠ 0`. Then `r a ∈ s`, so
   `latticePairing S (r a) c₀ ≠ 0`. By step 5, `P.root' a cK ≠ 0`. Then `hface`
   gives `0 < P.root' a ν ↔ 0 < P.root' a cK`. Combined with step 6 and the
   identity of step 5, this is
   `B.IsPos a ↔ 0 < latticePairing S (r a) c₀`, the required equivalence.
