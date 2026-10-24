# Coherence proofs for multiplicative Tate base change

The theorem
`Langlands.GroupScheme.Gm.TateComparison.multiplicativeBaseChangeCoherence`
proves the exact proposition
`Langlands.GroupScheme.Gm.TateComparison.MultiplicativeBaseChangeCoherence`
from `MultiplicativeBaseChangeCoherenceStatement`. It proves identity and
composition coherence for the five existing canonical multiplicative Tate
comparisons: finite torsion sections, selected integral inverse limits,
prime-adic integral modules, selected rational modules, and prime-adic rational
modules. All schemes and test schemes lie in one arbitrary universe.

The target retains all its quantifiers. Finite orders are arbitrary natural
numbers, including zero. The selected constructions allow any predicate
`P : ℕ → Prop` on the positive orders; the full and away cases are its usual
specializations. Both prime-adic constructions require `Fact p.Prime`. The
selected rational construction tensors with `ℚ` over `ℤ`; the prime-adic
rational construction tensors with `ℚ_[p]` over `ℤ_[p]`.

## The canonical target identifications

For each of the five comparisons, write `B_b,T` for base change along
`b : S' ⟶ S` at `T : Over S'`, and `R_a` for its contravariant test restriction.
The identity equation is

```text
B_id,T(x) = R_((Over.mapId S).hom.app T)(x).
```

For `c : S'' ⟶ S'` followed by `b : S' ⟶ S`, the composition equation is

```text
B_(c≫b),T(x) =
  R_((Over.mapComp c b).hom.app T)(B_b,(Over.map c).obj T(B_c,T(x))).
```

The restriction arrows align the direct and iterated test objects. Their
underlying scheme morphisms are identities. The proof preserves these arrows
explicitly and does not replace the target by equations with silently identified
test objects.

## Implemented proof

The private helper `levelEquiv_levelRestrict` specializes the existing
`levelEquiv_restrict` identity to the actual `Tate.Level` carrier. It identifies
test restriction in root coordinates with the root map induced by the map on
global sections of the underlying test-scheme morphism.

`levelBaseChangeIdentity` and `levelBaseChangeComposition` apply injectivity of
the finite root-coordinate equivalence `levelEquiv`. The existing
`levelEquiv_levelBaseChange` formula removes each canonical base-change map in
these coordinates; the helper rewrites test restriction. The identities for
the underlying morphisms of `Over.mapId` and `Over.mapComp`, together with
`Scheme.Hom.id_appTop`, reduce the remaining root map to the identity. In the
composition proof, `Functor.comp_obj` first aligns the iterated test object so
both nested base-change formulas apply. The resulting root-coordinate
equalities are reflexive.

`integralBaseChangeIdentity` and `integralBaseChangeComposition` use subtype
extensionality and function extensionality on the coherent family. At the
coordinate indexed by a selected positive order `n`, their goals are exactly
the corresponding finite laws at `n.val`. The two prime integral theorems use
the same argument at order `p ^ n`. Thus the coherent-limit proofs use the
actual finite comparisons at every coordinate, with no finiteness, rank or
surjectivity hypothesis.

`rationalBaseChangeIdentity` and `rationalBaseChangeComposition` use tensor
induction over `ℤ`. On a pure tensor, the existing formulas for
`rationalBaseChange` and `Tate.rationalTestRestrict` leave the rational scalar
unchanged and reduce the equality to the respective selected integral law.
The additive cases follow by the additive-map identities and the induction
hypotheses.

For `primeRationalBaseChangeIdentity` and
`primeRationalBaseChangeComposition`, the proof first establishes equality of
the corresponding `ℚ_[p]`-linear maps. It uses
`TensorProduct.AlgebraTensorModule.ext` on pure tensors over `ℤ_[p]`; each
remaining equality is precisely the relevant prime integral law with the same
scalar tensor factor. `LinearMap.congr_fun` then evaluates this equality at the
arbitrary input. In the composition case the compared map is the composite of
the two base-change maps followed by test restriction.

The final theorem conjoins these ten results in the exact published order:
identity then composition, successively for finite, selected integral, prime
integral, selected rational and prime rational objects.

## Provenance and scope

This is an internal proof of the named coherence statement, using the concrete
root-coordinate formulas, inverse-limit definitions and scalar extensions of
the imported multiplicative Tate constructions. It cites no external theorem
as a substitute for the implemented proof. No roots, basis, arbitrary
comparison equivalence or Tate-twist trivialization are supplied as hypotheses.
It adds no hypotheses to the target and changes neither the target nor its
imported definitions.

The conclusion consists of the ten specified equalities. It makes no further
claim about finite-adelic bundled maps, rational topologies, finite étaleness,
monodromy pullback, pairings, restricted products, or completion of the parent
PEL construction.
