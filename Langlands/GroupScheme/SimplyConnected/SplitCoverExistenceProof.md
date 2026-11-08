# Proof: simply connected central covers of split semisimple groups

Author: Worker 1238.

This module proves the published proposition
`Langlands.GroupScheme.SplitSimplyConnectedCoverExistenceStatement`
([`SplitCoverExistenceStatement`](SplitCoverExistenceStatement.md)) at its
original universe `u`:

```
theorem splitSimplyConnectedCoverExistence :
    SplitSimplyConnectedCoverExistenceStatement.{u}
```

So for every field `k : Type u`, every semisimple group scheme `G` over
`Spec k`, and every split commutative torus `T` with a maximal torus
`i : T ⟶ G`, there are an actual group scheme `C` over `Spec k` and an actual
homomorphism `π : C ⟶ G` with `IsSimplyConnected C` and `IsCentralIsogeny π`.
The theorem adds no hypotheses, and it does not change the statement or any
module the statement imports.

## Implemented proof

The proof is one application of the published conditional assembly
`splitSimplyConnectedCoverExistence_of_minimalLattice` from
[`SplitCoverMinimalLattice`](SplitCoverMinimalLattice.md). That theorem derives
the target from three hypotheses. Each is now a published theorem, and the
proof supplies it:

- `rootDatumExistence : RootDatumExistenceStatement.{u}`, from
  [`Reductive.RootDatumExistence`](../Reductive/RootDatumExistence.md): a split
  maximal torus of a connected reductive group over a field has a reduced root
  datum indexed by a finite type (Milne Theorem 21.11 and Corollary 21.12);
- `centralIsogenyRootDatumHom : CentralIsogenyRootDatumHomStatement.{u}`, from
  [`CentralIsogeny.SplitRootDatumProof`](../CentralIsogeny/SplitRootDatumProof.md):
  a central isogeny compatible with split maximal tori gives a morphism of the
  supplied root data, with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`,
  both injective, and the isogeny is an isomorphism exactly when the weight map
  is bijective (central case of Milne Proposition 23.5);
- `semisimplePerfect : SemisimplePerfectStatement.{u}`, from
  [`Derived.SemisimplePerfectProof`](../Derived/SemisimplePerfectProof.md):
  `derivedSubgroup G = ⊤` for every semisimple group over a field (Milne
  Corollary 21.50).

The assembly works as follows (its Markdown has the details). A candidate is a
semisimple group `C` with a central isogeny `π : C ⟶ G` and a split maximal
torus of `C` lying over `T`. Its coweight image is the image of the cocharacter
lattice of that torus in `X_*(T)`. Every coweight image contains the coroot span
of a root datum of `i`, which has finite index because `G` is semisimple. The
assembly picks with `Nat.find` a candidate whose relative index over the coroot
span is least; `(G, 𝟙 G, T, i, 𝟙 T)` shows that candidates exist. For a central
isogeny `f : H ⟶ C` from a semisimple `H`, the split maximal torus lifts to `H`,
and `f ≫ π` is central because `H` is perfect. This gives a new candidate whose
coweight image lies in the old one. Minimality forces the two images to be
equal. Then the coweight map of the root-datum morphism of `f` is bijective,
hence so is its weight map, and `f` is an isomorphism. So the minimal `C` is
simply connected, and its `π` is a central isogeny.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The statement is the split case of Milne, *Algebraic Groups* (2017), Remark
23.60 (printed p.502, PDF p.518), source `milne-2017-algebraic-groups`. Milne
derives it from the Existence and Isogeny Theorems (Theorems 23.55 and 23.9)
by building the cover with root datum `(P(Φ), Φ, Φ^∨)`. The implemented route
does not follow Milne. It is the derived minimal-coweight-lattice argument of
`SplitCoverMinimalLattice`, which uses neither the Existence nor the Isogeny
Theorem. It needs only root-datum existence, the root-datum morphism of a
central isogeny, and perfectness of semisimple groups. The Lean proof here
only combines these four published results.
