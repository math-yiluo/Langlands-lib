# Proof: existence of the root datum of a split maximal torus

Authors: Worker 835, with Worker 1223 (the finite-Weyl-image assembly
`Reductive.RootDatumFiniteWeylAssembly`) and Worker 1283 (the proof of
Weyl-group rationality, `Reductive.SplitWeylRationality`).

This module proves the published proposition
`Langlands.GroupScheme.RootDatumExistenceStatement`
([`Reductive.RootDatumStatement`](RootDatumStatement.md)) at its original
universe `u`:

```
theorem rootDatumExistence : RootDatumExistenceStatement.{u}
```

So for every field `k : Type u`, connected reductive group scheme `G` over
`Spec k`, split commutative torus `T` and maximal torus `i : T ⟶ G`, there are
a finite type `J : Type u` and a reduced Mathlib root datum
`P : RootDatum J X^*(T) X_*(T)` with `IsRootDatumOf i P`. That is:

- the pairing of `P` is the lattice pairing;
- the roots of `P` are exactly the actual roots of `i`;
- every reflection of `P` is the action on characters of conjugation by some
  `k`-point of `G` normalizing `T`.

This is the existence and reducedness part of Milne, *Algebraic Groups*
(2017), Theorem 21.11 and Corollary 21.12.

The module contains two theorems, a conditional step and the final theorem.
It adds no definitions and no axioms. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## The conditional step

```
theorem rootDatumExistence_of_splitWeylRationality
    (hW : SplitMaximalTorusWeylRationalityStatement.{u}) :
    RootDatumExistenceStatement.{u}
```

The hypothesis is the Weyl-group rationality proposition
([`Reductive.SplitWeylRationalityStatement`](SplitWeylRationalityStatement.md),
Milne 2017 Proposition 21.1). Let `T` be a split maximal torus and `K` an
extension field. Then every torus automorphism induced by a `K`-point of the
normalizer comes from a `k`-point of the normalizer.

Fix `k, G, T, i` as above. The proof first installs the instances that the
statements need:

- `hG.isAffineHom` and `hG.smooth` say that `G` is affine and smooth;
- the closed-subgroup component `hi.2.1` of `IsMaximalTorus` makes `i` a
  monomorphism and a closed immersion.

It then combines three results.

1. **Reflection data.** `SplitWeylRationality.reflectionData hW hG hT i hi`
   ([`Reductive.SplitRootReflectionReduction`](SplitRootReflectionReduction.md))
   gives a `k`-point of the normalizer for each actual root `α`. It also gives
   an integral cocharacter `α^∨` with `⟨α, α^∨⟩ = 2` that acts on characters by
   `χ ↦ χ - ⟨χ, α^∨⟩ α`.
2. **Finite Weyl image.** The published `splitTorusWeylImageFinite`
   ([`Torus.WeylImageFinite`](../Torus/WeylImageFinite.md)) says that the
   image of the Weyl action is finite. The proof installs this as an instance.
3. **Reducedness.** The published `rootReducedness`
   ([`Reductive.RootReducednessProof`](RootReducednessProof.md)) says that two
   linearly dependent roots are equal or opposite.

Worker 1223's `exists_rootDatum_of_reflectionData_of_finite_weylImage`
([`Reductive.RootDatumFiniteWeylAssembly`](RootDatumFiniteWeylAssembly.md))
turns these three inputs into a root datum indexed by the finite type of
actual roots. The datum satisfies `IsRootDatumOf i P` and `P.IsReduced`, which
is the required conclusion.

## The final theorem

```
theorem rootDatumExistence : RootDatumExistenceStatement.{u} :=
  rootDatumExistence_of_splitWeylRationality splitMaximalTorusWeylRationality
```

Here `splitMaximalTorusWeylRationality` is Worker 1283's theorem in
[`Reductive.SplitWeylRationality`](SplitWeylRationality.md). It proves
`SplitMaximalTorusWeylRationalityStatement.{u}` with no hypotheses, in three
steps:

- it descends the torus automorphism through its integral coordinates;
- it descends the normalizing point along the fpqc cover `Spec K → Spec k` as
  a transporter, using the split-torus cocycle triviality and
  `maximalTorusCentralizer`;
- it recovers the normalizing equation.

That module's Markdown describes the proof in full.

## Route and provenance

Milne proves Theorem 21.11 with the rank-one group `G_α = C_G(T_α)`, where
`T_α = (ker α)°`. Its Weyl group contains exactly one nontrivial element
`s_α`, represented over `k`, and `s_α` determines the coroot `α^∨`. The Lean
route follows this idea with intrinsic data, as follows.

- The rank-one group is the dynamic centralizer `L` of a generic cocharacter
  annihilating `α`. Over any field, the reduction module shows that `L`
  centralizes the full kernel of `α`. This uses the published root-torus
  generation theorem, the reductivity of dynamic centralizers,
  `maximalTorusCentralizer` and `rootReducedness`.
- Over an algebraic closure, the published Borel-pair construction gives a
  nontrivial Weyl element of `L`. Weyl-group rationality (Milne 21.1) then
  gives a rational one.
- That rational point centralizes the kernel of `α`, and this forces a unique
  integral coroot, `IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer`.

The earlier `Reductive.RootDatumAssembly` needed a spanning premise. The
finiteness of the Weyl image replaces it, so the route does not use the
character–root complement statement. It also does not use the relative
reflection existence statement.
