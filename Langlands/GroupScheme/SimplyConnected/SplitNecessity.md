# Proof: simple connectedness forces integral coroot generation

Author: Worker 4342.

This module proves the published proposition
`Langlands.GroupScheme.SplitSimplyConnectedCorootSpanStatement`
([`SplitNecessityStatement`](SplitNecessityStatement.md)) at its original
universe `u`:

```
theorem splitSimplyConnectedCorootSpan :
    SplitSimplyConnectedCorootSpanStatement.{u}
```

Let `k : Type u` be any field. Let `G` be a group scheme over `Spec k` with
`IsSimplyConnected G`. Let `i : T.toGrp ⟶ G` be a maximal torus with `T`
split. Let `P` be a root datum on `characterLattice T` and
`cocharacterLattice T` with `IsRootDatumOf i P`, a finite root index type and
`P.IsReduced`. Then the theorem gives `P.corootSpan ℤ = ⊤`: the integral
coroots span the whole cocharacter lattice. This is integral generation, which
is stronger than generation over `ℚ` or finite index. The theorem adds no
hypotheses. The field may be imperfect and of any characteristic. The proof
does not change the statement's Lean/Markdown pair or any module that pair
imports.

## Implemented proof

The proof is one application of the published conditional assembly
`splitSimplyConnectedCorootSpan_of_inputs` from
[`SplitNecessityAssembly`](SplitNecessityAssembly.md). That theorem derives the
target from `SplitSimplyConnectedCorootSpanInputsStatement.{u}`. This input is
the conjunction of three propositions, all stated in module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`. Each is now a
published theorem, and the proof passes in the anonymous triple:

- `splitReductiveExistence : SplitReductiveExistenceStatement.{u}`, from
  [`Reductive.SplitExistence`](../Reductive/SplitExistence.md). This is the
  Existence Theorem (Milne Theorem 23.55). Over any field, every reduced root
  datum with a finite index type on a finitely generated lattice is isomorphic,
  as a root pairing, to a root datum of a split maximal torus of a connected
  reductive group.
- `splitCentralIsogenyExistence : SplitCentralIsogenyExistenceStatement.{u}`,
  from
  [`Reductive.SplitCentralIsogenyExistenceProof`](../Reductive/SplitCentralIsogenyExistenceProof.md).
  This is the central case of the Isogeny Theorem (Milne Theorem 23.9). A
  morphism of root data of split maximal tori with injective weight and
  coweight maps comes from a central isogeny `φ` and a torus map `t` with
  `iC ≫ φ = t ≫ i`. The weight map is pullback of characters along `t`.
- `splitSemisimpleRootDatum : SplitSemisimpleRootDatumStatement.{u}`, from
  [`Reductive.SplitSemisimplicity`](../Reductive/SplitSemisimplicity.md). This
  is Milne Proposition 21.48 and its coroot form. A split connected reductive
  group is semisimple exactly when its roots span a subgroup of finite index,
  and exactly when its coroots do.

The assembly runs the converse half of Milne Proposition 23.59. Its Markdown
gives the details:

1. `G` is semisimple, so the coroot form of the semisimplicity criterion makes
   `cocharacterLattice T ⧸ P.corootSpan ℤ` finite.
2. The public construction `SimplyConnectedRootDatum.rootDatum P` is the root
   datum `(Hom(ℤΦ^∨, ℤ), Φ, ℤΦ^∨, Φ^∨)`. The Existence Theorem realizes it as a
   root datum `Q` of a split maximal torus `iC : TC ⟶ C` of a connected
   reductive group `C`, through an isomorphism `e`.
3. Restricting characters to the coroot lattice and including the coroot
   lattice into `Y = cocharacterLattice T`, composed with `e`, gives a morphism
   `f : P → Q`. Its weight map is injective by step 1, and its coweight map is
   injective.
4. The Isogeny Theorem gives a central isogeny `φ : C ⟶ G` and a torus map
   `t : TC ⟶ T` with `iC ≫ φ = t ≫ i`.
5. The coroots of `Q` span its whole cocharacter lattice, so `C` is
   semisimple by the semisimplicity criterion.
6. `G` is simply connected, so `φ` is an isomorphism, and then so is `t`.
7. The coweight map of `f` is therefore surjective. It factors through the
   inclusion `(P.corootSpan ℤ).subtype`, so that inclusion is surjective, which
   gives `P.corootSpan ℤ = ⊤`.

`lean_check` builds the module with no errors or warnings. The theorem depends
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Independence of the inputs

The three input theorems take no hypotheses, so they cannot use this
necessity result or any downstream result built on it. In particular they do
not use the theorem that algebraic simple connectedness is preserved by
arbitrary field extension (`IsSimplyConnectedFieldExtensionStatement`), whose
reductions take this necessity statement as a premise. The import closure of
this module contains no `SimplyConnected` field-extension, cover-existence or
sufficiency-criterion module. The assembly uses neither the separate
sufficiency direction `SplitCorootSpanSimplyConnectedStatement` nor
simply connected cover existence.

## Provenance

The statement is the necessity half of the integral coroot criterion, split
case: J. S. Milne, *Algebraic Groups* (2017), Proposition 23.59 (printed
p.502, PDF p.518), source `milne-2017-algebraic-groups`. Milne gives the
direction "simply connected implies `X = P(Φ)`" by contraposition through
Corollary 23.56. The assembly instead shows directly that the torus map of
the central isogeny is an isomorphism, and states the conclusion in the coroot
form `P.corootSpan ℤ = ⊤`. The Lean proof in this module only combines the four
published results above.
