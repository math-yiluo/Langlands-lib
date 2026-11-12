# Proof: big-cell and Steinberg data for simply connected groups

Author: Worker 4716.

This module proves the published proposition
`Langlands.GroupScheme.SteinbergBigCellStatement`
([`SteinbergBigCellStatement`](SteinbergBigCellStatement.md)) at its original
universe `u`:

```
theorem steinbergBigCell : SteinbergBigCellStatement.{u}
```

Let `k : Type u` be an algebraically closed field of prime characteristic `p`
and let `G` be a group scheme over `Spec k` with affine structure morphism that
is simply connected (`IsSimplyConnected`). Then the theorem gives the witnesses
`Λ`, `j : D(Λ) → G`, `H`, `i : H → G`, a rational point `n`, a coordinate `χ` of
`H` and a coordinate `d` of `G` that satisfy all seven conditions of the
statement. Conditions 2, 5 and 6 hold on arbitrary relative test schemes over
`Spec k`, including nonaffine, nonreduced and empty ones. In condition 7 the
bases are bases of the entire covariant spaces
`leftCovariantSubspace i (χ ^ e')`. The theorem adds no hypotheses and does not
change the statement's Lean/Markdown pair or any module that pair imports.

## Implemented proof

The proof is one application of the published conditional theorem

```
steinbergBigCell_of_rootAndCoroot
    (hroot : RootDatumExistenceStatement.{u})
    (hcoroot : SplitSimplyConnectedCorootSpanStatement.{u}) :
    SteinbergBigCellStatement.{u}
```

from [`SteinbergBigCellRootCorootAssembly`](SteinbergBigCellRootCorootAssembly.md).
Both antecedents are published theorems without hypotheses, and the proof
passes them in:

- `rootDatumExistence : RootDatumExistenceStatement.{u}`, from
  [`RootDatumExistence`](RootDatumExistence.md). For every field, connected
  reductive `G`, split torus `T` and maximal torus `i : T ⟶ G` it gives a
  finite reduced Mathlib root datum `P` with `IsRootDatumOf i P` (Milne,
  *Algebraic Groups* (2017), Theorem 21.11 and Corollary 21.12).
- `splitSimplyConnectedCorootSpan : SplitSimplyConnectedCorootSpanStatement.{u}`,
  from [`SplitNecessity`](../SimplyConnected/SplitNecessity.md). For a simply
  connected `G`, a split maximal torus and a finite reduced root datum of it,
  the coroots span the whole cocharacter lattice over `ℤ` (Milne 2017,
  Proposition 23.59, necessity, split case).

## The route through the imported assemblies

The imported assemblies were written by other workers; their Markdown gives
the details. Their chain, as used by this proof, is:

1. `steinbergBigCell_of_rootAndCoroot` adds the published highest-weight
   existence theorem `splitDominantHighestWeightRepresentationsExist`
   (`Rational.DominantHighestWeightProof`) to
   `steinbergBigCell_of_structuralInputs`
   ([`SteinbergBigCellStructuralAssembly`](SteinbergBigCellStructuralAssembly.md)).
2. That theorem adds the proved height irreducibility
   `splitSteinbergHeightIrreducibility`, an application of
   `SplitPinning.canonicalRhoSteinbergHeightIrreducibility`, and applies
   `steinbergBigCell_of_inputs`
   ([`SteinbergBigCellHostAssembly`](SteinbergBigCellHostAssembly.md)).
3. For the given `k`, `p` and `G`, `steinbergBigCellDataOfInputs` obtains a
   split maximal torus of `G` from the published
   `exists_isMaximalTorus_isSplitTorus_of_isSepClosed`. It builds a split
   pinning with `SplitPinning.ofRootDatumExistence` from the root-datum input
   and the root-line trivializations of `splitRootLieLine`. It obtains
   integral coroot span from the coroot input and the given simple
   connectedness. It then constructs `SteinbergBigCellData G` with
   `canonicalRhoSteinbergBigCellData`
   ([`CanonicalRhoSteinbergAssembly`](CanonicalRhoSteinbergAssembly.md)).
4. `SteinbergBigCellData.exists_data`
   ([`SteinbergBigCellData`](SteinbergBigCellData.md)) unpacks these data into
   the existential conclusion of the statement.

The witnesses of the constructed data are those that the statement's Markdown
describes as intended. `j` is the diagonalizable presentation of the split
maximal torus. `i` is the inclusion of the dynamic parabolic of the
polarization of the integral Weyl vector `ρ`, which
`IsRootDatumOf.isBorelPair_polarization_rho` proves to be a Borel subgroup
containing the torus. `n` is the constructed rational opposition
representative. `χ` is the canonical extended negative-`ρ` coordinate. `d` is a
distinguished matrix coefficient of the conjugated dual of a highest-weight
representation at `ρ`. The six geometric laws come from
`canonicalRhoBorelBigCellData`, which uses the published
`regularCocharacterBorel` and `absoluteBruhatCovering` proofs. The seventh law
uses the Steinberg heights `p ^ r - 1` and the proved irreducibility of the
right regular representation on the whole canonical covariant space at those
heights ([`CanonicalRhoSteinbergAssembly`](CanonicalRhoSteinbergAssembly.md),
[`SteinbergBigCellStructuralAssembly`](SteinbergBigCellStructuralAssembly.md)).

`lean_check` builds the module with no errors or warnings. The theorem depends
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Independence of the inputs

The theorems `rootDatumExistence` and `splitSimplyConnectedCorootSpan` take no
hypotheses, so they do not rest on this statement or on anything derived from
it. No maximal torus, Borel subgroup, Weyl representative, root datum,
highest-weight module, Steinberg irreducibility or big-cell decomposition
enters as an assumption: each is supplied by a published Library proof inside
the imported chain.

## Provenance

The statement is an internal interface for the proof sketch of Theorem A.1.0,
(a) implies (b), in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third enlarged edition (1994), Appendix to Chapter 1, Section A, printed p.192,
registered as `mumford-fogarty-kirwan-1994-git-3rd`. That page cites Steinberg,
*Representations of algebraic groups* (1963), registered as
`steinberg-1963-representations-algebraic-groups`, for the irreducibility of
`H⁰(G/B, L(mρ))` at `m = p^s - 1`. The Lean proof in this module only combines
the three published results named above; the imported chain derives the
Steinberg irreducibility through Frobenius dimension bounds rather than
following Steinberg's argument.
