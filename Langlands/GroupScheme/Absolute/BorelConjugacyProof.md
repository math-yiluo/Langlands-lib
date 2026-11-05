# Existence and conjugacy of Borel subgroups

Worker 1293.

`Langlands.GroupScheme.borelConjugacy.{u}` proves exactly the unchanged
`BorelConjugacyStatement.{u}`. For every algebraically closed field
`k : Type u` and every smooth affine group scheme `G` over `Spec k` with
connected underlying space, it gives an actual Borel embedding and conjugates
any two actual Borel embeddings by a point of `G(k)`, together with an actual
isomorphism of their source group schemes. No characteristic, reductivity or
splitting hypothesis is added.

## Implemented proof

The proof first applies the published `someBorelQuotientProper` to choose a
Borel embedding `j : C ⟶ G`. Its properness conclusion concerns every supplied
quotient model satisfying the stated geometric and all-test fiber hypotheses;
it chooses `C` before choosing the model. The theorem
`smoothSubgroupQuotientExistence` then constructs an actual quotient
`q : G.X ⟶ Q`, with separated, locally finite type and quasi-compact structural
map, smooth surjective quasi-compact projection, and exact left-coset fibers
on all relative scheme tests. The properness conclusion makes this `Q` proper.
The embedding `j` supplies the existence component of the target.

`Dynamic.flagQuotientSchemeAction` equips that same `Q` with the descended
left action of `G`. The image of the identity point of `G` gives a rational
point of `Q` and hence its underlying nonemptiness.

For any other Borel embedding `l : D ⟶ G`, the Borel predicate gives
smoothness, connectedness and solvability of `D`. Its closed immersion into
the affine `G` makes its structural map affine. Apply the proved
`solvableProperFixedPoint` to the actual action restricted along `l`.
It gives a rational point fixed on every relative test and refinement.
The published `IsBorelSubgroup.conjugatingDataOfFixedPoint` lifts that point
through `q` and constructs actual conjugating data from `l` to `j`.
Its factorization uses the exact all-test fiber condition, and Borel
maximality makes the resulting factor an isomorphism. The constructor
returns the inverse of the chosen rational lift to match the target's
inner-automorphism convention.

Apply this construction to both supplied embeddings `i : B ⟶ G` and
`i' : B' ⟶ G`, obtaining points `g, g'` and isomorphisms `φ : B ≅ C`,
`φ' : B' ≅ C`. The published `conjugatingDataOfCommonTarget` gives the point
`g'⁻¹ * g`, the isomorphism `φ ≪≫ φ'.symm`, and the exact equation

```text
i ≫ (G.innerIso (g'⁻¹ * g)).hom = (φ ≪≫ φ'.symm).hom ≫ i'.
```

These are the witnesses required by the unchanged existential conclusion.

## Sources and provenance

The original source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Theorem 17.9, printed p.354 / one-based PDF p.370.
Worker 1293 read that theorem and its proof, together with Corollary 17.3,
printed p.353 / PDF p.369. The complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to either
result. The source's conjugacy argument is the same proper-quotient
fixed-point argument used here.

For properness, this proof reuses Workers 1396 and 1399's exact general
`someBorelQuotientProper` theorem. Its published reduction begins with Borel
existence, embeds the arbitrary affine group in a general linear group,
chooses a closed orbit in the proper full flag scheme with solvable point
stabilizers, and applies the general fixed-point theorem to the Borel.
Maximality identifies the Borel with the reduced identity component of the
stabilizer. Finite-index quotient properness transfer applies to the supplied
quotient model. This differs from Milne's initial maximal-dimension and
Chevalley line-stabilizer construction; the general ambient group is retained
throughout. The full flag result supplies only one geometric input to this
general reduction.

The general fixed-point theorem is also an imported exact proof. Its route
uses the represented split-solvability comparison over an algebraically
closed field, properness-to-pseudo-completeness, existence of a rational
section, and the split-solvable fixed-point theorem corresponding to
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition C.1.5. Its own explanation documents that alternate route.
No fixed point, quotient properness or Borel conjugacy is assumed here.

The assembly and quotient-action/fixed-point conjugacy adapters were written
by Worker 1293. The common-target conjugacy composition was designed by
Worker 1293 and implemented by Worker 135. The proof imports the independently
published prerequisites by their Lean names and changes no statement pair.
