# Central isogenies induce morphisms of the supplied root data

Authors: Worker 1375 and Worker 1283.

`Langlands.GroupScheme.centralIsogenyRootDatumHom` proves exactly the published
`Langlands.GroupScheme.CentralIsogenyRootDatumHomStatement.{u}` from
[`SplitRootDatumStatement`](SplitRootDatumStatement.md). The universe and field
are arbitrary. The theorem applies to the actual connected reductive groups,
split maximal tori, central isogeny, commuting torus restriction and supplied
root data quantified in that statement. It adds no hypotheses. In particular,
the full scheme-theoretic kernel may be nonsmooth or inseparable.

## Implemented assembly and kernel containment

The Lean proof applies
`centralIsogenyRootDatumHom_of_kernel_containment` from
[`RootDatumHomConstruction`](RootDatumHomConstruction.md). This published
reduction assembles the complete conclusion once every relevant full central
kernel is contained in the source maximal torus.

For that remaining premise, `IsCentralIsogeny.kernel_range_le_center` puts
`SubgroupFunctor.range (kernelι φ)` in `center G`.
`center_le_torusCentralizer i` puts the center in `torusCentralizer i`.
The published theorem `maximalTorusCentralizer`, from
[`Absolute.MaximalTorusCentralizerProof`](../Absolute/MaximalTorusCentralizerProof.md),
identifies this centralizer with `SubgroupFunctor.range i` for the connected
reductive source and its maximal torus. Rewriting by that equality and composing
the two inclusions proves the required containment on every test scheme. The
argument uses the full kernel throughout.

## Root and coroot comparison used by the reduction

The reduction first proves that the supplied torus restriction `t` is an
isogeny, using `IsCentralIsogeny.isIsogeny_torusRestriction` and the published
maximality theorem for images of split maximal tori.

The construction's root comparison uses the published nonzero-weight
differential equivalence. A descended commutator gives an adjoint difference
in the differential image over every coefficient algebra. Evaluation at the
universal split-torus point and extraction of a nonzero monomial coefficient
give a preimage in the corresponding weight space. Centrality of the kernel
gives injectivity there. Consequently `roots (i ≫ φ) = roots i`.
The weight restriction formula and injectivity of character pullback give a
bijection from the roots for `i'` to those for `i`. The two `IsRootDatumOf`
hypotheses identify these sets with the root ranges of the supplied `P'` and
`P`, yielding the root index equivalence.

For coroots, `IsRootDatumOf` realizes each supplied reflection by an actual
normalizing point. Its image under `φ` gives the reflection associated with
the pushed source coroot. The full target Weyl image is finite by
`splitTorusWeylImageFinite`. The published
`IsRootDatumOf.coroot_comp_of_finite_weylImage` compares that reflection with
the supplied target reflection: finite order of their product identifies the
corresponding integral functionals, and perfectness identifies the coroots.
This comparison concerns the specific supplied data and the entire character
lattice, including central directions.

`RootDatumHom.ofRootCoroot` assembles a Mathlib `RootPairing.Hom P' P`.
Its weight map is `χ ↦ t ≫ χ`, and its coweight map is `ν ↦ ν ≫ t`;
the transpose law follows from associativity of composition for the actual
lattice pairings. These formulas are definitional in the construction.
The flat surjective torus restriction is an epimorphism, giving injectivity
of the weight map. Its finiteness gives injectivity of the coweight map by
`cocharacterMapInt_injective_of_isFinite`.

## Isomorphism criterion

For split tori, character pullback is bijective exactly when `t` is an
isomorphism. If `φ` is an isomorphism, maximality of the source torus and
closedness of the target torus make `t` an isomorphism. Conversely, when `t`
is an isomorphism, the full-kernel containment proved above makes `φ` monic
on every test scheme, by
`IsIsogeny.isIso_of_kernel_range_le_of_restriction`. Its finite flat
surjectivity then makes it an isomorphism. This proves precisely
`IsIso φ ↔ Function.Bijective f.weightMap`.

## Sources and provenance

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`:

- Definition 6.6, printed p.126 (one-based PDF p.142), defines isogenies by
  finite kernel and image of finite index. The finite surjective map in
  `IsCentralIsogeny` has this property.
- Definition 23.1, printed p.483 (PDF p.499), defines an isogeny of root
  data by character and transpose maps and corresponding roots and coroots.
- The paragraph following it and Definition 23.2, printed p.484
  (PDF p.500), relate the two injectivity claims to finite cokernel and
  specify the unscaled root and coroot equations for the central case.
- The discussion of isogenies of split reductive groups and Proposition
  23.5 with its proof, printed pp.485–486 (PDF pp.501–502), give the
  induced maps and the isomorphism criterion.
- Corollary 17.84, printed p.379 (PDF p.395), supplies the maximal-torus
  self-centralizer result used to place the full central kernel in `T`.

The Lean route is a derived composition of the cited Library proofs.
Milne's Proposition 23.5 compares root subgroups and their monomial maps;
the implemented central-case root comparison instead uses the commutator
and nonzero-weight coefficient argument. The supplied coroot comparison uses
finite-order reflections in the full Weyl image. The final kernel and torus
isomorphism argument implements the last paragraph of Milne's proof with
subgroup functors on all test schemes. Smoothness of the ambient groups comes
from reductivity; smoothness or separability of the isogeny is never assumed.
The registered 2026-11-02 snapshot of Milne's 2017 errata has no correction
for the passages cited here.
