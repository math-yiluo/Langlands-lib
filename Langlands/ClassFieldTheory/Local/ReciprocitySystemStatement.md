# Actual local reciprocity systems in a common algebraic closure

Worker 10 authors the theorem-statement specialization. Worker 21 contributed
the uniqueness argument described below and authored the separately published
interface. These are proposition definitions, not proofs of local class field
theory. No reciprocity family or desired isomorphism is an input to the
existence target.

## The actual specialization

Every prime `p`, every `F : PadicField.{u} p`, and every
`T : F.TopologicalData` are quantified. The carrier universe is unrestricted.
The base datum `T` supplies the residue cardinality in normalization. Every
field has the published `F.canonicalTopologicalData`, so the quantification
has its required all-fields realization.

The family of extension fields is the published
`FiniteIntermediateExtension F.Carrier`: all finite intermediate fields in
the actual `AlgebraicClosure F.Carrier`, including nonnormal ones. The
extension-field data is `CommonClosure.canonicalData F`, constructed from
the canonical realization of each actual `E.asPadicField`. It is not a
hypothesis that these data or a reciprocity family exist. This uses a
specified realization of every field rather than asserting a comparison
between arbitrary supplied extension-field topologies. The theorem covers
all the finite intermediate fields of the chosen closure. Transport to a
separately presented field or another closure is a separate construction.

The degree map is exactly `Weil.Local.localResidueDegree F`. It is the
published actual absolute residue action, followed by the finite-field
comparison that assigns degree positive one to geometric Frobenius.
It is not an arbitrary map `phi` satisfying a desired conclusion. The source
at `E` is the topological abelianization of the actual preimage of
`E.field.fixingSubgroup` in the local Weil pullback. The target is `E.field`
units with the canonical local topology.

## Meaning of the two statements

`CommonClosureReciprocityExistence` asserts that there is a family of
continuous group isomorphisms `e_E : W_E^ab -> E^x` satisfying all six
conditions of `CommonClosure.NormalizedSystemRelation`:

1. For every inclusion `E <= L`, the actual Weil subgroup inclusion on
   abelianizations corresponds to the determinant field norm `L^x -> E^x`.
2. For that inclusion, the actual finite-index transfer in the opposite
   direction corresponds to the field inclusion `E^x -> L^x`.
3. Conjugation by every actual Weil element with projection `sigma`
   corresponds to the field isomorphism `E -> sigma(E)`.
4. Each induced homomorphism `g_E : E^x -> G_E^ab` has dense range.
5. For each `E`, an isomorphism from its actual open-finite-quotient
   multiplicative completion to the actual Galois abelianization exists,
   and its composite with the completion map is `g_E`.
6. For every abelianized Weil element `w` over `E`,
   `|e_E(w)|_E = q_F^(-degree_F(w))`.

The maps in conditions 1-3 are the existing constructions on actual fields
and subgroups. Transfer is fixed by its coset-product construction. The
completion has a different carrier from `E^x`. All six conditions are in the
existential conclusion; none is supplied as a premise.

The degree in condition 6 is the degree over the base field `F`, not the
renormalized degree over `E`. A uniformizer of `E` has absolute value
`q_E^(-1) = q_F^(-f(E/F))`; its inverse image therefore has base degree
`f(E/F)`, giving geometric Frobenius of `E`. Allowing arbitrary base `T`
uses the intrinsic equality of residue cardinalities of compatible local
realizations. It introduces no additional realization assumption.

`CommonClosureReciprocityUniqueness` says that any two families satisfying
that relation are equal, as families of the specified continuous
isomorphisms. This includes every nonnormal intermediate field, although the
finite quotient argument at each component uses abelian extensions of that
field. A candidate family occurs only under the universal quantifiers in
this uniqueness assertion. The conjunction
`CommonClosureReciprocityTheorems` pairs it with unconditional existence.
The inverse of an isomorphism has values in an abelianized Weil group,
never in a chosen lift to a nonabelian group.

## Source correspondence and derived uniqueness

John Tate, *Number theoretic background*, Corvallis Part II (1979),
Section 1.1, printed pages 3-4 / retained PDF pages 12-13, defines the
family over all finite intermediate fields, its conjugation diagram (W2),
and its transfer diagram (W3), and displays the norm/inclusion diagram
following (W4). Section 1.4.1, printed page 6 / PDF15, constructs the
nonarchimedean Weil group as the integer-Frobenius subgroup and specifies
geometric reciprocity. Section 1.4.6, printed page 7 / PDF16, identifies
the norm and explains its restriction to each extension Weil subgroup.
Our isomorphisms are in the inverse direction to Tate's `r_E`.
Worker 10 read those original pages, including the surrounding existence
and uniqueness discussion on printed pages 5-7 / PDF14-16.

Jean-Pierre Serre, *Local Fields*, GTM 67 (1979), XI.3-5, printed pages
169-175 / PDF175-181, gives finite norm-residue reciprocity, the norm,
transfer and conjugation diagrams, their passage to the limit, and the
completion by norm subgroups. XIII.4, printed pages 196-198 / PDF201-203,
specializes to local fields and gives the unramified normalization.
XIV.6, printed pages 218-219 / PDF223-224, identifies norm subgroups with
open finite-index subgroups and proves that their intersection is trivial.
Worker 10 read these original passages. Serre's arithmetic normalization
is inverted here; kernels and compatibility diagrams are preserved.

Existence is the local Weil form of these results applied simultaneously
in the chosen closure. The pullback presentation is the existing model of
the integer-Frobenius subgroup, with its actual topology. The completion
condition is the local completion result. It does not assert that the
noncompact Weil group itself is the profinite Galois group.

Uniqueness of the exact displayed relation is a derived formulation; the
following argument explains its strength without inserting a finite
norm-kernel certificate into the target. It is not implemented in Lean.
Worker 21 supplied this argument, and Worker 10 checked its mathematical
steps against the definitions and the cited reciprocity properties.

Fix a component at `E` and write `g_E` for its induced Galois homomorphism.
For an abelian finite extension `M/E` in the same closure, the kernel of
`W_E^ab -> Gal(M/E)` is the image of `W_M^ab`. Indeed, `W_M` is the
preimage of the fixing subgroup, contains the closed commutator subgroup
of `W_E`, and is closed because it has finite index. The quotient maps are
surjective. The norm diagram and surjectivity of `e_M` therefore identify
the kernel of `E^x -> Gal(M/E)` with the actual norm subgroup.

Normalization makes `g_E(pi)` restrict to geometric Frobenius on every
unramified extension, for each uniformizer `pi` of `E`. Let `L/E` be
finite abelian, put `n = [L:E]`, let `E_n/E` be unramified of degree `n`,
and put `L' = L E_n`. The restriction `sigma` of `g_E(pi)` to `L'` has
order `n`: its order on `L` divides `n` and its order on `E_n` is `n`.
Let `M` be its fixed field. The norm-kernel property makes `pi` a norm
from `M`. The valuation of a norm is multiplied by the residue degree,
so `M/E` is totally ramified. Thus `M` and `E_n` intersect in `E`, and
degree counting gives `L' = M E_n`. For a second normalized family,
`g'_E(pi)` fixes `M` by the same norm kernel and agrees with `g_E(pi)`
on `E_n` by normalization. It therefore agrees on `L`, for every finite
abelian `L/E`. Uniformizers generate `E^x` (each unit is the ratio of two
uniformizers), so the two Galois homomorphisms agree.

Finally, the actual completion map of `E^x` is injective: its open
finite-index subgroups separate points. Explicitly, for a uniformizer
`pi`, the groups generated by `pi^m` and principal units `U^n`, as
positive integers `m,n` vary, have trivial intersection. The completion
comparison then makes `g_E` injective; since `e_E` is bijective, the
projection `W_E^ab -> G_E^ab` is injective as well. Equality of the two
Galois homomorphisms gives equality of the two inverse Weil maps, hence
of the candidates. This works at each finite `E`, proving equality of
families. No existence theorem for the very family being compared is
used as a premise in this uniqueness argument.

Registered original files:

- `tate-1979-number-theoretic-background`,
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `serre-1979-local-fields`,
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`,
  SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

No source-specific errata file was present at preparation.

## Dependencies and status

The only direct imports are the published `ReciprocitySystem` and actual
`Weil.Local.Assembly`. The former supplies every family, group, map,
normalization relation and canonical extension realization used here.
The latter supplies the actual geometric residue degree. No shared draft
or unproved substitute for the residue construction is imported.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation and exact inspection of
`CommonClosureReciprocityTheorems` succeeded with zero errors or warnings
and confirmed that it returns `Prop`. Independent semantic review,
publication, and a later proof task remain separate requirements.
