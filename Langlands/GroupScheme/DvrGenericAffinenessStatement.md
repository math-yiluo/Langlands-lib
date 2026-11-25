# Raynaud's affineness criterion over a discrete valuation ring

`Langlands.GroupScheme.DvrGenericAffinenessStatement.{u}` is a
proposition definition. For a flat group scheme of finite type over a
discrete valuation ring, with affine generic fibre, it asserts that
affineness is equivalent to separatedness. This module supplies the
statement and contains no proof.

The quantifiers range over every commutative domain `R : Type u` with
`IsDiscreteValuationRing R`, every specified fraction field `K : Type u`
with `Field K`, `Algebra R K` and `IsFractionRing R K`, and every actual
`G : GroupScheme (Spec (CommRingCat.of R))`. Mathlib's DVR convention
excludes fields. All schemes share the arbitrary universe `u`.

The three structural premises are `Flat G.X.hom`,
`LocallyOfFiniteType G.X.hom` and `QuasiCompact G.X.hom`.
The last two say that the actual structural morphism is of finite type.
The generic fibre is the actual group-scheme base change along
`Spec.map (CommRingCat.ofHom (algebraMap R K)) : Spec K → Spec R`.
Its structural morphism is assumed to satisfy `IsAffineHom`.
The conclusion is
`IsAffineHom G.X.hom ↔ IsSeparated G.X.hom`.
Since both bases are affine spectra, relative affineness is equivalent
to affineness of the corresponding total schemes.

No smoothness, connectedness, reductivity, henselianity, completeness or
residue-field condition is imposed. In particular, the generic group is
not assumed to be connected or smooth. The `GroupScheme` abbreviation is
`Grp (Over S)` and carries an actual group law without a commutativity
assumption.

## Source comparison

Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive group schemes*, with an
appendix by Brian Conrad, Proposition 3.1, author-preprint PDF/printed
p.5, including the DVR convention at the beginning of §3.
Registered source `prasad-yu-2006-quasi-reductive-author-preprint`,
SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
file `Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf`.
The retained preprint has 34 pages; its pagination differs from the
published J. Algebraic Geom. 15 (2006), 507–549 version.

Proposition 3.1 concerns a flat finite-type group scheme over the DVR
with affine generic fibre, and gives exactly this equivalence.
Although the preceding definition of a model uses a connected linear
generic group, Proposition 3.1 itself states no such hypothesis.
The Lean proposition retains its stated generality and its separatedness
condition; it does not replace the group scheme by an already affine
integral model. The source attributes the result to Raynaud and provides
a proof using normalization, smoothness after a DVR extension and
affinization. No separate errata note for this source was found in the
Library when checked.

## Consumer and scope

Conrad, *Reductive group schemes* (2014), Theorem 5.3.5, proof on p.166,
uses this result to replace the target by the schematic closure of the
generic image and conclude that the closure is affine.
Registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
That closure is a separated flat finite-type group scheme with affine
generic fibre, so it has exactly the inputs of this statement.
The closure and its group law are constructed in `GenericSubgroupClosure`
(`GenericSubgroupClosure.closureGroup`).
This module proves neither this criterion nor the reductive-monomorphism
closed-immersion theorem.

The Library's `RelativeIdentityComponent.SmoothDvrAffinenessStatement`
has a different scope: it concerns a represented relative identity
component inside an already smooth affine group scheme.
It does not supply affineness for the possibly nonaffine ambient group
scheme of the present criterion.
