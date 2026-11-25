# Split-component chamber comparison

Module
`Langlands.Representation.LanglandsClassification.ParabolicSplitComponentChamberProof`,
namespace `Langlands.GroupScheme`.

The theorem `parabolicSplitComponentChamber.{u}` proves exactly the published
`ParabolicSplitComponentChamberStatement.{u}`. It applies the reduction
`parabolicSplitComponentChamber_of_linearAlgebra` to the published theorems
`parabolicChamberLinearAlgebra`, `standardLeviRealDecomposition`, and
`relativeFundamentalWeight`, so the final theorem has no additional premises.

## Source and scope

The source of the target is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.3.14–V.3.15, printed p.113 / PDF p.119. The original page was read directly.
V.3.14 defines the roots
by restriction and the associated vectors by projection of coroots. V.3.15
defines positive and nonnegative combinations and the pair-inequality chambers,
and gives their fundamental-weight description with a central-character term.
The preceding V.3.13 unprojected-span error, recorded as I4 in the
[Chapter V ledger](../../../notes/renard/item-ledger-v.md), is avoided by the
published projected-root and annihilator definitions.

The scope is exactly the published target in
[ParabolicChamberStatements](ParabolicChamberStatements.md): an arbitrary field,
a connected reductive group, a maximal split torus, a generic cocharacter,
supplied integral reflection data, a subset `J` of the simple roots, a closed
representative of its standard Levi, a split component, and its compatible
factor `f : A → T`. The proof does not assert existence of reflection data or
a choice of compatible presentations for arbitrary parabolics. No reducedness
or nonempty-root condition is imposed.

## Geometric input and restriction

The published `standardLeviCentralDirections` theorem gives a factor of the
given split-component inclusion whose real cocharacter map is injective with
range `rootAnnihilator T J`. The published `eq_of_groupHom_comp_eq` identifies
that factor with `f`, using the monomorphism of the maximal split torus.

Specialize the real decomposition premise at `J = K` to obtain the character
and cocharacter complements. The first transport helper combines the kernel
and surjectivity of character restriction with the character complement. This
gives its bijection from `corootAnnihilator i D J` to `Vstar A`.

## Roots, coroots, and coweights

The ambient chamber premise supplies the existence and uniqueness of projected
simple roots and coroots, and separation of their root labels. A projected root
restricts to its original root because their difference is in the restriction
kernel. Thus restriction has the required root-set image, and its injectivity
on the annihilator transports separation to restricted roots.

A unique projected coroot has a unique preimage under the injective
cocharacter map with its specified range. Separation fixes the root label in
any competing restricted-coroot witness. The ambient coweight basis supplies
one fundamental coweight for each simple root outside `J`; the published subset
lemma places it in the same range. Coweight uniqueness from the
fundamental-weight premise and injectivity give its unique preimage.

## Chambers and fundamental weights

Choose an annihilator lift of a character of `A`. Adjunction of real character
restriction and the cocharacter map, together with the published pairing
identity for projected coroots, identifies its pair inequalities with the
ambient simple-coroot conditions. This proves equality of the printed and
lifted open chambers and of their closed versions.

The lifted chambers are exactly the restriction images of the ambient
simple-coroot faces. The weight basis in the ambient chamber premise describes
these faces by positive or nonnegative coefficients and an element in the
range of restricted group characters. Transport that description under
restriction. The uniqueness of ambient fundamental weights, supplied by the
fundamental-weight premise, permits the target's arbitrary weight family in
place of the chosen basis family.

## Cone comparisons

For the positive coroot cone, reindex each finite set of relative roots by its
underlying characters and choose lifts of the projected coroots. The difference
between the original-coroot combination and the image of the lifted
combination lies in the span of the coroots of `J`. Comparing it with the
specified projected combination gives an element in both complementary
subspaces, hence zero. Injectivity then gives the equality in `V A`. The
converse follows by summing the corresponding projected-coroot differences;
separation of restricted roots fixes every label.

For the nonnegative cone, first rewrite the hull as nonnegative combinations
indexed by the selected roots. The published `RootCombination` family lemma
allows repeated vectors. Finiteness of the simple roots follows from
`standardLeviCentralDirections`. The same argument with coefficient predicate
`0 ≤ c` proves the nonnegative comparison.

The last two clauses use the transport helpers for projected root cones. The
restriction kernel removes the projection error in each finite sum; its
annihilator complement supplies the reverse lift. The nonnegative case first
rewrites the finite hull as a family of coefficients. These comparisons are
proved for every finiteness witness required by the existing restricted-root
cone definitions.

The two companion helper modules contain only derived linear algebra with
explicit hypotheses:
[ParabolicSplitComponentTransport](ParabolicSplitComponentTransport.md) and
[ParabolicSplitComponentCorootCones](ParabolicSplitComponentCorootCones.md).
The reduction assembles precisely the thirteen clauses of the target, and
the final theorem discharges its three premises with the published proofs
named above. The proof covers the empty simple-root set and `J` equal to the
full simple-root set without extra assumptions; it makes no separate
topological closure assertion.
