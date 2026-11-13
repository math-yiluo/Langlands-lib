# Classical type-D spin presentations and actual indices

Author: Worker 180.

`Langlands.GroupScheme.ClassicalTypeDSpinPresentationStatement.{u}` is
an **unproved** prerequisite for the rank-one quaternionic spin
identification. It applies to every field, in every characteristic,
and to every absolute rank `n ≥ 4`. It assumes neither a supplied
algebra with involution nor a supplied form or spin cover.

## Hypotheses

Let `K : Type u` be a field, let `G` be an affine locally finite type
group scheme over `Spec K`, and let `d : TitsIndexData G` be an actual
index. Assume `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`.
Supply a numbering `e : d.Vertex ≃ Fin n` with `4 ≤ n`, preserving
every Cartan entry of `CartanMatrix.D n`.

The full absolute Galois star action must fix every vertex numbered
`1, …, n − 2` in one-based notation. In Lean this is
`(e a).val + 2 < n → d.star γ a = a` for every absolute Galois
element `γ` and vertex `a`. The only vertices that may move are the two
fork tips, numbered `n − 1` and `n`. Because the actual star action
acts by diagram automorphisms, this allows inner type `D` and the
classical outer type `²D`. For `D₄`, it fixes the chosen first arm and
allows a swap of the other two arms; trialitarian images of order 3
or 6 are excluded. The image need not be nontrivial.

There is no hypothesis about distinguished vertices, split rank,
local fields, perfection or characteristic.

## Conclusions

The statement supplies a central finite dimensional division algebra
`D : Type u` over `K`, natural numbers `degree` and `m`, an involution
`σ : Quaternionic.FirstKindInvolution K D`, a form
`q : σ.QuadraticForms (Fin m)`, and a group-scheme morphism
`π : G ⟶ σ.isometryGroup q`, with:

- `0 < degree`, `Module.finrank K D = degree ^ 2`, and
  `m * degree = 2 * n`;
- `Module.finrank K σ.symmetricSubspace =
  degree * (degree + 1) / 2`;
- `σ.IsNondegenerateQuadratic q` and
  `σ.quadraticWittIndex q = splitRank G`;
- for each nonfork vertex `a`, membership in
  `d.distinguishedVertices` is equivalent to
  `(e a).val + 1 = j * degree` for some natural number `j` with
  `0 < j ≤ σ.quadraticWittIndex q`;
- `σ.IsSpinCover q π`.

The integer division by 2 in the symmetric-dimension formula is natural
number division. The product of two consecutive integers is even.
`degree` is the division algebra's degree, not its dimension.

The presentation is chosen **for the supplied numbering**. The statement
does not assert the vertex formula for every numbering of an unrelated,
already chosen spin presentation. That distinction matters for the
three possible vector nodes of `D₄`.

No formula for the two fork vertices is asserted. Tits's fork exceptions
are therefore outside this statement's conclusion. The nonfork formula
already suffices for a rank-one index with only vertex 2 distinguished.
There is no discriminant assertion or uniqueness assertion.

## Actual forms and covers

The imported objects are the ones used by
`TypeDRankOneSpinStatement`: `σ.QuadraticForms (Fin m)` is
`M_m(D) / {X − ᵗX^σ}`; nondegeneracy means that its polar Gram matrix
is invertible; the Witt index is the maximum dimension of a totally
singular left `D`-subspace. The isometry group is the actual affine
group scheme of these forms. `IsSpinCover` requires simple
connectedness of `G`, smoothness of `O(q)`, and a central isogeny
`G → O(q)⁰` whose composite with the inclusion is `π`.

These are conclusions, including smoothness and the actual morphism.
The statement concerns group schemes and all algebra-valued points.
It does not replace the cover by an isomorphism of rational point groups.

In characteristic 2, the quotient of matrices remains the space of
quadratic forms; it cannot be replaced by the polar hermitian form.
The absolute degree `m * degree = 2 * n` is even, so invertibility
of the polar matrix is Tits's nondegeneracy condition in this case.
The symmetric-dimension condition is Tits's type-1 convention, including
in characteristic 2.

## Original sources and derived formulation

The primary index source is J. Tits, *Classification of algebraic
semisimple groups* (1966), Table II explanations, printed pp.54–55
/ proceedings PDF pp.59–60, and the entries `¹D_n` and `²D_n`,
printed pp.56–57 / PDF pp.61–62. Registered source:
`tits-1966-classification-algebraic-semisimple`; PDF SHA-256:
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

There `degree` is Tits's `d`, the square root of the division algebra
dimension, `m = 2n/d`, and `r` is the relative rank and form index.
On the chain the distinguished vertices are `d, 2d, …, rd`.
For `²D_n`, when `n = rd + 1` the last term becomes the orbit of
the fork tips. The restriction to vertices numbered at most `n − 2`
avoids that exception, and also the inner-type endpoint conventions.
The source describes strict-isogeny representatives, with hermitian
forms in characteristic different from 2 and Seip-Hornix quadratic
forms in characteristic 2; it does not directly state this Lean
group-scheme proposition.

The characteristic-independent form and group conventions come from
J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de
Clifford* (1968):

- §2.1, printed p.20 / PDF p.3, for the type-1 involution and
  symmetric-space dimension;
- §§2.2–2.3, printed pp.21–22 / PDF pp.4–5, for the quotient of
  bilinear forms, its polar form, nondegeneracy in even degree and
  the division-algebra realization;
- §3, Proposition 6, printed p.30 / PDF p.13, for the actual
  algebraic isometry groups and their geometric models;
- §3, Theorem 1 and Remark 3, printed p.31 / PDF p.14, for the
  central-simple-algebra realization and the type-`D₄` caveat;
- §4.4, printed p.39 / PDF p.22, where `Spin q` is the universal
  cover of `SU(q)⁰`.

Registered source: `tits-1968-formes-quadratiques-clifford`;
PDF SHA-256:
`f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782`.
The cited pages were read from the original scans.

The matrix-quotient convention is also stated in Tits, Bourbaki
exposé 505 (1977), §1.1.6, printed p.220 / PDF p.4
(`tits-1977-whitehead-bourbaki-505`, PDF SHA-256
`293a1b0637af56694914a6a4999b3bb56ae69d41444f748ad3fca037cce2f229`).
It gives the dimension `degree * (degree + 1) / 2` and the relation
`n = m * degree / 2` for the associated spin group. That exposé's
subsequent generation theorem is not used.

This is a derived formulation combining these descriptions with the
Library's actual Tits index, left row-vector conventions and spin-cover
predicate. The source does not supply the presentation as an input.
In particular the proof successor must construct the realization
aligned with the numbered vector node, perform the division-algebra
and quadratic-form comparison, identify the actual distinguished
vertices and relative rank, and construct the cover of the given `G`.
This file does not prove any of those structural steps.
