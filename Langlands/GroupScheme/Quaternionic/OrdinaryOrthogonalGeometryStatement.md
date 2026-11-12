# Smoothness and absolute almost-simplicity of even orthogonal groups

Authors: Worker 5196.

Module `Langlands.GroupScheme.Quaternionic.OrdinaryOrthogonalGeometryStatement`, namespace
`Langlands.GroupScheme.Quaternionic`. This module states, without proof, the geometric facts
about ordinary even-dimensional orthogonal groups that Task 5397 needs. It is a statement
only; its proof is a separate task.

## Statement

`OrdinaryOrthogonalGeometryStatement : Prop` holds when the following is true at the module's
universe `u`. Let `K : Type u` be any field, of any characteristic. Let `m : ℕ` with
`3 ≤ m`, and let `q : (FirstKindInvolution.scalar K).QuadraticForms (Fin (2 * m))` satisfy
`(FirstKindInvolution.scalar K).IsNondegenerateQuadratic q`. Then there is a proof
`h : Smooth ((FirstKindInvolution.scalar K).isometryGroup q).X.hom`, and, with `h` as the
smoothness instance,
`IsAbsolutelyAlmostSimple ((FirstKindInvolution.scalar K).connectedIsometryGroup q)`.

The objects used are all published:

- `FirstKindInvolution.scalar K` (module `ScalarInvolution`) is the identity involution of
  `K`. `(scalar K).QuadraticForms n` is `M_n(K) ⧸ {a - ᵗa}`.
- `IsNondegenerateQuadratic q` (module `Forms`) says that the polar matrix
  `(scalar K).polar q` is invertible. For a representative `Q` this matrix is `Q + ᵗQ`
  (`scalar_polar_mk`).
- `isometryGroup q` (module `GroupSchemes`) is an actual affine group scheme over
  `Spec K`, a closed subgroup of the unit group of `M_{2m}(K)`.
- `connectedIsometryGroup q` (module `GroupSchemes`) is `identityComponent` of
  `isometryGroup q` (module `IdentityComponent`). This is the open and closed subgroup
  scheme supported on the connected component of the identity. It needs a `Smooth`
  instance on `isometryGroup q`.
- `IsAbsolutelyAlmostSimple G` (module `Reductive.AbsolutelyAlmostSimple`) means
  `IsAlmostSimple G` and `IsAlmostSimple` of the base change of `G` along
  `toAlgebraicClosure K`. `IsAlmostSimple` (module `Reductive.AlmostSimple`) means
  semisimple and noncommutative, with every smooth connected closed normal subgroup trivial
  or everything.

## Formulation choices

- **Smoothness witness first.** The identity-component construction needs a smoothness
  instance. So the conclusion is an existential `∃ h : Smooth …`, followed by
  `haveI := h` and the almost-simplicity claim, which depends on `h`. `Smooth` is a
  proposition, so a proof of the existential is the smoothness of `O(q)` together with the
  almost-simplicity of `O(q)⁰`. This follows the published precedent of
  `FirstKindInvolution.IsSpinCover`, whose field `smooth` precedes the use of
  `connectedIsometryGroup`.
- **Even rank `2m`, `m ≥ 3`.** In rank `2m` the root system is `D_m`. `D_1` is a torus and
  `D_2 = A_1 × A_1` is not almost simple. `D_3 = A_3`, and `D_m` is irreducible for every
  `m ≥ 3`. Odd rank is excluded. In characteristic `2` the polar matrix of an odd-rank form is
  alternating of odd size, so it is never invertible and the hypothesis would be empty.
  Moreover `O(q)` is not smooth in odd rank in characteristic `2` (Conrad, Theorem C.1.5).
- **No characteristic hypothesis.** The statement quantifies over every field `K : Type u`.
- **Index type `Fin (2 * m)`** follows the task specification. The published constructions
  take `n : Type`.

## Ordinary quadratic-form interpretation

The paired Markdown of `ScalarInvolution` explains the identifications. A class
`q ∈ M_{2m}(K) ⧸ {a - ᵗa}` represented by `Q` is the ordinary quadratic form
`q(x) = x Q ᵗx` on row vectors `x ∈ K^{2m}`, and every ordinary quadratic form arises from
exactly one class (Tits 1968, §2.3). Its polar bilinear form
`b_q(x, y) = q(x + y) - q(x) - q(y)` has Gram matrix `Q + ᵗQ`. So the hypothesis says that
`b_q` is a perfect pairing. In even rank this is exactly Conrad's non-degeneracy of `q`, in
every characteristic (Conrad, C.1, printed p. 302, and p. 304: "if n is even or if n is odd
and 2 is a unit on S then the condition disc_e(q) ∈ G_m is equivalent to the
non-degeneracy of q").

The points of `isometryGroup q` with values in a commutative `K`-algebra `R` are the units
`u ∈ M_{2m}(R)` with `u Q ᵗu - Q ∈ R ⊗ {a - ᵗa}`. These are the `u` with
`q_R(x u) = q_R(x)` for every row vector `x ∈ R^{2m}`. The map `u ↦ (x ↦ x u⁻¹)` is
therefore an isomorphism from `isometryGroup q` onto Conrad's orthogonal group scheme
`O(q)`, the closed subgroup of `GL(V)` of `g` with `q(g x) = q(x)` (Conrad, printed p. 303).
Smoothness and absolute almost-simplicity of the identity component do not depend on this
identification.

## Characteristic 2 and the identity component

The statement uses the published `identityComponent`, the connected component of the
identity, and not a determinant kernel. Over a field `K` and in even rank `n = 2m`, Conrad's
results give the following.

- `O(q)` is smooth of dimension `n(n - 1)/2` in every characteristic (Theorem C.1.5).
- Conrad's special orthogonal group `SO(q)` is the kernel of the Dickson invariant
  `D_q : O(q) → (ℤ/2ℤ)_K` (Definition C.2.10). It is open and closed in `O(q)`, smooth and
  connected (Theorem C.2.11, Proposition C.3.1), with `O(q)/SO(q) = ℤ/2ℤ` (Remark C.2.12).
  Hence `SO(q) = O(q)⁰`, and `connectedIsometryGroup q` corresponds to `SO(q)`.
- When the characteristic is not `2`, `SO(q)` is the kernel of `det`. In characteristic `2`,
  `det : O(q) → μ_2` is identically `1` (Conrad, remark after Theorem C.1.5). So the naive
  kernel `SO'(q) = ker det` is all of `O(q)` and is disconnected; the identity component is
  the Dickson kernel instead. This is why the statement is phrased with the identity
  component.

## Mathematical content and sources

Over the algebraic closure `L = K̄`, `q` becomes isomorphic to the standard split form
`q_{2m} = x_1 x_2 + ⋯ + x_{2m-1} x_{2m}` (Conrad, Lemma C.2.1). By Conrad, Proposition C.3.10,
`SO_{2m}` is semisimple with root system `D_m` with respect to a split maximal torus. For
`m ≥ 3` the root system `D_m` is indecomposable, so `SO(q)_L` is almost simple (Milne,
Proposition 24.1). The base change of the identity component is the identity component of
the base change (published `identityComponent` base-change isomorphism `baseChangeIso`). Over
`K`, `O(q)⁰` is semisimple because its base change to `L` is. It is almost simple because a
smooth connected closed normal `K`-subgroup base-changes to such a subgroup over `L`. These
are the facts the proof task has to formalize.

- B. Conrad, *Reductive group schemes*, in *Autour des schémas en groupes I*, Panoramas et
  Synthèses 42–43, SMF, 2014 (`conrad-2014-reductive-group-schemes`); printed page = PDF
  page in the local file.
  - Appendix C.1, printed p. 302: quadratic forms, `B_q(x, y) = q(x + y) − q(x) − q(y)`,
    non-degeneracy. Printed pp. 303–304: the orthogonal group `O(q)` and the discriminant
    criterion for even `n`.
  - Theorem C.1.5, printed p. 305: "The S-group O(q) is smooth if and only if either n is
    even or n is odd with 2 a unit on S … These smooth groups have fibers of dimension
    n(n − 1)/2." Printed p. 306: "If n is even then over fields k of characteristic 2 the
    map det : O(q) → µ2 is identically 1 due to smoothness of O(q), so SO′(q) = O(q) in
    such cases."
  - Lemma C.2.1, printed p. 309: a quadratic space of rank `n` is fppf-locally (étale-locally
    for even `n`) isomorphic to `(O_S^n, q_n)`.
  - Definition C.2.10, printed p. 317: "SO(q) is SO′(q) = ker(det|O(q)) when n is odd and
    ker D_q when n is even". "It is also an open subscheme of O(q) when n is even."
  - Theorem C.2.11, printed p. 318: "The group SO(q) is smooth with connected fibers of
    dimension n(n − 1)/2." Remark C.2.12, p. 318: `O(q)/SO(q) = (ℤ/2ℤ)_S` for even `n`.
    Proposition C.3.1, p. 318: for even `n`, `SO(q) → S` has connected fibres.
  - Proposition C.3.10, printed p. 325: "For m ⩾ 2, the smooth affine Z-group SO_2m is
    semisimple … The diagonal µ2 ⊂ T is the schematic center of SO_2m, and Φ(SO_2m, T) is
    D_m."
- J. S. Milne, *Algebraic Groups*, Cambridge Stud. Adv. Math. 170, 2017
  (`milne-2017-algebraic-groups`), Proposition 24.1, printed p. 512 / PDF p. 528: for a split
  semisimple group, almost-simple, indecomposable root system and geometrically
  almost-simple are equivalent.
- J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de Clifford*, Invent. Math.
  5 (1968), 19–41 (`tits-1968-formes-quadratiques-clifford`), §2.3, printed p. 23 / PDF
  p. 6: for `D = k` the quotient `Q` corresponds bijectively to ordinary quadratic forms.
- Motivation: Tits, Bourbaki exposé 505 (1977), 1.1.6, printed p. 220 / PDF p. 4
  (`tits-1977-whitehead-bourbaki-505`), and Tits 1966, Table II, printed pp. 56–57 / PDF
  pp. 61–62 (`tits-1966-classification-algebraic-semisimple`). Over a splitting field, the
  quaternionic groups of type `D` that Task 5397 studies become even orthogonal groups. This
  statement supplies the split-side geometry, and the Morita comparison is a separate
  statement (`QuaternionicMoritaIsometryStatement`).
