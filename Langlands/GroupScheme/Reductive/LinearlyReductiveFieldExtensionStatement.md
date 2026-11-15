# Linear reductivity under extension of the base field

`Langlands.GroupScheme.LinearlyReductiveFieldExtensionStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k K : Type u` be fields with `[Algebra k K]`, and
let `G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. For a field
`F : Type u` and a group scheme `H` over `Spec (CommRingCat.of F)`, let
`IsLinearlyReductive H` (a local `let` in the statement) be

```text
∀ (n : ℕ) (ρ : MatrixRepresentation H (Fin n)),
  sSup {W : Submodule F (Fin n → F) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule F (Fin n → F), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤.
```

Then

```text
IsLinearlyReductive G ↔
  IsLinearlyReductive
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).
```

In words: an affine group scheme `G` of finite type over a field `k` is
linearly reductive (every finite-dimensional representation is semisimple)
if and only if its base change `G_K` to an extension field `K` is linearly
reductive. No condition is placed on `K / k`: it may be inseparable or
transcendental.

The ingredients are existing declarations, used without change.

- `MatrixRepresentation H (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : H ⟶ GL_n` over `F`, that is, a representation of `H` on
  `Fⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these, so quantifying over all `n` and all `ρ` covers
  all finite-dimensional representations.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `F`-algebra `A`, every point `x` of `H` with
  values in `A`, every `v ∈ W` and every `F`-linear map `ℓ : A → F`, applying
  `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is
  the set of vectors of `Aⁿ` all of whose images under such `ℓ` lie in `W`,
  this says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to
  `x⁻¹` gives equality. So the stable subspaces are exactly the subspaces
  stable under `H` in Milne's sense, that is, the subrepresentations.
- The set inside `sSup` is the set of simple subrepresentations of `ρ`:
  nonzero stable subspaces `W` whose only stable subspaces contained in `W`
  are `0` and `W`. So `IsLinearlyReductive H` says that every `Fⁿ` is the
  sum of its simple subrepresentations. For `n = 0` the condition holds
  trivially (the empty sum). The same condition is used in
  `CommutativeLinearlyReductiveMultiplicativeTypeStatement` (in
  [`Torus.LinearlyReductiveMultiplicativeTypeStatement`](../Torus/LinearlyReductiveMultiplicativeTypeStatement.md))
  and in `CharZeroSemisimpleRepresentationIdentityComponentStatement` (in
  [`Reductive.SemisimpleRepresentationIdentityComponentStatement`](SemisimpleRepresentationIdentityComponentStatement.md)).
- `GroupScheme.baseChange f` (from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is the
  pullback of group schemes along `f`. Here `f` is
  `Spec K ⟶ Spec k`, the morphism induced by `algebraMap k K`, so the
  second group is `G_K = G ×_{Spec k} Spec K` with its group structure.
  It lies over `Spec (CommRingCat.of K)`, so `IsLinearlyReductive` is applied
  to it with `F = K`.

## Provenance (derived)

Main source: J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field*, 2022 corrected reprint, in the project literature
folder, registered as `milne-2022-algebraic-groups` (SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`). Printed
page numbers are given; the PDF page is the printed page plus 11.

Remark 12.53(c), printed p. 249, reads: "Let G be an algebraic group over k,
and let k′ be a field containing k. If G_{k′} is linearly reductive, then so
is G (apply 4.19a). Conversely, if G is linearly reductive and k′ is
separable over k, then G_{k′} is linearly reductive. Indeed, the
representations of the form (V, r) ⊗ k′ are semisimple (4.19c), and every
representation of G_{k′} is a subquotient of such a representation (this
follows from 4.14)." Its footnote 2 (same page) reads: "In fact, it follows
from the classification (12.56) that G is linearly reductive if and only if
G_{k′} is linearly reductive (no condition on k′/k)." The Lean statement is
the claim of the footnote. Milne proves one implication for every `k′` and
the other for separable `k′` in the remark itself, and states the general
equivalence in the footnote without proof.

Definition 12.52, printed p. 248: "An algebraic group is linearly reductive
if every finite-dimensional representation is semisimple." Opening of
Chapter 12, printed p. 230: "Recall that all algebraic groups are affine
over a base field k."

The 2017 edition (`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`; the PDF page
is the printed page plus 16) has the same wording for Definition 12.52 and
Remark 12.53(c), both on printed p. 248, where the footnote is numbered 1
and has the same wording.

Conventions for representations, from the 2017 edition (the same passages
are cited in the Markdown of
`CommutativeLinearlyReductiveMultiplicativeTypeStatement`):

- Notations, printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k". Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k."
- Chapter 4 opens, printed p. 83, with "Throughout this chapter, G is an
  affine algebraic group over a field k." On the same page: "A linear
  representation of G is a homomorphism r: G → GL_V of group-valued functors.
  When V is finite-dimensional, r is a homomorphism of algebraic groups."
  Printed p. 41: "If V has finite dimension n, then the choice of a basis for
  V determines an isomorphism GL_V → GL_n".
- Subrepresentations. The proof of Corollary 4.8, printed p. 86, states: "A
  subspace W of V is stable under G if and only if it is an O(G)-subcomodule
  of V". These subspaces are the subrepresentations.
- Semisimple. Definition 4.15, printed p. 90: "A representation of an
  algebraic group is simple if it is ≠ 0 and its only subrepresentations are
  0 and itself. It is semisimple if it is a sum of simple
  subrepresentations."

The provenance is derived for these reasons:

- The group. Milne's `G` is an affine group scheme of finite type over `k`
  (the affineness convention of Chapter 12). The Lean statement assumes
  `[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`; since
  `Spec k` is quasi-compact and `G` is affine over it, the two together say
  that `G` is of finite type over `k`. Smoothness is not assumed, as in
  Milne.
- The extension. Milne's `k′` is a field containing `k`. The Lean statement
  takes a field `K` with `[Algebra k K]`; a ring homomorphism between fields
  is injective, so `K` is an extension field of `k`, and every extension
  field arises this way. `G_{k′}` is the base change, which is the group
  `(GroupScheme.baseChange f).obj G` with `f` as above. It is again affine
  and of finite type over `K`, so it is an algebraic group over `K` in
  Milne's sense; the statement does not need these properties as instances,
  because `IsLinearlyReductive` does not use them.
- Linearly reductive. Every finite-dimensional representation `(V, r)` is
  isomorphic, after the choice of a basis of `V`, to a homomorphism
  `H → GL_n`, and an isomorphism of representations carries simple
  subrepresentations to simple subrepresentations. So Definition 12.52 for
  `G` (over `k`) and for `G_K` (over `K`) is `IsLinearlyReductive`.
- `k`, `K`, `G` and the test algebras in `IsStableSubspace` lie in one
  universe `u`. This is a formalization convention.

Relation to the Library. The Library has no notion of linear reductivity.
`SemisimpleRepresentationFieldExtensionStatement` (in
[`Reductive.SemisimpleRepresentationFieldExtensionStatement`](SemisimpleRepresentationFieldExtensionStatement.md),
Milne's Proposition 4.19) concerns one representation and its base change;
the present statement concerns all representations of `G` and all
representations of `G_K`, including those not obtained by base change.

Errata. The official errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 230, 248 or 249. The errata snapshot of 2026-11-02 for
the 2017 book (source ID `milne-2017-algebraic-groups-errata-2026-11-02`,
SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has, for
p. 85, "G_W is the stabilizer of W in G (not V)", consistent with the reading
of stable subspaces above, and for p. 249 an entry on the proof of
Theorem 12.57 only; it has no entry for printed pp. 3, 6, 41, 83, 86, 90,
230 or 248.

## For the later proof (not part of this unit)

- If `G_K` is linearly reductive, so is `G`: for `ρ : MatrixRepresentation G
  (Fin n)`, the base change `ρ.baseChange f` (in
  [`Rational.ValuedRepresentationBaseChange`](../Rational/ValuedRepresentationBaseChange.md))
  is a representation of `G_K`, hence semisimple, and part (a) of
  `SemisimpleRepresentationFieldExtensionStatement` (Milne's Proposition
  4.19(a)) gives that `ρ` is semisimple. This is Milne's argument.
- The converse for separable `K / k` is Milne's argument quoted above. For
  general `K / k`, Milne's footnote refers to the classification of
  Remark 12.56: in characteristic zero, Corollary 22.43, whose Lean form is
  the first conjunct of `CharZeroSemisimpleRepresentationIdentityComponentStatement`
  (stated there for smooth `G`; algebraic groups in characteristic zero are
  smooth); in characteristic `p ≠ 0`, Nagata's theorem, whose Lean form
  `NagataLinearlyReductiveStatement` was submitted separately by the same
  author and was not in the Library when this unit was written. In both cases
  a proof must also show that the conditions of the classification are
  unchanged by base change to `K`.
