# `GL_n` is reductive: statements

This module states two theorems about the Library general linear group scheme
`Langlands.GroupScheme.GeneralLinear.groupScheme n R` over `Spec R`. They concern the notions
of `Langlands.GroupScheme.Reductive.Basic`. The module proves neither. The third declaration,
`ReductiveStatement`, is their conjunction. All three declarations are `Prop`-valued
definitions in the namespace `Langlands.GroupScheme.GeneralLinear`, with one universe
parameter `u`.

## `IsConnectedReductiveStatement`

For every field `k : Type u` and every finite index type `n : Type` with decidable equality,
`groupScheme n (CommRingCat.of k)` satisfies `IsConnectedReductive`. Unfolding that structure,
`GL_n` over `Spec k` is smooth, affine and connected. Its base change to `AlgebraicClosure k` has
trivial unipotent radical: every smooth connected unipotent closed subgroup with normal image is
trivial.

## `IsReductiveStatement`

For every finite index type `n : Type` with decidable equality and every `R : CommRingCat.{u}`,
`groupScheme n R` satisfies `IsReductive`. That is, it is smooth and affine over `Spec R`, and
for every point `s` of `Spec R` its geometric fibre is pseudo-reductive. The geometric fibre is
the base change along `Spec κ(s)^alg → Spec R` (`geometricFiber`). Over an algebraically closed
field, pseudo-reductive is the same as connected reductive. The case `n` empty is included; then
`GL_n` is the trivial group.

## `ReductiveStatement`

`ReductiveStatement` is `IsConnectedReductiveStatement ∧ IsReductiveStatement`, in the same
universe `u`. It is the single target for a proof of both statements.

## Sources

- Milne, *Algebraic groups* (2017), §19.b. Lemma 19.16 and Example 19.19 are on printed p. 401
  (PDF p. 417). Example 19.19 says that `GL_n` is reductive because it is connected and its
  standard representation is simple and faithful. Lemma 19.16 says that a normal unipotent
  subgroup acts trivially on every semisimple representation. Milne's reductive groups are the
  connected ones of Definition 6.46 (printed p. 135), as in `IsConnectedReductive`.
- Conrad, *Reductive group schemes* (2014), Definition 3.1.1 (p. 81): a reductive group over a
  scheme `S` is a smooth `S`-affine group whose geometric fibres are connected reductive. The
  second statement is that definition applied to `GL_n` over `Spec R`. Its content beyond the
  first statement is that geometric fibres of `GL_n` are `GL_n` over algebraically closed
  fields. Conrad treats this as standard; it is derived here from Milne's field case.
