# Solutions of birational group laws over a discrete valuation ring

The module `Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement` states the
theorem of Weil and Artin that a birational group law over a discrete valuation ring has
a solution, in the form of Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990),
§5.1, Theorem 5, printed p. 114 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). The definitions it uses are in
`Langlands.AlgebraicGeometry.BirationalGroupLaw`. The module states a proposition and
proves nothing.

## The proposition

`BirationalGroupLawSolutionStatement.{u}` quantifies over a discrete valuation ring `R`
in universe `u`, a scheme `X` and `f : X ⟶ Spec R` which is smooth, separated, locally
of finite type, quasi-compact and surjective, and a `BirationalGroupLaw f` `m`. It
asserts:

1. `Nonempty m.Solution`: `m` has a solution;
2. if every point `p` of `X ×_R X` lying over the generic point of `Spec R` (its image is
   not the closed point) lies in `m.domain`, in the image of the universal left
   translation of `m` and in the image of the universal right translation of `m`, then
   there is a solution `σ` with `σ.domain = ⊤`.

## Correspondence with the source

BLR 5.1/5: let `S` be the spectrum of a field or of a discrete valuation ring and `m` an
`S`-birational group law on a smooth separated `S`-scheme `X` which is faithfully flat
and of finite type over `S`. Then `m` has a solution, unique up to canonical
isomorphism. If, in the case of a discrete valuation ring, the generic fibre `X_K` is a
group scheme under the law `m_K`, the assertion holds with `X' = X`.

- The base is a discrete valuation ring; the case of a field is not stated.
- Faithfully flat and of finite type: `Smooth` gives flatness, `Surjective` gives
  faithful flatness, and `LocallyOfFiniteType` with `QuasiCompact` is finite type.
- Clause 1 is the existence assertion. Uniqueness, proved in BLR 5.1/3, is not stated.
- Clause 2 is the assertion for `X' = X`, with its hypothesis expressed on the given
  representative of `m`. The hypothesis says that `m` is defined on all of the generic
  fibre `X_K ×_K X_K` and that the universal translations `Φ` and `Ψ`, which are open
  immersions over `R`, map the generic fibre onto the generic fibre. Then
  `m_K : X_K ×_K X_K ⟶ X_K` is an associative law whose universal translations are
  isomorphisms, and `X_K` is nonempty since `f` is surjective; such a law is a group law
  (the unit section exists by descent of the right-unit map `x ↦ e(x)` along the
  faithfully flat `X_K ⟶ Spec K`). Conversely, when `X_K` is a group scheme under the
  rational map `m_K`, the group law and a representative of `m` agree on the generic
  fibre of the representative's domain, so they glue to a representative satisfying the
  hypothesis. In BLR the domain `X'` of a solution is an open subscheme of `X`;
  `σ.domain = ⊤` is `X' = X`.

The existence proof in BLR first passes to a strict birational group law on an `R`-dense
open subscheme (5.2/2), constructs the solution over a strictly henselian base by gluing
translates (5.2/3, §5.3), and descends it to the given discrete valuation ring
(6.5/2, printed p. 157). The clause `X' = X` is proved after 5.1/5 using Weil's extension
theorem 4.4/1.

## Use

This is the step from birational group laws to group schemes in the construction of
Néron models (BLR 4.3/6, printed p. 108, which refers to 5.1/5).
