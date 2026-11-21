# Promotion of a root-supported Lie coset within an apartment

`Langlands.Geometry.Building.LieCosetPromotionOfPositiveRootSupportStatement`
is a Prop-valued target for the apartment translation step in the proof of
Kaletha–Prasad Proposition 13.6.7. It is not a statement of the entire
proposition.

Let `F` be a nonarchimedean local field of either characteristic, `G` an
affine group scheme over `F`, `P : ParahoricBuildingData G` supplied building
data, and `L : P.LieFiltrationData` supplied relative affine-root and
centralizer Lie lattices. Use the real-depth convention of
`KPLieFiltrationDual`. Assume `L.IsPeriodic`, so that `𝔤_{x,r+}` is the
union of the decreasing family at `s > r` and lies in `𝔤_{x,r}`.

For an apartment point `x`, an apartment translation vector `v`, a real
number `r` and `X` in the generic Lie algebra, the target has two further
premises:

- The strict-depth submodule `𝔤_{x,r+}` is finitely generated over
  `𝒪[F]`. Here this is an explicit hypothesis on supplied submodules.
- Write `n = ⌈−r⌉₊`, `t = r+n` and `𝔪` for the maximal ideal of `𝒪[F]`.
  For each `a ∈ 𝔪ⁿ`, the vector `a • X` belongs to the supremum of
  `L.affineRootLie ψ` over the relative affine roots `ψ` for which either
  `ψ(x) > t` or `ψ(x) = t` and `ψ̇(v) > 0`. This is a condition on the
  representative, not on the centralizer or root components of the
  strict-depth denominator. At nonnegative depths it just requires `X`
  to lie in the indicated root span: `n = 0`, so one can take `a = 1`.
  Every root included in the supremum satisfies `ψ(x) ≥ t`; hence the
  support condition implies `X ∈ 𝔤_{x,r}` by the real-depth definition.

The conclusion gives `δ > 0` such that for each `0 < ε < δ` there is
an `s > r` with `X + 𝔤_{x,r+} ⊆ 𝔤_{εv +ᵥ x,s}`. In Lean, membership of
`Y` in the translate is `Y - X ∈ 𝔤_{x,r+}`. The choice of `s` precedes
`Y`, so the conclusion is containment of the whole coset in one deeper
lattice, not a nonempty intersection or a separate depth for each `Y`.

## Provenance and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023),
printed p. 481 / PDF p. 512, proof of Proposition 13.6.7, moves from `x` to
`x′ = ε ν + x` using the affine-root evaluation formula and obtains
`pΞ ⊆ 𝔤_{x′,s}`. This derived relative-root target isolates that geometric
step on the Library's supplied §13.3.3 spans. It uses the depth convention
of §13.3.1, printed pp. 470–471 / PDF pp. 501–502. It spells out the root
support needed for the translation instead of deducing it from contraction
by a cocharacter, and exposes finite generation to handle the whole strict
submodule at a common depth. It does not assert parahoric conjugacy,
existence of an optimal point, or instability under the reductive quotient.
The 1 November 2024 corrections, p. 49, do not change this part of the proof.
