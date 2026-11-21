# Root support of a Lie vector contracted by an apartment cocharacter

`Langlands.Geometry.Building.LieRootSupportOfApartmentCocharacterStatement`
is a Prop-valued target on the actual maximal split torus `S → G` of supplied
`ParahoricBuildingData G` over a nonarchimedean local field `F`. It uses the
centralizer and relative affine-root submodules of a supplied
`L : P.LieFiltrationData`.

Let `x` be in the apartment of `S`, let `r ∈ ℝ`, and suppose
`X ∈ L.lieFiltrationReal x r`. The second premise says that `X` belongs to
the strictly positive adjoint weight span for the composite of an actual
`F`-cocharacter `ν : Gₘ → S` with `S → G`. This is contraction in the sense
of KP Definition 13.6.5, with this specific cocharacter already given.

Write `v` for the image of `1 ⊗ ν` in the reduced apartment translation
space (the quotient by the common root kernel), `n = ⌈−r⌉₊` and `t = r+n`.
For every `a ∈ 𝔪ⁿ`, the conclusion puts `a • X` in the supremum of the
relative affine-root Lie submodules `L.affineRootLie ψ` satisfying both
`ψ(x) ≥ t` and `ψ̇(v) > 0`. In particular, the supported span in this
conclusion has no centralizer summand. The scalar shift is the one used
by `lieFiltrationReal`; at nonnegative depths one can take `a = 1`. The
target does not assume periodicity, because it compares at one shifted
depth, not between different shifts.

## Provenance and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023),
printed p. 481 / PDF p. 512, proof of Proposition 13.6.7, uses contraction
by `ν` to eliminate the centralizer term and obtain positive derivatives
on the contributing boundary terms. The statement here is a derived
formulation on the Library's **relative** root spans of §13.3.3 (printed
pp. 470–471 / PDF pp. 501–502), rather than the source proof's decomposition
written with absolute affine roots. It uses the real-depth convention of
§13.3.1 and the cocharacter contraction convention of Definition 13.6.5
(printed p. 480 / PDF p. 511). The 1 November 2024 corrections, p. 49, do
not change this weight-support step. The statement does not obtain `ν`
by conjugacy, move the whole coset, choose an optimal point, or identify
any of the supplied submodules with Lie algebras of constructed models.
