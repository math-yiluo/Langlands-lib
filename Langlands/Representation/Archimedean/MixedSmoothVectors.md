# Genuine smooth vectors for commuting finite and archimedean actions

Let `σ` (finite-place) and `π` (archimedean) be commuting representations on a
complex inner product space `E` by bounded complex-linear operators. In the
self-modeled real charted group for `π`, the genuine smooth vectors `V∞` are
those whose actual `π`-orbit maps are smooth. Each `σ l` intertwines `π` with
itself, so the genuine smooth intertwiner construction gives `finiteOnSmooth`
on `V∞`. `Vectors` is the existing algebraic smooth part of this finite-place
representation: its elements are genuine smooth vectors fixed by some open
subgroup of the finite-place group. The fixed-space comparison uses injectivity
of the inclusion into `E` to identify fixedness on `V∞` with fixedness for `σ`
on `E`. For a locally compact nonarchimedean finite-place group, cofinality of
compact open subgroups gives a compact open fixed level for every element of
`Vectors`.

`finiteRepresentation` is the action on that smooth part. The translate by `l`
is fixed by `l J l⁻¹` if and only if the original is fixed by the compact open
subgroup `J`. The proof conjugates each `j ∈ J` to `l j l⁻¹` and uses the
representation laws and invertibility of the action on `V∞` to transport the
fixed-vector equations in both directions. For the Lie-group `π` action, the
genuine smooth translation by `g` preserves the very same subgroup's fixed
condition by commutation, and translation by `g⁻¹` gives the converse. Thus
this action restricts to `archimedeanRepresentation` on `Vectors`. Both
fixed-level equivalences also hold for the underlying values of the actual
mixed smooth actions, which agree with the original operators on `E`. The
commutation identity on `Vectors` follows by comparing these underlying values.

This is internal infrastructure derived from the published genuine smooth
intertwiner, algebraic smooth part, and compact open subgroup constructions.
The model, archimedean group, finite-place group, and carrier have independent
universes. No unitarity, completeness, globalization, or density assertion is
used or supplied.
