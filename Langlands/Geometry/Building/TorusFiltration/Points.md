# Minimal congruent torus subgroups at all finite depths

`Langlands.Geometry.Building.minimalCongruentPoints` gives a subgroup
of `T(K)` for each nonnegative real depth `r`, where `T` is a torus over
the maximal unramified field `K = inertiaFixedField F` of a nonarchimedean
local field `F`. The term for `r < 1` is `minimalCongruentShallowSubgroup`.
For `r = q + n` with `0 ≤ q < 1` and `n > 0` an integer, the construction
uses the `n`th congruence kernel on integral sections, mapped to `T(K)`.

The positive-level operation is expressed independently of a choice of
smooth model. It intersects the `n`th congruence subgroups of all smooth
integral models whose integral points contain the prescribed shallow
subgroup at `q`. This family contains the connected Néron model. When a
smooth model has exactly the prescribed shallow integral points, its
`n`th congruence subgroup is the intersection. Indeed, the generic
identity extends from this model to each of the models in the family
by the smooth-model extension criterion. The extension preserves
congruence points, giving one inclusion. The realizing model itself
belongs to the family, giving the other inclusion. Thus
`minimalCongruentPoints_add_pnat` gives the point formula of part (3)
for every realizing model, and `minimalCongruentPoints_pnat` computes
each positive integer depth using the connected Néron model.

`minimalCongruentPlus` is the union at strictly greater depths. Its
agreement with the underlying set of the subgroup supremum is proved
under the antitone condition on the full family. The coefficient
extension map `rationalExtend` gives the pullback subgroup
`minimalCongruentBasePoints` in the points of a torus over `F`.

This is a point construction. The model existence used to identify a
term with a congruence group scheme is the assertion of Lemma B.10.9
for shallow positive depths and Definition A.5.12 for their integer
translates.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Definition A.5.12 and Lemma A.5.13 for congruence levels (printed
p. 636 / PDF p. 667), Definition B.5.2 for the union convention (printed
p. 667 / PDF p. 698), and Definition B.10.8(3) and Lemma B.10.9 for the
depth decomposition (printed p. 690 / PDF p. 721). The base-field
pullback is part (4) added in `kaletha-prasad-2024-corrections`, version
of 1 November 2024, PDF p. 50, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
