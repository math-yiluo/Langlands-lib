# The pro-unipotent radical of the standard torus filtration

`Langlands.Geometry.Building.StandardTorusZeroPlusRadicalStatement` is the
statement of Kaletha–Prasad Proposition B.9.1 over the maximal unramified
field. This file states it and does not prove it.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its
maximal unramified extension and `O = fixedFieldIntegers F` the integers
of `K`. Let `T` be a torus over `K` and `M = connectedNeronModel F T hT`
its connected Néron model, with special fibre `M.specialFibre` over the
residue field of `O`. The statement asserts that there are a group
scheme `U` over that residue field and a morphism `i : U ⟶ M.specialFibre`
such that

* `IsUnipotentRadical i` holds, so `i` represents the unipotent radical
  `R_u(T^0)` of the special fibre; and
* the set
  `((rationalPoints.map i).range.comap M.reduction).map M.integralPointMap`
  equals the intersection of `M.integralPoints` with the union of the
  subgroups `localTorusFiltration F T hT r` over all real `r > 0`.

The first set is formed in three steps. The range of `rationalPoints.map i`
is the group `R_u(T^0)(f)` of residue-field points of the radical inside
`T^0(f)`. Its preimage under `M.reduction` consists of the integral
sections of `M` whose reduction lies in this group. These sections are
then mapped into the generic point group `rationalPoints T.toGrp`. This
is the expression used in the second clause of
`MinimalCongruentZeroPlusStatement`.

On the right, `M.integralPoints` is `T(K)^0`; by
`connectedNeronModel_integralPoints` it equals the zero term of
`localTorusFiltration`. The family `localTorusFiltration F T hT` is the
standard filtration of Definition B.5.1. Its zero term is the Iwahori
subgroup `T(K)^0`. Its term at `r > 0` consists of the elements of
`T(K)^0` with `ω(χ(t) − 1) ≥ r` for every character `χ` of `T`. These
characters are tested after extension to the fixed separable closure of
`F`. The additive valuation there is normalized by the valuation of `F`,
which is also normalized on the unramified field `K`. The union over
`r > 0` is therefore `T(K)^std_{0+}`, following the strict-depth union
convention of Definition B.5.2. The filtration decreases, so its positive
terms lie in `T(K)^0`. The statement nevertheless keeps the intersection
with `T(K)^0`, as in the source formulation `T(K)^0 ∩ T(K)^std_{0+}`.

The statement asserts the existence of a represented radical. Any two
represented radicals have the same image on every test scheme by
`IsUnipotentRadical.range_eq`. The asserted equality therefore holds for
one represented radical exactly when it holds for every one. No radical,
split subtorus or compatibility of reductions is a hypothesis: the model,
its reduction and the filtration are the Library's constructions for the
given torus.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Proposition B.9.1 and its proof are on printed pp. 684–685 / PDF
pp. 715–716. The proof begins by noting that the statement does not
change when `k` is replaced by `K`; this file states the result over `K`.
The standard filtration is Definition B.5.1 and the strict-depth union
convention is in Definition B.5.2 (printed p. 667 / PDF p. 698). The
connected Néron model is Definition B.8.9(3) (printed p. 684 / PDF p. 715).
This proposition concerns the standard filtration. Lemma B.10.11 (printed
p. 690 / PDF p. 721) compares its zero-plus term with that of the minimal
congruent filtration and cites this proposition for the description by the
unipotent radical; that lemma is stated in `MinimalCongruentZeroPlusStatement`.
