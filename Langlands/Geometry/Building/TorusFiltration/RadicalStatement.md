# The pro-unipotent term of the minimal congruent torus filtration

`MinimalCongruentZeroPlusStatement` concerns a torus over the maximal
unramified extension `K = inertiaFixedField F` of a nonarchimedean local
field `F`. Put `M = connectedNeronModel F T hT`. The statement gives
three descriptions of the strict-depth union at zero.

* It equals the intersection of `M.integralPoints = T(K)^0` and the
  strict-depth union at zero for the standard filtration.
* It is the preimage of the rational points of the unipotent radical
  of `M.specialFibre`. The preimage is taken under reduction on
  integral sections and then mapped into the generic torus.
* A smooth model with these integral points has a compatible map
  to `M` whose special-fibre map factors surjectively through the
  unipotent radical.

`MinimalCongruentPositiveUnipotentStatement` asserts that every smooth
model realizing a term at strictly positive depth has unipotent
special fibre. Over the perfect residue field, the cited proof
constructs unipotent groups from the positive-depth images and
congruence morphisms. The printed vector-group assertion at all
positive depths fails in general under the definition of vector
group in §2.10.20. For example, in equal characteristic two take
`K` to be the maximal unramified extension of `F₂((t))`, and take
`E = K(u)` with `u³ = t`. For the induced torus `Res_{E/K} G_m`
at depth `1/3`, the minimal congruent and standard filtrations
agree by Corollary B.10.13. Proposition B.3.6 constructs the
standard model by Weil restriction from the first congruence group
scheme over the integers of `E`. Its special-fibre points are parametrized by
`a ∈ f̄[u]/(u³)` through the original generic coordinate `1 + ua`.
Their group law is `a + b + uab`, so the point with parameter `1`
has square with parameter `u ≠ 0`. The additive group of a vector
space in characteristic two has exponent two. The preimage and
unipotence statements retain their original scope.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See §2.10.20 (printed pp. 128–129 / PDF pp. 159–160), Proposition B.3.6
(printed pp. 658–659 / PDF pp. 689–690), Lemma B.10.11, Proposition
B.10.12 and Corollary B.10.13 (printed pp. 690–692 / PDF pp. 721–723). The filtration in these
statements uses Definition B.10.8 as amended in
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p. 50,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
