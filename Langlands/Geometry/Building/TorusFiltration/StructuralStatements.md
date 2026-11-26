# Structural statements for the minimal congruent torus filtration

The statements concern the constructed `minimalCongruentPoints` on any
torus over `K = inertiaFixedField F`, for a nonarchimedean local field `F`.
Models have base `O = fixedFieldIntegers F` and their integral sections
map into the actual torus point group. `MinimalCongruentStructuralStatements`
is the conjunction of the following proposition definitions.

* `MinimalCongruentShallowModelStatement` asserts that the generated
  subgroup at each strictly positive depth below one has a smooth
  affine model with geometrically connected fibres and those exact
  integral points.
* `MinimalCongruentFunctorialityStatement` asserts the subgroup inclusion
  induced by every `K`-homomorphism of tori at each depth.
* `MinimalCongruentOrderStatement` asserts that the family decreases,
  that the intersection over depths is the trivial subgroup, and
  that the set of depths where the strict-depth union differs from
  the depth term is discrete.
* `MinimalCongruentConnectedModelStatement` asserts existence of
  a smooth affine model with geometrically connected fibres and the
  given integral-point subgroup at every depth.
* `MinimalCongruentCongruenceStatement` identifies the first congruence
  subgroup of any such smooth realizing model at `r` with the term at
  `r + 1`. Its left side is the image in the generic torus of the
  kernel of reduction.
* `MinimalCongruentWeaklyInducedStatement` asserts equality with
  the standard filtration `localTorusFiltration` at every depth.
  Its hypothesis `IsWeaklyInducedTorus` means induced after a finite
  tame extension of `K`.

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
give the shallow model result and the structural properties in Lemma B.10.9
and Proposition B.10.10 (printed p. 690 / PDF p. 721). The schematicity,
connectedness and congruence conventions are in Definitions B.5.2–B.5.3
(printed pp. 667–668 / PDF pp. 698–699). The separated filtration convention
is also in Definition B.10.2 (printed p. 687 / PDF p. 718). The weakly
induced comparison is Corollary B.10.13 (printed p. 692 / PDF p. 723), with
its hypothesis from Definition B.6.2.
The constructed point family uses Definition B.10.8 as amended in
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p. 50,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
