# Bounded open-subgroup normalizers in the rational common norm kernel

`boundedOpenNormalizer` proves exactly the published
`Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerStatement.{u}`,
at arbitrary universe `u`. For every connected reductive group `G` over a
nonarchimedean local field `F` and every algebraically bounded open subgroup
`H` of its actual rational points, the actual normalizer of `H`, intersected
with `Langlands.Plancherel.rationalCommonNormKernel G`, is algebraically
bounded. All topologies are the canonical rational-point topologies.

The theorem applies `boundedOpenNormalizer_of_adjoint_inputs`, supplying both
of its inputs by proved declarations. That reduction makes the open subgroup
a Zariski-dense family of actual rational points using rational local density,
and constructs an actual quotient `q : G → A` by the full scheme center.

The first input is `denseBoundedNormalizerAdjoint`. It chooses a closed
faithful matrix representation and restricts coordinate conjugation to the
span of the matrix and inverse-matrix values of `H`. Density extends the
restricted action from the subgroup to an actual representation of `G`.
Its full scheme kernel is the center. The normalizer preserves a bounded
spanning family in the restricted space, so the whole family of its matrices
has bounded entries. Inversion in the normalizer also bounds inverse entries,
giving algebraic boundedness of its actual general linear image. Descent
through `q` is a closed embedding by the full kernel identification, so
reflection of algebraic boundedness bounds the actual adjoint image.

The second input is
`isAlgebraicallyBounded_adjoint_preimage_inter_normKernel`. A quotient by the
actual derived subgroup gives a torus `Q`. The joint morphism from `G` to
`A × Q` is finite: its kernel is the finite full central intersection with the
derived subgroup. Rational-character pullback carries the common norm kernel
of `G` into that of `Q`, and the latter is compact over the local field. Thus
the product of a bounded adjoint set and this torus norm kernel is bounded.
Pullback along the finite joint morphism proves the required boundedness of
the adjoint preimage inside the common norm kernel. The final reduction uses
monotonicity to bound the requested normalizer intersection.

This proof uses no unproved statement as an additional premise. It supplies
neither building data nor an extra hypothesis on `H`. The protected statement
and its imported Lean/Markdown pairs are unchanged.

The target is the local-field case of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 2.2.16, printed
pp.77–78 / PDF pp.108–109, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The implemented bounded-spanning-family proof replaces the source's
eigenvalue argument and its use of Lemma 2.2.15. The November 2024 corrections
contain no entry numbered 2.2.16.
