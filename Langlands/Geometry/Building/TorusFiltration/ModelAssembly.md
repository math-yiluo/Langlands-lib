# Integral models of the minimal congruent torus subgroups

`minimalCongruentModelFromDilatation` constructs a smooth affine model
with geometrically connected fibres and the exact subgroup
`minimalCongruentPoints` at each nonnegative real depth. The base is
`O = fixedFieldIntegers F`, where `F` is a nonarchimedean local field and
`K = inertiaFixedField F`. The construction takes three inputs.

* The positive-depth standard subgroups of induced `K`-tori below depth
  one have smooth models with geometrically connected fibres.
* A smooth connected closed subgroup of the special fibre of the connected
  Néron model defines a smooth connected dilatation. Its points are the
  image in `T(K)` of the reduction preimage of the centre's rational
  points.
* Each smooth connected model has positive integer congruence models
  with smooth geometrically connected fibres and the exact points
  `IntegralModel.congruenceSubgroupAt`.

The definition takes the connected Néron model at depth zero. For a
shallow positive depth, every induced-torus map extends from its standard
model into the connected Néron model by smooth extension on integral
points. Consequently each generator of the shallow subgroup has
reduction in the image of an actual special-fibre homomorphism.
Surjectivity of reduction for the standard models gives equality with
those rational-point images. The first congruence subgroup is included
in the generated shallow group, so the group is the full reduction
preimage of the generated residue subgroup.

The residue field of `O` is algebraically closed. Among the smooth
connected closed groups constructed from finite subfamilies of the
special-fibre maps, the proof chooses one whose prime coordinate kernel
in the ambient affine ring has the least height. Adding one more index
gives a containing closed subgroup by rational point detection for
closed immersions. The coordinate-kernel height for the larger group
cannot decrease by the choice of the original subfamily, so the inclusion
is an isomorphism. Thus the chosen finite subfamily already generates
the full group of points and identifies the actual closed centre for
the dilatation.

For a depth at least one, the construction obtains the model at
the fractional part as above and applies the integer congruence
construction at the floor of the depth. The integral-point
identification is `minimalCongruentPoints_add_pnat`.
`minimalCongruentPlusSubgroup` forms the subgroup supremum of the
strictly greater terms. Its underlying set is the strict-depth union
when the terms decrease with depth.

See Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Definition B.10.8 and Lemma B.10.9 (printed p. 690 / PDF p. 721)
give the model recipe. Proposition B.3.6(1) (printed pp. 658–659 /
PDF pp. 689–690) gives the induced standard models. Lemma A.5.10,
Definition A.5.12 and Lemma A.5.13 (printed pp. 635–637 / PDF pp. 666–668)
give the smooth dilatation and congruence inputs. Definition B.5.2
(printed p. 667 / PDF p. 698) gives the strict-depth union convention.
The correction specifying induced `K`-tori is in
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p. 50,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
