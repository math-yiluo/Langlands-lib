# Actual pointed product actions and tensor weights

For a field `k : Type u`, an actual commutative group scheme `S`, and pointed
actions on schemes `V` and `W` over `k`, `PointedAction.prod` constructs the
componentwise action on the actual fiber product, with the pair of distinguished
points as origin. Its identity, multiplication, fixed-origin and projection
laws hold on every test scheme. The construction needs no group structure on
`V` or `W`, and no split-torus hypothesis.

When both structure morphisms are affine, `prod_isAffineHom` supplies affineness
of the product. `tensorPresentation` identifies the spectrum of
`Coord V ⊗[k] Coord W` with the actual product using the affine-spectrum product
comparison and the two chosen coordinate presentations. Its map is the pair of
the two universal input points after scalar extension to the tensor algebra.
Full faithfulness of affine spectrum then gives the algebra equivalence
`tensorCoordinates` from the actual product coordinates to that tensor algebra.

The projection pullbacks correspond to `x ⊗ 1` and `1 ⊗ y`.
Consequently `tensorCoordinates_symm_tmul` identifies the inverse image of
`x ⊗ y` with the product of those two projection pullbacks. These are statements
about the actual chosen coordinate presentations, rather than a separately
postulated tensor grading.

`tensorWeightSpace a b χ` is the image of the actual product eigenspace of
character `χ` under `tensorCoordinates`. The theorem
`tmul_mem_tensorWeightSpace` proves that a pure tensor of eigenfunctions of
characters `α` and `β` lies in character `α + β`. The proof evaluates the
product of projection pullbacks on every coefficient algebra and every pair of
points. The componentwise action laws give the two eigenfunction equations;
character addition multiplies their character values. This uses the positive
pullback convention from `PointedCoordinateAction`.

This is an internal construction for the coordinate-tensor step in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma 3.3.4 and its proof, printed pp. 108–109 / PDF pp. 134–135.
The product-presentation argument generalizes the affine commutator product
presentation. It supplies no decomposition of the coordinate or augmentation
spaces, tensor support bound, image support theorem, Lie comparison, or proof of
`SemigroupCommutatorStatement`.
