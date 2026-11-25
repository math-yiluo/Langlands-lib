# Invariant lifts inside translation-stable ideals

This derived supporting module combines finite stable covariant families with
geometric reductivity. Its inputs are the published finite regular-span
construction, rational detection of actual fixed vectors, and normalized
homogeneous separation. Geometric reductivity remains an explicit hypothesis
on the subgroup; this module does not establish it or quotient affineness.

`scalarPreimage` is the ground-field subspace of elements whose image under an
algebra map is a scalar. The membership lemma expresses this as the existence
of a scalar c whose algebra-map image is the given image.

`IsRightCovariantFamily.dual_fixed_of_scalar_images` works over an algebraically
closed field with a smooth subgroup. Suppose the images of the actual sections
f_j under an algebra map to a nontrivial algebra are scalars c_j and those
images are preserved by every rational right translation. Then c is fixed by
the actual dual representation on every relative scheme test. Specializing
covariance to the universal ambient point and a constant inverse subgroup point
gives the inverse-transpose identity after applying the algebra map. Injectivity
of the scalar map recovers that identity over the field. The published rational
fixed-vector criterion upgrades it to the all-test assertion.

`exists_invariant_mem_ideal_image_one` assumes additionally that the ambient
group is affine and the subgroup is geometrically reductive. Let I be an ideal
of the actual global section algebra stable under rational right translations.
Let phi map this algebra to an arbitrary nontrivial ground-field algebra.
Assume that rational translations preserve the image of every element in the
scalar preimage of phi, and that some s in I has image one. Then there is an
element t in I which is right invariant on every relative scheme test and
whose image is one.

The proof takes W to be the intersection of I with the scalar preimage.
The stated assumptions make W stable under rational translations. Smoothness
gives reducedness of the subgroup, so finite stable-family existence applies
to s. The scalar images of the resulting family supply c. It is nonzero,
since otherwise the linear combination giving s would have image zero.
The preceding lemma makes c dual-fixed. Geometric reductivity supplies a
positive-degree homogeneous transpose-invariant polynomial normalized at c.
Evaluating it in the family lies in I, is invariant on every relative test,
and maps to one, by the previously established ideal and power-lifting formulas.

`exists_invariant_separating_ideals` specializes this to two rationally
translation-stable ideals I and K with I + K equal to the whole section ring
and K proper. It gives an all-test invariant t with t in I and t - 1 in K.
The map is the quotient by K, which is nontrivial because K is proper.
If a section has scalar image c, its difference from c lies in K; translating
that difference proves that the image stays c. A comaximality certificate gives
the element s mapping to one, so the preceding lift theorem applies.
