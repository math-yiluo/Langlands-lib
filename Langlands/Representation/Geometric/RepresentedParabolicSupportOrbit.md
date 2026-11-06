# Actual orbit pieces of represented parabolic induction

This internal construction identifies the actual support quotients of
normalized induction from a represented parabolic with the compactly induced
stabilizer representations of their orbits. Its namespace is
`Langlands.Aubert.General.RepresentedParabolic`.

It implements the orbit-identification portion of Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.5.1:
the support quotients on printed p.163 / PDF p.169 and their identification
with induction from the orbit stabilizer on printed p.171 / PDF p.177.
The construction composes the Library's generic compact-to-smooth support
comparison and independently proved closed-subgroup Mackey comparison.
It does not apply the target-radical coinvariants or identify normalized
geometric-lemma pieces.

The source is a smooth complex representation of the Levi's own rational
points, with its canonical topology. `isSmooth_leviInducingFunctor_obj`
proves that its inducing covariance on the literal parabolic point image
is smooth. Pullback along the Levi-point homeomorphism preserves smoothness.
The actual semidirect Levi projection is continuous by
`continuous_projection_pointImage`, so inflation is smooth as well.
Finally the positive half Haar character has open kernel, and scalar
twisting therefore preserves smoothness.

`smoothLeviInducingFunctor` bundles these same covariance representations
and their original morphisms in the full smooth category of the parabolic
image. Forgetting smoothness recovers `leviInducingFunctor` exactly.
There is no admissibility or other representation finiteness premise.

`leviInductionSupportCompactIso` assumes compactness of the actual source
parabolic quotient. At every grade of a supplied ordered double-coset cover
it identifies compact induction's support quotient with the corresponding
quotient for the actual normalized smooth induction. The underlying
comparison is the canonical compact-to-smooth inclusion, which retains
the function and its support. It is precomposed with the just-proved
smooth inducing covariance.

`leviInductionSupportOrbitIso` additionally assumes that the ambient point
group is Hausdorff and sigma compact, and takes the target represented
parabolic. The closed-subgroup Mackey theorem applies because both
parabolic point images are closed. Whiskering its natural graded
isomorphism with `smoothLeviInducingFunctor` and composing with the inverse
compact-to-smooth support comparison gives the displayed result.

The ordered-cover convention indexes the orbit of
`P(s.representative i)⁻¹` in `P\G`. Accordingly the stabilizer and its
conjugated covariance in `orbitPiece` refer to this same orbit; there is
no change of representatives or order.

The field and representation carrier universes are independent. The
ambient composite and compact orbit pieces have carrier universe
`max u v`. Compactness of the actual parabolic quotient remains an explicit
input of these comparison constructors. Hausdorffness and sigma
compactness can be derived for the full geometric lemma's canonical
reductive point topology by the existing rational-point results; this
module does not add them as premises to that closed statement. It neither
proves quotient compactness nor the normalized support-grade proposition.
