# The zero-plus term and the connected Néron radical

`minimalCongruentZeroPlus` proves `MinimalCongruentZeroPlusStatement`
over `inertiaFixedField F`, with models over `fixedFieldIntegers F`.
It identifies the minimal congruent zero-plus term with the strictly
positive standard union inside the connected Néron points and with
the reduction preimage of the unipotent radical of the connected
Néron special fibre.

`exists_standardZeroPlus_radicalPreimage` supplies the radical and
the standard-group equality. Any positive minimal congruent depth
can be truncated to strictly positive shallow depth by antitonicity.
There the first congruence kernel reduces to one, and standard
functoriality puts every induced generator in the radical preimage.
The opposite inclusion follows because each section reducing into the
radical is in a positive shallow induced image by
`exists_standardZeroPlus_radicalPreimage`.

The smooth model is the actual dilatation of the connected Néron
model along the radical.
`IntegralModel.dilatationStructure` gives smoothness and
`IntegralModel.integralPoints_dilatation` identifies its integral
points. `IntegralModel.range_dilatationIntegralSections` and
surjectivity of Henselian reduction show that the image of the
special-fibre map lies in the radical on rational points.
`SubgroupFunctor.exists_factor_of_algClosed_points` factors the
scheme map through the radical. Lifting a radical point to an integral
section and then to the dilatation proves surjectivity on rational
points. The image of the factor map is constructible by Chevalley's
theorem. A nonempty constructible complement would contain a closed
point by the Jacobson property, and over the algebraically closed
residue field that point would be rational. This proves scheme
surjectivity.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Lemma B.10.11 and Proposition B.10.12, printed pp. 690–692,
PDF pp. 721–723. The standard radical input is Proposition B.9.1,
printed pp. 684–685, PDF pp. 715–716, and the model uses §A.5.
The book is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
