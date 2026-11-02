# Linear systems and change of coefficient ring

For a commutative algebra `A` over a commutative ring `R`, and generating
sections of a line bundle on any scheme over `Spec A`, this derived development
proves that the actual linear-system morphism commutes with the polynomial
coefficient morphism `ProjSpace.map R A n`. All rings and schemes have the
same arbitrary universe, and `n` is any natural number.

The proof first identifies the maps on global scalars under a composite
structure morphism. The chart polynomial evaluation maps then agree after
the graded coefficient map: constants agree by this scalar naturality and
variables give the identical section ratios. The existing
`chartMap_comp_projMap` theorem gives functoriality of the actual affine chart
morphisms. Its dependent chart data are identified by the coefficient map's
formula on variables, and `chartMap_ringHom_congr` identifies the evaluation
maps. A cover by the generating sections' frame opens gives equality of the
glued scheme morphisms.

Specializing the coefficient ring to `ULift Int`, with its canonical algebra
structure on `K`, proves `linearSystemMap_comp_polynomialToIntegral`: the
polynomial linear-system map followed by the existing coefficient morphism
to the integral model is exactly the integral linear-system map. Terminal
uniqueness identifies the structure maps to `Spec (ULift Int)`. This also
proves `relativeLinearSystemMap_toPolynomial`, by checking both projections
of the pullback defining relative projective space over `Spec K`.

For the actual coordinate sections on polynomial projective space,
`integralLinearSystemMap_projectiveCoordinates` now identifies their integral
linear-system morphism with the existing `polynomialToIntegral K n`.
It uses the proved polynomial coordinate identity, not a comparison assumption.
The definition `polynomialIntegralTwistIso` transports the existing
section-preserving `linearSystemTwistIso` along this equality. Its source is
the actual pullback of the integral degree-one twist along
`polynomialToIntegral K n`, and its target is the actual polynomial twist
`twistOne K n`. The theorem `polynomialIntegralTwistIso_coordinate` proves
that it sends every pulled-back integral coordinate section to the
corresponding polynomial coordinate section. Its proof uses section
compatibility with equality transport and the actual linear-system twist
comparison's coordinate formula.

The provenance is derived from the imported constructions, chart functoriality,
coordinate identity and twist comparison. There is no new external-source
assertion. This focused unit supplies the coefficient and twist bridge used
in subsequent relative projective constructions. The glued tautological
line bundle and the ordinary large-level moduli representability theorem
remain further obligations.
