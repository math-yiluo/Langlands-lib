# Canonical discrete-series coefficients of projected function representations

This derived module connects the representation-theoretic argument in Waldspurger
(2003), Theorem VIII.4.2, printed pp.330–331 (PDF pp.96–97), to the Library's
canonical discrete-series coefficient sum. All positive-form and coefficient-L²
assumptions remain explicit auxiliary inputs.

An actual irreducible square-integrable subrepresentation is bundled as an
irreducible admissible smooth representation and sent to its actual
`DiscreteSeriesClass`. The published representative-transport equality identifies
its coefficient space with that of the canonical `Quotient.out` representative.
Its central action descends to `classActsByCharacter`, so its coefficients
belong to the canonical discrete-series sum.

For a smooth admissible representation with an invariant positive form and
square-integrable form coefficients, the published unitary semisimplicity and
square-integrability arguments apply. Every smooth coefficient is a finite
algebraic sum of coefficients of irreducible subrepresentations. Transporting
those coefficient spaces as above places the whole coefficient space in the
canonical sum.

Actual carrier lifts preserve irreducibility, admissibility, square
integrability, central action and coefficient spaces. The resulting inclusion
of the original canonical sum in the sum with lifted carriers supplies the
`max uG uW` carrier convention, with group and enlargement universes independent.

`projectedEvaluationAtOne` is the literal evaluation functional on the projected
left-level function representation. Left invariance under the prescribed open
subgroup makes this functional smooth for the dual right action. Each vector
is then its own matrix coefficient against this evaluation functional. Applying
the preceding canonical coefficient theorem gives its membership in the
discrete-series sum once the actual positive form, admissibility and
coefficient-L² inputs have been supplied. This implementation uses smooth
evaluation directly instead of constructing the source's reproducing vector.
Both the original-carrier and enlarged-carrier conclusions are proved.

No analytic input is proved here, and neither closed VIII.4.2 target
(`RationalCuspidalDiscreteCoefficientStatement`, `RationalCuspidalFixedCoefficientLiftingStatement`)
follows without those inputs. The central Haar measure is unchanged throughout.
