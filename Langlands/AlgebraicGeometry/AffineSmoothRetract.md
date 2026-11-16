# Smoothness of affine retracts

`AffineRetractGeometry.SchemeRetract X Y` is the type of a section `Y ⟶ X`,
a retraction `X ⟶ Y`, and their composite identity on `Y`, all over a common
base scheme. It packages scheme retraction data without imposing a group law
or affine hypotheses. Its `smooth` theorem applies when both structure maps
are affine and the structure map of `X` is smooth.

This internal support result removes the noetherian assumption from the affine retract smoothness argument in `GroupScheme.SplitKernelRetractGeometry`. Formal smoothness descends to an algebra retract by the existing `DynamicSmooth.formallySmooth_of_algSpec_retract`. Finite presentation descends by the published `Algebra.FinitePresentation.of_retract` in `RingTheory.Grassmannian.ProperFinitePresentation`. Together these give smoothness over every ring. The equivalence between affine schemes over `Spec R` and opposite `R`-algebras transports the argument to affine schemes. Restricting to the base's affine open cover proves `smooth_of_retract_anyBase`.

Both schemes in the last theorem must be affine over the base. The retraction maps are morphisms over that same base. No noetherian, reducedness, or field hypothesis is used.

For the ring case the contravariant affine equivalence turns `i ≫ r = 𝟙` into an algebra retraction. The finite-presentation theorem applies to these two algebra maps with their exact composite identity; the formal-smoothness theorem applies to the original scheme maps. For arbitrary affine schemes, the chosen affine equivalence isomorphisms conjugate the two maps to maps between algebra spectra. Smoothness and the retraction identity transport along these isomorphisms.

For a general base, the proof pulls both schemes and both maps back to each affine open of the base. Affineness and smoothness persist under this pullback, and functoriality preserves the retraction identity. The ring-case theorem applies on every chart, and target locality of smoothness gives the conclusion. As in `Dynamic.BaseSmoothConnectedProof`, the module sets `backward.isDefEq.respectTransparency false` to allow Lean to synthesize the target-locality instance.

This is a derived internal support result for relative dynamic subgroup geometry; it does not establish the derived-group parabolic correspondence by itself.
