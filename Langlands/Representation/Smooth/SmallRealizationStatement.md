# Small realizations of irreducible smooth p-adic representations

Authors: Worker 195 and Worker 82. Worker 195 formulated the isolated target;
its derived proof route follows Worker 82's published Levi-exhaustion rationale.

`Langlands.PadicIrreducibleSmoothSmallRealizationStatement.{uF,uW,uV}`
is a closed proposition definition. For every prime `p`, every actual finite
extension `F : PadicField.{uF} p`, every supplied realization
`T : F.TopologicalData`, and every rank `n`, it asserts that an irreducible
`π : SmoothRep.{0,uF,uW} ℂ (GeneralLinear n F.Carrier)` has an equivalent
irreducible smooth realization with carrier in `Type uV`. The topology is
exactly `T.topology` on both sides.

The conclusion provides an actual object
`σ : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)` and a
`Nonempty (π.representation.Equiv σ.representation)`. Thus it supplies an
equivariant complex-linear equivalence between the actual carriers, rather
than equality of class names or an assumed resizing operation. Irreducibility
excludes the zero representation. The field universe `uF`, original carrier
universe `uW`, and new carrier universe `uV` remain independent. There is no
admissibility, cardinal-bound, countable-dimension, or smallness hypothesis.
Rank zero is included.

## Derived provenance and proof obligation

This is an internal, derived existence target needed by the published
`CuspidalSupport.PadicLeviCuspidalFactorizationStatement` and ultimately
`GLSupercuspidalEmbeddingStatement`. It isolates the small-realization
obligation explained in the Markdown of
`CuspidalSupport/LeviTensorFactorizationStatement`. It is not a transcription
of a theorem about Lean universes from the representation-theory literature.

A mathematical route to its proof is as follows. The certificate
`T.moduleTopology` identifies the supplied topology with the finite-dimensional
`ℚ_p`-module topology. A finite basis therefore identifies the field
topologically with a finite power of `ℚ_p`. Second countability then passes to
finite matrix spaces and the general linear group. In an irreducible smooth
representation, a nonzero vector has open stabilizer. The corresponding
discrete coset space is countable, so the orbit of that vector is countable.
Its complex span is invariant and nonzero, hence is the whole representation.
Choose a basis from this countable spanning set and index it by a subset `I`
of `ℕ`. The carrier `I →₀ ℂ` lies in `Type 0`; lifting it to `Type uV` and
transporting the action gives the requested realization. Smoothness and
irreducibility transfer along the resulting actual equivalence.

These steps are proof obligations, not results proved or assumed in this
module. Countability here concerns a spanning set, not the complex scalars
or the set of vectors. Neither admissibility nor a tensor factorization theorem
is required by this route.

For the Levi-exhaustion consumer, once a block factor is realized in `Type uV`,
the published `GeneralLinear.isSupercuspidal_of_equiv` transfers its
supercuspidality across the same equivalence, including admissibility and
vanishing for all conjugate unipotent radicals. Existence of the tensor
factorization and the assembly of factor equivalences remain separate
obligations. This statement proves neither that exhaustion result nor the
supercuspidal embedding theorem.
