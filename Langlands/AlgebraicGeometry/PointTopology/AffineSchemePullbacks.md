# Actual affine-scheme pullbacks and coordinate-algebra pushouts

Author: Worker 105.

This is derived infrastructure for the affine fibre-product and uniqueness
assertions in Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Proposition 2.1 and its proof, printed
pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`algebraSpectrumPullback` is the cone of actual schemes over `Spec R`
obtained from an arbitrary coordinate-algebra pushout cocone by taking
the spectra of its actual algebra maps. Its universal property
`algebraSpectrumPullbackIsLimit` holds in the full category of schemes
over `Spec R`, including tests by nonaffine schemes.

In the other direction, `affineCoordinatePushout` applies the actual
global-section algebra maps to a cone of affine schemes over `Spec R`.
For a limit cone, `affineCoordinatePushoutIsColimit` constructs the
pushout universal property of these actual algebras with their specified
base structures.

The proof uses the equivalence between commutative `R`-algebras and rings
under `R`: forgetting the base preserves and reflects pushouts, which
are connected colimits. Mathlib's spectrum functor takes ring pushouts
to scheme pullbacks and reflects limits by full faithfulness.
For arbitrary affine schemes, naturality of the canonical global-section
spectrum isomorphism transports the actual cone. Forgetting from schemes
over the base creates connected limits and therefore preserves and
reflects pullbacks. All these universal properties are constructed,
not supplied as extra comparison hypotheses.

No finite type, topology, Hausdorffness or locality is required.
The constructions do not assert any topological comparison or complete
the scheme-topology characterization; those use this infrastructure
in separate statements and proofs.
