# Small-level rigidity for the normalized CM moduli problem

`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.cmSmallLevelRigidity` proves
`CMSmallLevelRigidityStatement` with its original datum, signature charts,
universes, and prerequisites. At every sufficiently small original Harris
level, a rational self-isogeny of an admitted polarized CM object which scales
the polarization and fixes the level orbit is the identity.

The proof applies `cmRigidityFromPolarizedAutomorphismFiniteness` to
`Langlands.AbelianScheme.polarizedAutomorphismFiniteness.{0}`. The latter
uses the positive Rosati trace form on the finite free integral endomorphism
lattice. Preservation of the polarization fixes the diagonal value of this
form, so the polarized automorphism subgroup embeds in a finite sublevel set.

The rigidity reduction starts with the frame equation supplied by orbit
fixedness. Compactness gives `q² = 1` for the rational multiplier `q`.
Intersecting the compact level with the open stabilizer of the integral
frame lattice gives a finite-index subgroup. A positive even power of
the self-isogeny thus preserves that lattice in both directions. The lattice is
realized by an isogenous abelian scheme, and the power becomes an integral
automorphism preserving the transported polarization on that scheme.
Finiteness supplies a positive power equation in the polarized subgroup.
The subgroup inclusion, rationalization, and conjugation transfer finite
order to that positive power, hence to the original rational self-isogeny.

The frame equation transfers finite order to the local image of the level
element at the place witnessing smallness. Smallness forces that image to
be trivial, so the rational Tate operator is the identity there. The
published `fieldPrimeRationalFaithfulness` theorem at that prime then gives
identity of the underlying rational homomorphism, and extensionality gives
identity of the self-isogeny.

The proof composes the published rigidity reduction and the published
polarized automorphism finiteness theorem. The target Markdown records the
original Harris–Taylor and Kottwitz source passages.

Proof by Worker 335.
