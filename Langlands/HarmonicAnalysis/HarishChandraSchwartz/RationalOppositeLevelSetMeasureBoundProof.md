# Waldspurger II.4.1 on the actual opposite radical

`rationalOppositeLevelSetMeasureBound` proves the published
`RationalOppositeLevelSetMeasureBoundStatement` at universe `u`. The proof
uses a compact part of the open cell to get the spherical lower bound needed
for each level. The source uses its integral formula (2) on the whole cell.

Normalize ambient Haar to give the compact open Iwasawa factor `K` mass one.
The average over `K` is then the ambient integral with the indicator of `K`.
The local Haar formula for `p v⁻¹` restricts this integral to a box in `K`.
Its parabolic coordinate `p` lies in `K` and has Levi projection `m` in `K`.
This condition defines a compact open neighborhood of the identity in the
parabolic. The opposite coordinate belongs to the compact open subgroup of
the opposite radical cut out by `K`.

Let `a` be a power of the cocharacter at the uniformizer, and let `E` be a
measurable level with half-weight `r`. The proof arranges that `a⁻¹ E a` lies
in `K`. For each parabolic coordinate, it restricts the opposite coordinate
to the preimage of `E` under `v ↦ (a m) v⁻¹ (a m)⁻¹`. The preimage lies inside
the compact box. Inversion preserves opposite Haar. Conjugation by `m`
preserves the compact subgroup of the opposite radical and has modulus one.
Opposite Haar reciprocity and centrality of `a` in the Levi give the preimage
measure `δ₀(a) μ(E)`. The integrand in the spherical average at `a⁻¹` equals
`δ₀(a⁻¹)^(1/2) r` on this preimage by the Iwasawa weight laws. Consequently
`Ξ(a) = Ξ(a⁻¹)` bounds a fixed positive multiple of `δ₀(a)^(1/2) r μ(E)`.

The chart-entry lemma takes the power to be `n + b` for level `n`, with one
natural number `b` for every level. It uses the inverse-weight contraction
estimate, the modulus-height comparison, and uniform contraction on a compact
height sublevel. The powers lie in the weak minimal chamber by the simple-root
pairings of a standard cocharacter. The actual spherical upper estimate on
these powers has the same half-modulus factor. Subadditivity of logarithmic
height bounds its polynomial factor by a constant times `n^d` for `n ≥ 1`.
Canceling the common half-modulus and dividing by `r = q^(-n/2)` gives the
required volume bound. The proof works with the supplied Haar measure and
uses the simultaneous standard basis for the spherical upper estimate.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d’après Harish-Chandra* (2003), Lemma II.4.1, printed pp. 259–261.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
