# Spherical lower bound in the actual standard Levi

`Langlands.HarishChandraSchwartz.rationalLeviXiLowerBound` proves
`RationalLeviXiLowerBoundStatement.{u}`. Given the compact open subgroup
`K` with the Levi Iwasawa decomposition, the proof chooses an ambient
basis member `H` contained in `K` and in every preimage of `K` under
`x ↦ f⁻¹ x f` for `f ∈ F0`. These preimages are identity neighborhoods
by continuity. Finiteness of `F0` permits one choice of `H` for all the
representatives.

On the canonical Levi scheme, `hasIwahoriIntersectionDecomposition_leviScheme`
restricts the minimal Iwahori factorization to the preimage of `H`.
Inverting the ordered factorization puts the minimal parabolic factor
first and the opposite radical last. For a uniformizer point in the
`J`-chamber, the corresponding cocharacter lifts through the compatible
minimal split component because the annihilation conditions for the empty
face are vacuous. The pairing formula under restriction of characters and
the intrinsic Levi simple-root identity place its image in the intrinsic
weak chamber. The published `weakChamberContraction_leviScheme` transfers
ambient contraction to that chamber by a central cocharacter shift.
For a representative `f i(a)`, the factors commute. Inverse conjugation
therefore applies the chamber contraction first and then applies
`x ↦ f⁻¹ x f`. The defining containment for `H` puts the resulting
point in the preimage of `K`.

`xiLowerBound_of_factorization` applies to this open subgroup in the
canonical Levi scheme. The proof uses `iwasawaWeight_map` and
`rationalXi_leviScheme` to read the resulting estimate on the actual
standard Levi subgroup of `G(F)`. Positivity of `rationalLeviXi` allows
the bound's constant `C` to be increased to `max C 1`.

The argument follows the lower-bound proof in Lemma II.1.1 of
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), printed p. 251. The choice of a single
basis member for the finite translates and the transport to the full
standard-Levi chamber are derived adaptations. The registered source is
`waldspurger-2003-plancherel` with SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
