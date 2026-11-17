# Actual Weyl indices and lower subgroup functors for the weak expansion

This is the first definition unit for the weighted weak constant term expansion.
It introduces `Langlands.HarishChandraSchwartz.WeakExpansion.WeylIndex` and
the actual lower subgroup functors. It does not assert the expansion or
regularity of any intertwining family.

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques*, DOI 10.1017/S1474748003000082, V.1, printed pp.287–289,
especially the definition on p.288:
“W(M′|G|M) = W^{M′} \ W(M′|G|M)”.
Here the set on the right is the set of Weyl elements carrying `M` into
`M′`. We use the published quotient `relativeWeylGroup i = N_G(T)(F)/Z_G(T)(F)`,
with the actual standard Levi subgroup functors. The containment defining
`admissibleWeylElements` is an all-test subgroup-functor containment.
`lowerWeylSubgroup` is the image of the actual normalizer points lying in
`M′(F)`, under the published Weyl quotient homomorphism. `weylIndexSetoid`
restricts the relation of left multiplication by that subgroup to the
admissible elements. In Mathlib's coset terminology this is `rightRel`;
`weylIndexMk_eq_iff` explicitly checks the direction: `v w⁻¹ ∈ W^{M′}`.
The quotient may be empty. Its finiteness follows from the imported actual
reductive Weyl-group finiteness theorem.

The source subsequently identifies this quotient with a representative
system. `Representatives` records both the Weyl representatives and their
actual normalizer lifts, with the containment witness for every lift.
`representatives` chooses one such system. Later analytic objects must take a
system explicitly, so the choice is visible. Equality of normalizer lifts'
Weyl classes gives equality of the conjugated Levi functors by the published
`standardLeviConjugation` theorem. Consequently admissibility is independent
of that lift. Independence of the expansion from the choice of a
`W^{M′}`-representative requires the later coefficient and measure agreement
targets; this file proves no analytic representative independence.

`conjugatedLevi`, `conjugatedParabolic` and `conjugatedUnipotent` use preimage
under the inverse of the scheme inner automorphism, hence denote the forward
conjugates `nM_In⁻¹`, `nP_In⁻¹` and `nU_In⁻¹`. The rational-point formulas
reuse the published conjugation adapters and fix this direction explicitly.
The lower ambient group is the actual scheme
`Standard.leviScheme i ν I′`; the three lower functors are the preimages of
these conjugates under `Standard.leviHom i ν I′`. Thus `lowerParabolic`
is precisely `M′ ∩ nP_In⁻¹`, the semistandard parabolic in the V.1 formula.
It is not replaced by a standard parabolic of `M′`. The displayed containment
lemmas are formal consequences of the original standard containments.

These are constructions over arbitrary fields, without a characteristic or
split-group restriction and without a representation universe. The later
unit must supply the dynamic model of the lower parabolic, the conjugated
representation and orbit, source-normalized measures, and density packages.
V.2.2–V.2.3 (pp.293–294) and VI.3.1's weak-part argument (pp.303–305)
use coefficients and packets on this lower ambient group; those analytic
definitions and their Prop-valued targets are separate. We use no transport
to standard lower data and make no assertion about V.3.1's normalized
intertwining operator in this unit.

`lowerWeylSubgroup` abbreviates the existing `standardRelativeWeylGroup`.
