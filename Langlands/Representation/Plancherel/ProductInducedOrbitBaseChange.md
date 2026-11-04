# Base-object independence of actual smooth orbit sections

This module proves a derived comparison needed for Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
VI.1, printed pp.295–296 (PDF pp.61–62), DOI 10.1017/S1474748003000082.
There the sections are defined on actual representatives, are compatible with
canonical transport between equivalent representatives, and are tested for
smoothness by fixing one representative and restricting its unitary character
family to a compact picture. The present construction proves independence of
that fixed representative for the actual smooth-section model implemented in
`ProductInducedOrbitSections`.

The group, norm-family index, representation carrier and torus-coordinate
universes are independent. All actual inducing objects have the same fixed
carrier universe; their vector spaces need not be equal. The inputs are a
nonarchimedean locally compact topological group G, a subgroup M, indexed
positive characters on M, and a canonical irreducible admissible smooth complex
representation pi of M. The new base A is an actual representative in pi's
unitary unramified twist orbit. Compact restriction additionally uses an actual
semidirect decomposition P = M U, closed P and U, compact open K, continuous
positive characters and Levi projection, and the actual factorization G = P K.
The smoothness comparison uses a supplied multiplicative identification of the
unitary unramified characters with a finite coordinate torus. All these inputs
remain explicit. No irreducibility of a parabolically induced representation is
assumed.

The source has a discrete-series orbit. The Lean construction works for the
stated irreducible admissible inducing objects and their actual unitary orbit.
It does not establish that the full class stabilizer is unitary. The finite
scalar-smooth convention is the algebraic tensor convention of
`SmoothTensorFamilies`; no coefficient-space topology is introduced here.

`unitaryOrbitRepresentative_mem_iff` proves that recentering at A gives the same
actual objects. If chi sends pi's class to A's class, then eta sends A's class
to B's class precisely when eta chi sends pi's class to B's class. The reverse
implication uses eta chi inverse and cancellation in the actual unramified
character action on `SmoothDualClass`. This is a proof from A's membership,
not an assumed orbit comparison.

`unitaryOrbitRepresentativeBaseEquiv` retains the actual object B and changes
only its orbit-membership proof. Its inverse has the same property.
`productInducedOrbitBaseEquiv` reindexes the dependent section space by this
index equivalence. Its forward and inverse maps retain every section value in
the same actual normalized product-induced coefficient fiber. The theorem
`productInducedOrbitBaseEquiv_coherent_iff` preserves and reflects coherence
under every actual inducing equivalence, by applying the old coherence law to
the unchanged objects.

`unitaryTorusParameter_mul` records that coordinate multiplication corresponds
to multiplication of the actual characters. For a parameter z0 and any actual
equivalence a from pi twisted by its character to A,
`productInducedOrbitCompactPullback_baseChange` proves the pointwise equality

    R_A(q_reindexed)(z) = T_a(R_pi(q)(z z0)).

Here R is actual normalized compact restriction of the section's value at the
literal parameter representative. The fixed map T_a is
`productCompactBaseChangeEquiv` for the character at z0. The section q needs
coherence but no smoothness for this square. The proof first packages R_pi as
a function of a unitary character, so multiplication can be rewritten without
changing a dependent fiber separately from its section value. Coherence then
identifies the two actual section values by the variable equivalence
`productBaseTwistEquiv`. The existing actual normalized restriction square
`productInducedCompactBaseChange` completes the equality. Its coefficient map
retains transport of vectors and inverse pullback of smooth functionals.

For `productInducedOrbitBaseEquiv_smooth_iff`, coherence is already equivalent.
A's membership supplies one z0 and one a for the displayed square. Torus
translation preserves and reflects finite scalar-smooth expansions, and a
fixed compact linear equivalence preserves and reflects those expansions by
acting on their constant coefficient vectors. Applying the two results from
`FiniteSmoothFamilyTransport` proves equivalence of the actual compact
smoothness conditions. Neither the desired smoothness comparison nor a descent
equivalence is an input.

`productInducedSmoothOrbitBaseEquiv` restricts the actual-object reindexing to
the smooth coherent subspaces. The three evaluation lemmas give its value at
an arbitrary target representative, its value at the reindexed original
representative, and its inverse value at every original representative. In
particular both directions fix the actual fiber value. The resulting map
contains no chosen realizing character or inducing equivalence in its data;
those choices are used only in the proof of smoothness. Different realizing
characters may give different fixed compact maps, because self-twists may act
nontrivially. Independence of the section comparison follows from its
actual-object reindexing and the proved coherence square.

This construction establishes conditional base-representative independence for
the supplied torus coordinates. Finite integer changes of these coordinates
are treated separately in `ProductInducedOrbitCoordinates`. Arbitrary abstract
torus equivalences, the discrete-series full-stabilizer comparison, rational
reductive realization, comparison with the source's Levi-inflated
normalization, and analytic Plancherel remain separate obligations.
