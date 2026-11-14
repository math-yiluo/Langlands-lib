# Integral cocenter cocharacter exactness

This internal helper develops the cocharacter-kernel argument behind the
identification of the algebraic fundamental group with that of the cocenter for
a group with simply connected derived group. It supports the construction in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), §11.5 before
Lemma 11.5.1, printed pp. 429–430 / PDF pp. 460–461.

For a chosen maximal torus and simply connected derived cover, simple
connectedness of the full derived group makes the covering morphism an
isomorphism. Consequently its ambient composite presents the full derived
subgroup. A supplied cocenter is a full fppf quotient by that subgroup.

`cocenterIntersectionKernelIso` reverses an actual subgroup intersection and
uses the published kernel/intersection comparison. Applying it to the chosen
cover and maximal torus gives `scTorusCocenterKernelIso`: the chosen preimage
torus is the full kernel of the restriction of the supplied cocenter quotient.
The comparison respects the actual inclusion into the maximal torus.
`scTorusCocenterKernelBaseChangeIso` transports this comparison through an
arbitrary field extension using the actual kernel base-change isomorphism.

Finally, `cocenter_cocharacter_eq_zero_iff` uses the universal property of this
full kernel on actual cocharacters. It identifies the kernel of geometric
cocharacter postcomposition with the chosen `corootImage`. This is integral
exactness; no saturation, tensoring with a field, coroot basis, or removal of
torsion occurs.

`cocenter_cocharacter_surjective` transfers the published cocenter quotient's
integral cocharacter surjectivity to every supplied actual cocenter, over any
field extension splitting the chosen maximal torus. It compares the two fppf
quotients of the full derived subgroup by their canonical isomorphism. A desired
cocharacter is first composed with the inverse comparison, lifted by the
published theorem, then transported back using the quotient factorization.
This surjectivity step does not require the derived group to be simply connected.

`cocenter_cocharacter_ker` records exactness as an equality of integral
submodules. Under the simply-connected-derived hypothesis,
`cocenterCocharacterEquiv` combines that kernel equality and surjectivity with the
first isomorphism theorem. It identifies the chosen quotient presentation of
`π₁(G)` with the actual cocenter cocharacter lattice.
`cocenterCocharacterEquiv_projection` verifies its actual postcomposition law
on cocharacter representatives. The equivalence requires a splitting extension
for the chosen maximal torus; it does not yet identify any selected
fundamental-group or inertia map.
