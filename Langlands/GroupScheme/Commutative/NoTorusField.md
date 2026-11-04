# Commutative groups without tori over arbitrary fields

Module `Langlands.GroupScheme.Commutative.NoTorusField`.

The proposition `Langlands.GroupScheme.CommutativeNoTorusUnipotentStatement.{u}`
is the commutative instance of the parent no-torus theorem. It quantifies over
any field `k : Type u` and a commutative group scheme `Z` over `Spec k` whose
structure morphism is smooth and affine and whose underlying space is connected.
It assumes that, for every torus `T` over `k`, every actual group-scheme
homomorphism `T → Z` has bottom subgroup-functor range. It concludes that `Z` is
unipotent. There is no perfectness, infinitude, characteristic, or algebraic
closedness assumption on `k`.

The theorem
`CommutativeNoTorus.isUnipotent_of_no_torus_over_field` proves this implication
for a given `Z`. The theorem `commutativeNoTorusUnipotent` packages it as the
universe-general proposition above. The proof uses the actual base change of
`Z` to `K = SeparableClosure k`. This field is separably closed and Galois over
`k`. The published geometric connectedness theorem for smooth connected affine
groups supplies connectedness after this extension; smoothness and affineness
are stable under the actual scheme pullback.

The finite-Galois descent theorem
`CocharacterDatum.gm_hom_eq_zero_of_isGalois` applies to the original no-torus
hypothesis and shows that every cocharacter `Gm_K → Z_K` vanishes. In detail,
its supporting modules descend each multiplicative universal point to a finite
Galois intermediate field and use the actual Weil transfer from a torus, whose
vanishing detects the original cocharacter. This step does not assume no-torus
preservation after arbitrary base change.

The previously published theorem
`CommutativeNoTorus.isUnipotent_of_gm_hom_eq_zero_of_isSepClosed` therefore makes
`Z_K` unipotent. That criterion handles the purely inseparable passage from a
separably closed field to its algebraic closure using the actual cocharacter
comparison. Finally, `IsUnipotent.of_baseChange` reflects unipotence back to `Z`.
Local finite type, needed for coefficient descent, follows here from smoothness.

This is an internal deduction from the actual coefficient descent, transfer,
commutative character criterion, geometric connectedness, and field-reflection
interfaces. Its additional proposition is a named commutative specialization of
the original target. The general target `NoTorusUnipotentStatement` for groups
without a commutativity assumption remains a separate proof obligation.
