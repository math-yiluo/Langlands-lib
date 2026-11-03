# Infinitesimal gluing for actual field Picard groupoids

`FieldPicardInfinitesimalGluingStatement` states a gluing equivalence for the
actual relative line-bundle groupoids of a proper scheme over any field.
It is a proposition to be proved separately.

For a field `k : Type u`, an actual scheme `X : Scheme.{u}`, and a proper
map `f : X -> Spec k`, choose arbitrary commutative `k`-algebras
`R, A, B, C : Type u` and algebra maps
`p : R -> A`, `q : R -> B`, `a : A -> C`, `b : B -> C`.
The hypotheses are that this is a categorical pullback square of the
underlying commutative rings, that `b` is surjective, and that its kernel
ideal is nilpotent. No noetherian, artinian, finite dimensional, local or
residue-field hypothesis is imposed on these four algebras.

The conclusion is that the specific functor
`PicardGroupoid.affineSquareComparison f p q a b h` is an equivalence.
Its domain is the actual Picard groupoid on `X_R`, the total scheme of
the ordinary base change of `f` to `Spec R`. Its target is the comma
groupoid of the two actual restriction functors from `X_A` and `X_B`
to `X_C`. Thus an object in the target consists of actual line bundles
`L_A`, `L_B` and an actual isomorphism between their ordinary pullbacks
to `X_C`. Its arrows are compatible pairs of actual bundle
isomorphisms. The specified comparison uses ordinary pullback and its
published coherent composition isomorphisms. The equivalence asserts
both effectivity of these gluing objects and full faithfulness on their
actual isomorphisms; it is stronger than a claim about isomorphism classes.

This is a derived rank-one scheme specialization of the Stacks Project
infinitesimal gluing results. Section 99.5, Situation 99.5.1 and
Lemma 99.5.7, in retained `08KA.html`, state the analogous equivalence
for finitely presented quasi-coherent families flat over the test base
and having proper support, across a scheme pushout with one thickening
and the other arrow affine. Under the present ring hypotheses the
corresponding square has `Spec C -> Spec B` a nilpotent thickening,
`Spec C -> Spec A` affine and `Spec R` its pushout. Properness of `f`
gives finite presentation; over a field `f` is also flat. A line bundle
on a base change of `X` is finitely presented and flat over that test
base, and its support is proper. These facts explain the relation with
the coherent-family formulation.

Restricting a coherent-family equivalence to locally free rank one
requires justification. The algebraic input is More on Algebra,
Situation 15.6.1 (Tag 08KH) and Lemma 15.6.9 (Tag 0D2J):
finite projective modules on a ring fibre product with one surjective
map are equivalent to compatible finite projective modules on its two
factors. In the notation of that source,
`B'`, `B`, `A'`, `A` correspond to `R`, `A`, `B`, `C` here.
On an affine open `Spec D` of `X`, tensoring the ring square with `D`
over the field `k` preserves its exact fibre-product description and
the surjection. The nilpotent kernel remains nilpotent. Finite
projective patching applies on this affine open. Rank one is detected
after restriction to the factor `D tensor_k A`, since its spectrum
embeds into the spectrum of `D tensor_k R` as a nilpotent closed
subscheme and has the same points and residue fields. Full faithfulness
allows these local patched bundles and their comparisons to glue on
overlaps. This explains the derived scope of the proposition; these
steps remain obligations of its separate Lean proof.

Sources are `stacks-coherent-sheaf-stack-08ka-2026-11-01`,
`08KA.html`, Situation 99.5.1 and Lemma 99.5.7; and
`stacks-finite-projective-patching-0d2j-2026-11-03`,
`08KH.html`, Situation 15.6.1, and `0D2J.html`, Lemma 15.6.9.
No cited result is asserted to be already proved by defining this
proposition.

The statement preserves the field and scheme universe `u`, arbitrary
fields and arbitrary proper schemes. It assumes no projectivity,
smoothness, reducedness, connectedness or rational point. It supplies
neither a smooth chart nor the Picard stack atlas by itself.
