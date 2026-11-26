# Proof: affine analytification detects open and closed immersions

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationAnalyticImmersion`
proves the unchanged statement
`AffineAnalytificationAnalyticImmersionStatement.{u, v}` in all universes. For
a complete, ultrametric, nontrivially normed field `K : Type u`, commutative
`K`-algebras `A B : Type v` with finite polynomial presentations `P` and `Q`,
and a `K`-algebra map `f : A →ₐ[K] B`, it gives
- `Function.Surjective f ↔ closedImmersion (localizedHom K P Q f)`;
- `IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
  openImmersion (localizedHom K P Q f)`.

## Implemented proof

The four implications come from four results.

1. Surjective maps give closed immersions:
   `closedImmersion_localizedHom_of_surjective` in
   `AffineAnalytificationClosedImmersionPreservation`. On the selected
   original charts the strong map is the quotient by the kernel, and the
   recognized inverse image of every target affinoid domain is given by an
   admissible quotient.
2. Closed immersions come from surjective maps:
   `surjective_of_closedImmersion_localizedHom` in
   `AffineAnalytificationClosedImmersionReflection`. An analytic closed
   immersion is monic and a closed embedding on points. Monicity makes `f` a
   ring epimorphism (`AffineAnalytificationMonomorphismComparison`). After
   passing to models of `A` and `B` in the universe of `K`
   (`AffineAnalytificationUniverseReduction`), the glued scheme
   analytification of `Spec(f)` is identified with the affine map on points.
   It is therefore proper, and properness reflection for quasi-finite
   morphisms to an affine target makes `f` finite. A finite ring epimorphism is
   surjective.
3. Open immersions give analytic open immersions:
   `openImmersion_localizedHom_of_isOpenImmersion` in
   `AffineAnalytificationOpenImmersionPreservation`. The analytic map factors
   through the open domain of the points whose center lies in the image of
   `Spec B`. An inverse is glued from affinoid lifts: every affinoid chart of
   that domain is given by an algebra map from `A`, which factors through `f`
   by the lifting property of the open immersion.
4. Analytic open immersions give open immersions:
   `isOpenImmersion_of_openImmersion_localizedHom` in
   `AffineAnalytificationOpenImmersionReflection`. An analytic open immersion
   is monic and étale. Monicity makes `Spec(f)` a monomorphism, étale
   reflection makes `f` étale, and Mathlib's flat-monomorphism criterion gives
   an open immersion.

The theorem assembles the two equivalences from these four implications.

## Sources

Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*
(1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:
Proposition 3.4.6(8), printed p.65/PDF p.79, with its proof on printed
p.66/PDF p.80, and Proposition 3.4.7(2), printed p.66/PDF p.80. Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, gives the
analytic notions of open and closed immersion (after Definition 1.3.1, printed
p.23/PDF p.20; Lemma 1.3.7, printed pp.27–28/PDF pp.24–25). Conrad, *Weil and
Grothendieck approaches to adelic points* (2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed
p.19, proof of Proposition 5.11(3), uses this compatibility.

The implemented route differs from Berkovich's proofs where stated in the
helper modules. Monicity replaces radicality in the open-immersion converse.
The closed-immersion converse obtains finiteness from properness reflection
for quasi-finite morphisms, which rests on the finite form of Zariski's Main
Theorem. The open-immersion direction constructs the analytic inverse by
gluing affinoid lifts.
