# Moving a rational parabolic above a fixed minimal parabolic

This module is an internal, derived assembly of published definitions and
explicit structural premises. It supplies no proof of those premises or of
`StandardParabolicClassificationStatement`.

For group schemes over any base scheme, `range_eq_comap_of_iso_square` converts
an actual commuting square
`i ≫ e.hom = d.hom ≫ i'`, with both `e` and `d` isomorphisms, into
`range i = (range i').comap e.hom`. On every test scheme the forward implication
uses the point map of `d.hom`; the reverse implication uses `d.inv` and cancels
`e.hom`. Neither inclusion has to be monic.

The remaining lemmas work over an arbitrary field `k : Type u`, with an actual
connected reductive group scheme `G`:

- `IsMinimalParabolicFunctor.isRationallyConjugate_of_statement` unpacks each
  minimal functor into an actual minimal parabolic subgroup. The explicit
  premise `MinimalParabolicConjugacyStatement` gives the point `g` and
  subgroup isomorphism. The square lemma yields exactly
  `M = M'.comap (G.innerIso g).hom`.
- `IsParabolicFunctor.exists_minimal_le_of_statement` unpacks a parabolic
  functor and applies the explicit premise `ParabolicContainsMinimalStatement`
  to obtain an actual minimal subgroup with the required all-test inclusion.
- `exists_conjugate_containing_minimal_of_statements` combines those two
  lemmas. Given a fixed minimal functor `M` and a parabolic functor `F`, it
  returns `g` with `M ≤ F.comap (G.innerIso g).inv`. This preimage under the
  inverse is the forward conjugate of `F`.
- `conjugatingPointContainingMinimal_of_statements` chooses such an actual
  rational point and bundles it with the same all-test containment certificate.
  It uses classical choice on the preceding existence lemma.
- `exists_conjugate_dynamicParabolic_containing_generic_of_minimal_statements`
  applies this to the dynamic parabolic of any cocharacter `zeta` and to the
  fixed generic dynamic parabolic of a maximal split torus. Its four explicit
  premises are `ParabolicDynamicStatement`, `GenericMinimalParabolicStatement`,
  `MinimalParabolicConjugacyStatement` and `ParabolicContainsMinimalStatement`.

In the final lemma the published affine representative
`Dynamic.Affine.parabolicHom zeta` is closed and represents the dynamic functor
on every test scheme. Affineness of `G` follows from its affine structure morphism
and the affine base `Spec k`. The first premise certifies its parabolicity; the second
certifies minimality of the fixed generic dynamic functor. Pulling back the
resulting inclusion through the inverse inner automorphism and using dynamic
functoriality gives
`P(ν ≫ i) ≤ P(zeta ≫ (G.innerIso g).hom)`.

All conclusions use the original subgroup functors on every test scheme.
The trivial cocharacter, improper parabolic and empty relative root system
are included: the argument introduces no nonzero, properness or nonemptiness
premise. There is no restriction on the characteristic, perfectness or
cardinality of the field.

The provenance is the inspected published definitions of parabolic and minimal
parabolic functors, their actual-subgroup counterparts, rational conjugacy,
affine dynamic representability and isomorphism functoriality. No additional
literature assertion is used. All structural propositions named as premises
remain obligations of their respective proof tasks. This module proves no
standardness-by-containment, standard-index injectivity or conjugacy rigidity.
