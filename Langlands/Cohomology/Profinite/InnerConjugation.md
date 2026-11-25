# Inner conjugation acts trivially on cohomology

`Langlands/Cohomology/Profinite/InnerConjugation.lean`, namespace
`Langlands.ProfiniteCohomology`.

For `g ∈ G`, conjugation `γ ↦ g⁻¹ γ g` together with `a ↦ g a` on the coefficients is a
compatible pair and induces an endomorphism of `Hⁿ(G, A)`. For a compact group it is the
identity in every degree. The proof is by dimension shifting: the endomorphism commutes with the
connecting maps, is the identity on `H⁰`, and the coinduced modules are acyclic.

## Declarations

- `innerConjHom g : G →* G`, `γ ↦ g⁻¹ γ g` (`innerConjHom_apply`, `continuous_innerConjHom`).
- `innerConjMor A g`: the morphism `a ↦ g a` from the restriction of `A` along `innerConjHom g`
  to `A` (`innerConjMor_hom_apply`), natural in `A` (`innerConjMor_naturality`).
- `cohomologyInnerConj A n g`: the induced endomorphism `map (innerConjHom g) (innerConjMor A g) n`
  of `Hⁿ(G, A)`; `innerConjShortComplexMor`, `δ_comp_cohomologyInnerConj` (compatibility with
  connecting maps), `cohomologyInnerConj_zero` (identity on `H⁰`).
- `cohomologyInnerConj_eq_id`, `cohomologyInnerConj_apply`: for a compact group the endomorphism
  is the identity in every degree.
- `hom_apply_hom_apply_of_comp_eq`, `hom_apply_hom_apply_eq_of_comp_eq`: evaluation of a
  commutative triangle or square in `ModuleCat` at an element.
- `continuous_toMonoidHom`: a bundled continuous homomorphism is continuous as a monoid
  homomorphism.

The Library has inner conjugations with the opposite convention (`γ ↦ a γ a⁻¹`, coefficients
through `a⁻¹`): `Langlands.OrdinaryCohomology.innerConjugation` for ordinary group cohomology,
shown to act as the identity in degree `2` only (`innerConjugationMap_two`), and
`Langlands.Continuous.innerConjugation` on continuous cohomology, with its functoriality but no
statement that it acts as the identity. Neither gives the statement in all degrees for the
cochains of this theory, so the source's version is taken.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/InnerConj.lean` and (for the two
evaluation lemmas)
`src/GroundTheory/ProfiniteCohomology/CompactSupportCohomology/HomApplyHomApplyEqOfCompEq.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's;
`continuous_toMonoidHom` is new (the source passed the homomorphism and its continuity
separately).

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter VII,
  §5, Proposition 3, p. 116 (the automorphisms `σ_t` of `H^q(G, A)` defined by `s ↦ tst⁻¹` and
  `a ↦ t⁻¹a` are the identity). Serre proves it for the cohomology of an abstract group.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §6, Proposition (1.6.3), p. 61 (the conjugation
  `σ_* : Hⁿ(G, A) → Hⁿ(G, A)` is the identity; conjugation is defined in §5, p. 46).
