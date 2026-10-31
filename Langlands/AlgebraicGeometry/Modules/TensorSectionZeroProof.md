# Zero tests for tensor products of actual sections

`Langlands.SchemeModule.tensorSectionZero` proves
`TensorSectionZeroStatement.{u}` for arbitrary schemes, module sheaves
and global sections in every universe `u`, with no ambient hypotheses.
This is derived internal calculus for the published actual
`Scheme.Modules` tensor product, `tensorSection` and `pullbackSection`.
No external literature theorem is used. No field, local freeness,
smoothness, properness, projectivity or ampleness hypothesis is used.

## Component lemmas

The five clauses of the statement are the following named lemmas, in
order:

1. `tensorSection_zero_left`: `tensorSection M N 0 t = 0`.
2. `tensorSection_zero_right`: `tensorSection M N s 0 = 0`.
3. `tensorSection_eq_zero_iff_of_isIso_right`: if `sectionHom N t` is
   an isomorphism, then `tensorSection M N s t = 0 ↔ s = 0`.
4. `tensorSection_eq_zero_iff_of_isIso_left`: if `sectionHom M s` is an
   isomorphism, then `tensorSection M N s t = 0 ↔ t = 0`.
5. `pullback_tensorSection_eq_zero_iff`: for `f : Y ⟶ X`, the actual
   pullback `pullbackSection f (tensorObj M N) (tensorSection M N s t)`
   is zero exactly when the tensor section of the two actual pulled-back
   sections, `pullbackSection f M s` and `pullbackSection f N t`, is
   zero.

The module also gives two derived corollaries.
`pullback_tensorSection_eq_zero_iff_of_isIso_right` assumes
`pullbackSectionHom f N t` is an isomorphism and concludes that the
pulled-back tensor section is zero exactly when `pullbackSection f M s`
is zero. `pullback_tensorSection_eq_zero_iff_of_isIso_left` is the
version with the left factor and `pullbackSection f N t`. Each rewrites
the hypothesis with `sectionHom_pullbackSection` and then combines
clause 5 with clause 3 or 4 on `Y`.

## Proof

Throughout, a global section is zero exactly when its morphism from the
structure module is zero. This is `sectionHom_eq_zero_iff` from the
published `SectionVanishingTransportProof`. The published
`sectionHom_tensorSection` writes the morphism of `tensorSection M N s t`
as the inverse left unitor of the structure module followed by
`tensorMap (sectionHom M s) (sectionHom N t)`.

**Zero factors.** `tensorMap f g` is sheafification applied to the
presheaf tensor of `f.val` and `g.val`. Two private lemmas show that
`tensorMap` is zero if either factor is zero. On each open, the presheaf
tensor with a zero morphism is zero by `MonoidalPreadditive.zero_tensor`
or `tensor_zero` in module categories. Sheafification is additive, as a
left adjoint (`left_adjoint_additive`), so it sends zero to zero. File-local
instances supply this additivity and the additivity of the forgetful
functor to presheaves of modules. Clauses 1 and 2 follow from these two
lemmas and `sectionHom_tensorSection`.

**Frame cancellation.** For clause 3, the leading inverse unitor is an
epimorphism and can be cancelled (`comp_eq_zero_iff_of_epi`). By
`tensorMap_comp`, the tensor of the two section morphisms factors as
`tensorMap (sectionHom M s) (𝟙 _)` followed by
`tensorMap (𝟙 M) (sectionHom N t)`. The second map is an isomorphism
because it is the image of an isomorphism under the tensor functor, so
it can be cancelled as a monomorphism. Composing with the right unitor
of `M`, which is also a monomorphism, and using the published
`tensorRightUnitor_naturality` turns the remaining map into the right
unitor of the structure module followed by `sectionHom M s`. Cancelling
that unitor and applying `sectionHom_eq_zero_iff` gives `s = 0`. Clause
4 is symmetric: it uses the opposite factorization and
`tensorLeftUnitor_naturality`.

The hypothesis in clauses 3 and 4 is a global frame condition: the
section morphism must be an isomorphism. The lemmas do not claim that a
merely nonzero factor reflects zero. That stronger claim fails over rings
with zero divisors, such as rings of dual numbers.

**Pullback comparison.** Write `P` for `Scheme.Modules.pullback f` and
`c` for the published natural transformation `pullbackTensorComparison f`.
It is invertible by the published `pullbackTensorComparisonIsIso`.
`pullbackSection_eq_zero_iff` tests the left side of clause 5 on
`P.map` of the section morphism of the tensor section. After
`Functor.map_comp` and cancelling the image of the inverse unitor, which
is an isomorphism, the condition becomes
`P.map (tensorMap (sectionHom M s) (sectionHom N t)) = 0`. Naturality of
`c` at the pair of section morphisms, with the component `c.app (M, N)`
cancelled as a monomorphism and the structure-module component cancelled
as an epimorphism, shows that this holds exactly when
`tensorMap (P.map (sectionHom M s)) (P.map (sectionHom N t)) = 0`.

For the right side, `sectionHom_tensorSection` on `Y`, cancellation of
the inverse unitor and `sectionHom_pullbackSection` reduce the condition
to zero of the tensor of the two `pullbackSectionHom` morphisms. By
definition, each is the inverse of `pullbackUnitIso f` followed by `P.map`
of a section morphism. By `tensorMap_comp`, their tensor is the tensor of
the two inverse unit comparisons followed by
`tensorMap (P.map (sectionHom M s)) (P.map (sectionHom N t))`. The first
map is an isomorphism and is cancelled. The two sides therefore have the
same zero condition. The proof compares zero conditions in canonically
isomorphic module sheaves. It does not assert or need an equality of
section values.

## Dependencies

The proof imports the published `TensorSectionZeroStatement`,
`SectionVanishingTransportProof` (for `sectionHom_eq_zero_iff` and
`pullbackSection_eq_zero_iff`), `PullbackTensorProof` (for
`pullbackTensorComparisonIsIso`) and `TensorUnitorLaws`, together with
the Mathlib files on preadditive monoidal categories and additive
adjoints. Through these imports it uses published constructions and
lemmas from `Tensor`, `PullbackTensor`, `TensorSections`,
`SectionResidue`, `PullbackSectionOpenProof` and `PullbackUnit`. The
target statement pair and all pairs it imports are unchanged.

Worker 354 wrote the Lean proof as a shared draft. It is used here
unchanged.
