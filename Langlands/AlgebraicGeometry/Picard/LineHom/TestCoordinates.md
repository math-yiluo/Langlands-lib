# Frame coordinates of morphisms between pulled-back line bundles

Helper module for the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement`.

Setting: a scheme `X`, an open cover `T : ι → X.Opens` with `⨆ i, T i = ⊤`,
sheaves of modules `L` and `M` on `X` with frames `e i` of `L` and `f i` of
`M` on `T i` (`Scheme.Modules.IsFrameOn`), and unit transition functions `α`
and `β` with `IsTransition e α` and `IsTransition f β` (Library
`Picard/CocycleLineBundleFrame`). Sections are pulled back along a morphism
`q : Y ⟶ X` by the ported FLT `pullbackLocalSection q`, and transition
functions by the Library `pullbackCocycle q`.

- `isTransition_pullback`: if `IsTransition e g`, then the pulled-back
  sections `pullbackLocalSection q (e i)` on `q ⁻¹ᵁ T i` satisfy
  `IsTransition` with the pulled-back transition functions
  `pullbackCocycle q g`.
- `iSup_preimage_eq_top`: the preimages `q ⁻¹ᵁ T i` again cover `Y`.
- `pullbackFrameHomEquiv he hf hα hβ hT q`: the bijection between morphisms
  `q^* L ⟶ q^* M` and families `a i ∈ Γ(Y, q ⁻¹ᵁ T i)` with
  `IsGaugeFamily (pullbackCocycle q α) (pullbackCocycle q β) a`.
  `pullbackFrameHomEquiv_spec` says that the family `a` of `φ` satisfies
  `φ (q^* e i) = a i • q^* f i`.
- `pullbackComp_inv_app_pullbackLocalSection`: the inverse of the Mathlib
  isomorphism `pullbackComp k q : (k ≫ q)^* ≅ q^* ⋙ k^*` sends the
  pullback of a section along `k ≫ q` to its pullback along `q` and then `k`.
- `pullbackFrameHomEquiv_transport`: for `k : Y' ⟶ Y` and `q' = k ≫ q`, the
  family of the transported morphism
  `Langlands.Scheme.Modules.transport k h h φ : q'^* L ⟶ q'^* M` is, in each
  coordinate, the image `k.appLE (q ⁻¹ᵁ T i) (q' ⁻¹ᵁ T i) _ (a i)` of the
  family `a` of `φ`.
- `presheafHom_map_eq_transport`: for objects `U`, `U'` of `Over Y` and
  `k : U' ⟶ U`, the restriction map of the Hom presheaf
  `intrinsicModulePseudofunctor.presheafHom L M` along `k` is
  `transport k.left (Over.w k) (Over.w k)`.
- `intrinsicModuleHomPresheaf_map_down`: consequently, the restriction map of
  the Library relative Hom presheaf `intrinsicModuleHomPresheaf p L M` along
  `g : T' ⟶ T` in `Over B` is transport along the induced morphism
  `((Over.pullback p).map g).left` of base changes.

Proofs as implemented. `isTransition_pullback` pulls back the transition
relation with the FLT lemmas `map_homOfLE_pullbackLocalSection` and
`pullbackLocalSection_smul`. `pullbackFrameHomEquiv` and its `_spec` are the
`FrameHom` statements `frameHomEquiv`, `frameHomEquiv_spec` applied to the
pulled-back frames (FLT `IsFrameOn.pullbackLocalSection`).
`pullbackComp_inv_app_pullbackLocalSection` applies the inverse to the Library
identity `sectionPullback_comp` and cancels `hom ≫ inv`. For
`pullbackFrameHomEquiv_transport` (after `subst`), the uniqueness statement
`frameHomEquiv_apply_eq` reduces it to the identity
`transport φ (q'^* e j) = k(a j) • q'^* f j`; this unfolds `transport` with
`LineBundleFlatDescent.compIso_rfl` into `pullbackComp` components and uses
`pullbackComp_inv_app_pullbackLocalSection`, the naturality
`sectionPullback_naturality`, `pullbackFrameHomEquiv_spec`,
`pullbackLocalSection_smul` and `sectionPullback_comp`.
`presheafHom_map_eq_transport` unfolds the Mathlib `pullHom` and rewrites the
two `mapComp'` components with the Library lemmas
`IntrinsicModuleHomDescent.mapComp'_hom` and `mapComp'_inv`.

These are the standard compatibilities of frames, transition functions and
pullback; they are internal to this proof.
