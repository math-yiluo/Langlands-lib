# The dual of a line bundle is its tensor inverse

Module `Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation` proves
that a line bundle `L` on a scheme `X` has a tensor inverse, namely its
dual `L^∨ = Hom(L, O_X)`. The module is a helper for the proof of
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. There it
supplies the `inverse` hypothesis of
`Langlands.AbelianScheme.picardZeroLineBundleClassification_of_inverse`.
The objects are the Library ones:

* `dual M` is the internal dual `internalHom M O_X` from `ModuleDual`;
* `dualTensorEval M : tensorObj M (dual M) ⟶ structureSheaf X` is the
  evaluation `m ⊗ φ ↦ φ(m)` from `ModuleDualEvaluation`;
* `IsLocallyFreeRankOne` and `LineBundle` come from `Picard.LineBundle`.

## Main results

* `Langlands.Scheme.Modules.isIso_dualTensorEval (hM : IsLocallyFreeRankOne M) :
  IsIso (dualTensorEval M)`. For a locally free module `M` of rank one, the
  evaluation `M ⊗ M^∨ → O_X` is an isomorphism.
* `Langlands.Scheme.Modules.isLocallyFreeRankOne_dual (hM : IsLocallyFreeRankOne M) :
  IsLocallyFreeRankOne (dual M)`. The dual of such a module is again locally
  free of rank one.
* `Langlands.AlgebraicGeometry.Picard.LineBundle.exists_tensorObj_iso_structureSheaf
  (L : LineBundle X) : ∃ M : LineBundle X, Nonempty (tensorObj L.obj M.obj ≅
  structureSheaf X)`. Every line bundle has a tensor inverse. The witness is
  `⟨dual L.obj, isLocallyFreeRankOne_dual L.property⟩`, and the isomorphism
  is `asIso (dualTensorEval L.obj)`.

## Local generators (namespace `Langlands.Scheme.Modules`)

Fix an open `W` and a trivialization `t : M.restrict W.ι ≅ O_W`.

* `overTrivialization t : M.over W ≅ unit (X.ringCatSheaf.over W)`. This
  transports `t` to sheaves on the opens contained in `W`. It uses the
  Library equivalence `Scheme.Modules.overEquiv W` (preimage of an
  isomorphism under its fully faithful functor), the comparison
  `overFunctorEquiv W`, and `restrictUnitIso W.ι`.
* `unitLocalBasis t : free PUnit ≅ M.over W` is a one-element local basis.
  It is `coproductUniqueIso` followed by the inverse of `overTrivialization t`.
  With it, the Library finite local-basis lemmas of `ModuleDualLocalFree`
  apply with index type `I = PUnit`.
* `trivGen t i` (for `i : V ⟶ W`) is the local generator `σ` in `Γ(M, V)`,
  and `trivDualGen t` is the dual generator `σ^∨` in `Γ(M^∨, W)`. They are the
  Library `localBasisSection` and `localBasisCoordinate` of `unitLocalBasis t`.
* `trivGen_restrict`: the generators are compatible with restriction.
* `trivDualGen_eval`: `σ^∨|_V (σ) = 1`, by `localBasisCoordinate_basis`.
* `trivGen_expansion`: `m = σ^∨|_V(m) · σ` for every `m ∈ Γ(M, V)`, by
  `localBasis_expansion` with a one-term sum.
* `trivDual_expansion`: `φ = φ(σ) · σ^∨|_V` for every `φ ∈ Γ(M^∨, V)`. Both
  sides are local homomorphisms (`LocalHom.ext`). On a smaller open `V'`, the
  claim follows from `trivGen_expansion`, linearity of `φ`, naturality of
  evaluation (`internalHomEval_restrict`) and commutativity of `Γ(X, V')`.

## Sectionwise evaluation

* `tensorEvalSection V : (M ⊗ M^∨)(V) → Γ(X, V)` is the component at `V` of
  the presheaf map `tensorHomEquiv _ _ _ (dualTensorEval M)`, which is
  adjoint to the sheaf map. Here `M ⊗ M^∨` is the sectionwise (presheaf)
  tensor product. By `tensorEvalSection_tmul`, it sends `m ⊗ φ` to
  `φ(m)`. It is additive (`tensorEvalSection_add`).
* `gamma_smul_tmul`: `(a • m) ⊗ φ = m ⊗ (a • φ)` in the sectionwise tensor
  product.
* `tensorEvalSection_expansion`: on `V ⊆ W`, every `x` equals
  `(ev(x) · σ) ⊗ σ^∨|_V`. The proof is induction on `x`. For `m ⊗ φ` it uses
  the two expansions above, and the additive case is immediate.
* `bijective_tensorEvalSection t i`: on every `V ⊆ W` the map
  `tensorEvalSection V` is bijective. Injectivity follows from the
  expansion. The preimage of `s` is `(s · σ) ⊗ σ^∨|_V`, because
  `σ^∨(σ) = 1`.
* `exists_bijective_tensorEvalSection hM hx`: every point `x` of an open `U`
  lies in a smaller open `V ⊆ U` on which `tensorEvalSection V` is
  bijective. Take `V = U ⊓ W'` for a trivializing open `W'` of `x`.

## Proof of `isIso_dualTensorEval`

Let `f₃` be the underlying presheaf-of-abelian-groups map of
`tensorHomEquiv _ _ _ (dualTensorEval M)`. Let `f₁` be the sheafification unit
`tensorSheafifyUnit M (dual M)`, and let `f₂` be the underlying map of
`(dualTensorEval M).val`. The Library lemma
`tensorHomEquiv_eq_tensorSheafifyUnit_comp` gives `f₁ ≫ f₂ = f₃`.

1. `f₁` is locally surjective, since it is a sheafification unit
   `toSheafify` (a Mathlib instance).
2. `f₃` is locally surjective and locally injective for the topology of
   opens. Near each point there is an open on which its component is
   bijective (`exists_bijective_tensorEvalSection`). For injectivity,
   restriction is moved across `f₃` by naturality.
3. By Mathlib's `Presheaf.isLocallySurjective_of_isLocallySurjective_fac` and
   `Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac`,
   `f₂` is locally surjective and locally injective.
4. Both source and target of `f₂` are sheaves. Mathlib's
   `Sheaf.isLocallyBijective_iff_isIso` therefore shows that the image of
   `dualTensorEval M` under `SheafOfModules.toSheaf` is an isomorphism.
5. `SheafOfModules.toSheaf` reflects isomorphisms, so `dualTensorEval M` is
   an isomorphism (`isIso_of_reflects_iso`).

## Proof of `isLocallyFreeRankOne_dual`

Let `t'` be a trivialization of `M` on `W' ∋ x`. The Library
`dualLocalFreeIso (unitLocalBasis t') : free PUnit ≅ (dual M).over W'`,
composed with `coproductUniqueIso`, gives `(dual M).over W' ≅ unit`. The
helper `restrictTrivialization` transports this isomorphism back to
`(dual M).restrict W'.ι ≅ O_{W'}`. It is the inverse direction of
`overTrivialization`.

## Provenance

The mathematics is standard. The Stacks Project, Lemma 17.25.5 (Section
17.25, Tag 01CR), shows that for an invertible module `L` the dual
`Hom(L, O_X)` is invertible and the evaluation `L ⊗ Hom(L, O_X) → O_X` is an
isomorphism. Lemma 17.25.4 there shows that a locally free module of rank one
is invertible. The registered source is
`stacks-local-freeness-invertibility-sections-2026-10-21`. See also
Hartshorne, *Algebraic Geometry*, Proposition II.6.12. The Lean route is the
formalization's own and does not follow a specific printed proof: it uses
local generators, then local bijectivity of the presheaf evaluation, then
reflection along the forgetful functor to sheaves. The Lean results are
stated only for the Library's locally-free-of-rank-one predicate, not for
general invertible modules.
