# Conjugacy of local-to-relative Weil maps

This module proves the published proposition
`Langlands.ClassField.Global.LocalRelativeWeilMapConjugacyStatement.{u}` (module
`Langlands.ClassField.Global.LocalRelativeWeilMapStatement`) as the theorem

`Langlands.ClassField.Global.localRelativeWeilMapConjugacy :
  LocalRelativeWeilMapConjugacyStatement.{u}`.

The universe `u` is arbitrary. The theorem keeps every quantifier and hypothesis of the
published statement and adds none. In particular it makes no assumption on the class
family `c`. Let `E/F` be a Galois extension of number fields, `w` a finite place of `E`
above the finite place `v` of `F`, and `e` a reciprocity candidate of `E_w`. Let
`ι, ι' : W_{F_v} → W_{E/F}` be continuous homomorphisms with
`IsLocalRelativeWeilMap v w e ι` and `IsLocalRelativeWeilMap v w e ι'`. The theorem gives
`b : C_E` with `ι' g = inclusion b * ι g * (inclusion b)⁻¹` for every `g`.

## Helper lemmas

All helpers are in namespace `Langlands.ClassField.Global.RelativeWeilGroup`.

- `completionClosureEmbedding_fixed_of_global v w σ h z`: let `σ` be an automorphism of
  the algebraic closure of `F_v` over `F_v` that fixes the image of `E` under
  `E → E_w → \bar{F_v}`. Then `σ` fixes the image of every `z ∈ E_w`.
- `mem_range_completionWeilMap_of_fixes v w g h`: if the Galois image of `g ∈ W_{F_v}`
  fixes the image of `E`, then `g` lies in the image of `completionWeilMap v w`, that is,
  of `W_{E_w}`.
- `projection_eq_of_isLocalRelativeWeilMap hι hι' g`: two maps satisfying the Galois
  condition of `IsLocalRelativeWeilMap` at the same place `w` have the same image in
  `Gal(E/F)`. The candidates may differ.

## Implemented proof

**The completion is spanned by `E`.** The published `finiteTensorMap_surjective`
(module `Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction`) says that
`F_v ⊗_F E → ∏_{q | v} E_q` is surjective. So every `z ∈ E_w` is the `w`-component of
the image of some tensor `t`. The first helper follows by tensor induction: on
`a ⊗ y` the image is `a · y`, and `σ` fixes the image of `a ∈ F_v` (it is an
`F_v`-automorphism, using `completionClosureEmbedding_algebraMap`) and the image of
`y ∈ E` (by hypothesis). Sums are additive. For the second helper, the published
`Weil.Local.extensionWeilMap_range` and `Weil.Local.extensionGaloisMap_range` identify
the image of `W_{E_w}` with the Weil elements whose Galois image fixes the image of
`E_w`. The first helper supplies that.

**Same Galois images.** The Galois condition in `IsLocalRelativeWeilMap` determines the
image of `ι g` on `E` through the injective embedding `E → \bar{F_v}`. Hence
`projection (ι' g) = projection (ι g)`.

**The cocycle.** By exactness (`RelativeWeilGroup.exact`), `ι' g (ι g)⁻¹` is
`inclusion (α g)` for a chosen `α g ∈ C_E`. The conjugation formula
`RelativeWeilGroup.conjugation` gives the crossed-homomorphism identity
`α (g h) = α g · τ_g(α h)`, where `τ_g` is the image of `ι g` in `Gal(E/F)` acting
through `ideleClassEquiv`.

**Triviality on `W_{E_w}`.** The third condition of `IsLocalRelativeWeilMap` gives the
same value for `ι` and `ι'` on the image of `W_{E_w}`, because the candidate is the same.
So `α` vanishes there. By the second helper, every `g` with `τ_g = 1` lies in that image,
so `α g = 1`. With the cocycle identity, `α g` depends only on `τ_g`.

**Descent and `H¹ = 0`.** Let `D` be the image of `g ↦ τ_g` in `Gal(E/F)` and `K` its
fixed field. By `IntermediateField.fixingSubgroup_fixedField`, `Gal(E/K)` is identified
with `D`. Choosing lifts defines `f : Gal(E/K) → C_E` with `f σ = α (lift σ)`. It is a
multiplicative 1-cocycle for `relativeIdeleClassAut K E`. The published
`ideleClassH1Vanishing` gives `H¹(Gal(E/K), C_E) = 0`. As in the published proof of
`H1VanishingProof.exists_coboundary_of_prime_card`, `groupCohomology.H1π_eq_zero_iff`
turns this into `c₀ ∈ C_E` with `f σ = σ(c₀) / c₀`. Hence `α g = τ_g(c₀) / c₀` for every
`g`.

**Conclusion.** Take `b = c₀⁻¹`. Then
`inclusion b * ι g * (inclusion b)⁻¹ = inclusion (τ_g(c₀) / c₀) * ι g = ι' g`, by the
conjugation formula and commutativity of `C_E`.

## Checks

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It
assumes no unproved proposition. Its inputs are published definitions and the published
theorems named above, including `ideleClassH1Vanishing`. It makes no use of local
Langlands results.

## Provenance

The argument is Tate's, at finite level: J. Tate, *Number theoretic background*, Proc.
Sympos. Pure Math. 33, Part II (1979), §1.5, printed p.8, and the proof of (1.6.1),
printed pp.8–9 (source `tate-1979-number-theoretic-background`). It is the route
sketched under "Expected proof" in the Markdown of the target statement. Two steps are
formalized differently from the sketch. The proof that every element of the kernel of the
Galois image lies in `W_{E_w}` uses the surjectivity of `F_v ⊗_F E → ∏ E_q` instead of a
density argument in the Galois group. The descent to the decomposition group passes to the
fixed field `K` of the image and applies `H¹ = 0` for `E/K`.
