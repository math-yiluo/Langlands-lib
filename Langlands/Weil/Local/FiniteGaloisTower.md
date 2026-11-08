# Inflation of finite Galois Weil classes in a tower

Author: Worker 1839, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. All
declarations are in `Langlands.Weil.Local.FiniteGaloisTower`. This module proves
the inflation relation for Weil classes in Tate, *Number theoretic background*
(1979), (1.2.4), printed p.5:

`inf α_{E/F} = [L : E] · α_{L/F}`

for actual local Weil groups. Here `α_{K/F}` is Worker 1556's
`finiteGaloisClass F K _ _ e e_rel`: the class of the extension `W_F / W_K^c` of
`Gal(K/F)` by `Kˣ`, where the identification `W_K^ab ≅ Kˣ` is the inverse of a
geometric reciprocity candidate `e`. The relation is a consequence of Artin–Tate
XIII §3, Theorems 5 and 6 (`Langlands.GroupTheory.ExtensionAkizukiWitt`), and of the
transfer–inclusion square of reciprocity for `E ⊂ L`. That square is the
published proposition `LocalClassField.ExtensionWeilTransferReciprocityStatement`,
which is taken as the hypothesis `hT`.

## Setting

All three fields are `F E L : PadicField.{u} p`, with embeddings
`f : F.Carrier →ₐ[Padic p] E.Carrier` and `g : E.Carrier →ₐ[Padic p] L.Carrier`.
`L` is an `F`-algebra through `g.comp f`, so the scalar tower holds by
definition. The hypotheses are:

- `hE`, `hL`: `E/F` and `L/F` are Galois;
- `hF1`: for all `x : E`,
  `extensionFieldEmbedding F L (g.comp f) (g x) = extensionFieldEmbedding F E f x`.
  That is, the published embedding of `L` into `\bar F` extends that of `E`.

`hF1` is a normalization of the choice of `g`. It is used only to show that the
restriction of the `L`-quotient is the `E`-quotient, and that the correction
below fixes `E`.

## The correction between direct and composite Weil maps

The published closure isomorphisms `ε_{FE}`, `ε_{EL}` and `ε_{FL}` are
independent choices. So the composite Weil map `W_L → W_E → W_F` and the direct
map `extensionWeilMap F L (g.comp f)` need not agree.

- `compositeClosureEquiv = ε_{EL} ∘ ε_{FE}`, and `compositeClosureEquiv_algebraMap`
  shows that it lies over `g ∘ f`.
- `towerCorrection = κ = ε_comp⁻¹ ∘ ε_{FL}` is an element of `G_F`. It fixes `F`
  because both isomorphisms lie over `g ∘ f`.
  `compositeClosureEquiv_towerCorrection` states `ε_comp ∘ κ = ε_{FL}`.
- `extensionGaloisMap_comp`: the composite Galois map is
  `σ ↦ κ · extensionGaloisMap F L (g.comp f) σ · κ⁻¹`. The proof evaluates both
  sides through `ε_comp`, using `extensionClosureLift_galoisMap` three times.
- `extensionWeilMap_comp`: the composite Weil map is the direct one followed by
  `galoisConjugationWeil F κ`. The Galois components agree by the previous lemma.
  The degree components then agree because `frobenius` is injective
  (`frobenius_injective`) and both elements lie in the pullback.
- `towerCorrection_fieldEmbedding`: by `hF1`, `κ` fixes the image of `E` in
  `\bar F`.

## Coefficient inflation

For a tower `K ⊂ L ⊂ M` of fields with `L/K` normal:

- `unitsInflation_equivariant`: the unit inclusion is equivariant along normal
  restriction, by `AlgEquiv.restrictNormal_commutes`.
- `relativeInflation_cohomologyClass`: the published
  `relativeInflation K L M 2` sends the class of a normalized cocycle `c` to the
  class of `NormalizedTwoCocycle.inflate (restrictNormalHom L) (Units.map algebraMap) c`.
  This is Mathlib's `groupCohomology.H2π_comp_map_apply`, since the induced map on
  cocycles is `x ↦ φ ∘ x ∘ (π × π)`.

## Quotients, kernels and sections

- `towerRestriction` is `AlgEquiv.restrictNormalHom E : Gal(L/F) → Gal(E/F)` for
  the algebra structure `g`. `towerRestriction_apply` states `g (π σ x) = σ (g x)`.
- `towerRestriction_finiteGaloisQuotient` and `towerRestriction_comp`: restriction
  of the `L`-quotient `finiteGaloisQuotient F L (g.comp f)` is the `E`-quotient
  `finiteGaloisQuotient F E f`. Both are computed through the embeddings into
  `\bar F` with `finiteGaloisQuotient_apply`, and `hF1` identifies the
  embeddings.
- `towerKernelQuotient : W_E → ker π` is `y ↦ q_L(extensionWeilMap F E f y)`.
  `towerKernelQuotient_ker` proves that its kernel is the range of
  `extensionWeilMap E L g`. For one inclusion, write the composite as the direct
  map conjugated by `κ`; conjugation by `κ` preserves the kernel of `q_L`
  (`galoisConjugationWeil_mem_ker`). For the other, conjugate by `κ⁻¹` into the
  range of the direct map, then use `extensionWeilMap_comp` and injectivity of
  `extensionWeilMap F E f`.
- `towerKernelSection h` is the `W_E`-preimage of the section value
  `finiteGaloisSection F L (g.comp f) hL h` for `h ∈ ker π`. That value lies in
  the `E`-kernel by `finiteGaloisSection_mem`. The lemmas
  `extensionWeilMap_towerKernelSection` and
  `towerKernelQuotient_towerKernelSection` say that it is a section.
- `towerKernelFintype` is the finite type structure on `ker π`.

## The transfer square in kernel coordinates

- `absoluteBaseConjugation_towerCorrection`: the restriction of `κ` to `L` fixes
  `g(E)`, by `towerCorrection_fieldEmbedding` and `hF1`.
- `transferFactor_mem`: `t(h) x t(h q(x))⁻¹` lies in `ker q` for every section
  `t`.
- `transferFactor_reciprocity`: for `y ∈ W_E` and `h ∈ ker π`, the inverse
  `L`-reciprocity of the transfer factor `t(h) y t(h q_L(y))⁻¹` equals
  `κ|_L (e_L(w))⁻¹`. Here `w ∈ W_L` is the preimage under `extensionWeilMap E L g`
  of the corresponding factor in `W_E`. The proof identifies the factor with the
  image of `finiteGaloisAbsoluteConjugation F L (g.comp f) hL κ w`, using
  `extensionWeilMap_comp`. It then applies
  `reciprocityUnits_finiteGaloisAbsoluteConjugation`.
- `towerTransfer`: under `hT`, for every `y ∈ W_E`,

  `Units.map g (r_E (j_E y)) = ∏_{h ∈ ker π} r_L ⟨t(h) y t(h q_L y)⁻¹⟩`,

  where `r_E`, `r_L` are the inverse reciprocity kernel maps
  `finiteGaloisKernelReciprocity`. The proof starts from `hT` for `g`, `e_E` and
  `e_L` at `y`. It evaluates Mathlib's transfer with
  `GroupExtensionPushout.transfer_eq_prod_section`, using `towerKernelQuotient`
  and `towerKernelSection`. Each factor is rewritten by
  `transferFactor_reciprocity`. The factors `κ|_L` combine into `κ|_L` of the
  transfer, which `κ|_L` fixes because the transfer lies in `g(Eˣ)`.

## Main theorem

`cohomologyClass_inflate_pushout_of_comp` restates the published
`cohomologyClass_inflate_pushout` for a quotient `q'` with `π ∘ q = q'`, by
substitution.

`relativeInflation_finiteGaloisClass` (under `hF1`, Galois hypotheses, geometric
candidates `e_E`, `e_L` and `hT`):

`relativeInflation F E L 2 (finiteGaloisClass F E f hE e_E he_E) =
  finrank E L • finiteGaloisClass F L (g.comp f) hL e_L he_L`.

The proof rewrites the left side with `relativeInflation_cohomologyClass`. It
applies `cohomologyClass_inflate_pushout_of_comp` with the following data:

- `q = q_L`, its section `finiteGaloisSection`, and `r = r_L` with equivariance
  `finiteGaloisKernelReciprocity_conjugateKernel`;
- `π = towerRestriction`, surjective by `AlgEquiv.restrictNormalHom_surjective`;
- `ι = Units.map (algebraMap E L)`;
- `q' = q_E` with `towerRestriction_comp`, its section and `r_E`;
- the kernel hypothesis from `towerTransfer`.

Finally, `|ker π| = [L : E]`. This follows from `Subgroup.card_mul_index`,
surjectivity of `π`, `IsGalois.card_aut_eq_finrank` for both extensions and the
tower law.

## Provenance

Derived formalization of Tate 1979, (1.2.4), source
`tate-1979-number-theoretic-background`, printed p.5 (PDF p.14). Tate cites
Artin–Tate for the first relation. The proof here instead uses Artin–Tate's theorem
on the Akizuki–Witt map, source `artin-tate-2009-class-field-theory`, Chapter XIII
§3, Theorem 6, printed pp.135–137 (PDF pp.144–146), formalized in
`ExtensionAkizukiWitt`. Tate's argument assumes the Weil-group axioms. Here
the only arithmetic input is the explicitly assumed transfer–inclusion square
`hT` for `E ⊂ L`. The construction does not assume a class identity or a map to
a prescribed extension. The correction element `κ`, the normalization `hF1` and
the coset computation are internal to this implementation.
