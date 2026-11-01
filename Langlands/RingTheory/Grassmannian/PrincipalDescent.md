# Finite principal-open descent for quotient Grassmannians

The paired Lean file constructs and proves uniqueness of a quotient
Grassmannian element from compatible elements on a finite principal-open
cover. Its primary construction is
`Module.Grassmannian.PrincipalDescent.gluedGr`; its exported theorem is
`Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away`.
It uses Mathlib's quotient convention: a Grassmannian element is a submodule
whose quotient is finite projective of constant stalk rank `k`.

The source is the registered distribution
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, distribution SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete original files were read:

- `P2M/Sol/S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away.lean`,
  lines 1–310, SHA-256
  `6dd972e379cc228fc73e95c492ca13c4077e468a28bd468ebb0f7e7c992087fa`.
- `Theorems/Thm_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away.lean`,
  lines 1–20, SHA-256
  `cb69af59f775f41d1ddac0ce1be749be7f9af7232f56842b224945a377d7b344`.

## Inputs and conclusion

All ring and module carriers are universe-zero types, as in the original.
Let `R` be a commutative ring, `M` an arbitrary `R`-module, and `A` a
commutative `R`-algebra. Fix natural numbers `k` and `n`, and
`f : Fin n → A` with `Ideal.span (Set.range f) = ⊤`. For each `i`, supply a
commutative ring `B i` with compatible `A`- and `R`-algebra structures,
the scalar tower `R → A → B i`, and
`IsLocalization.Away (f i) (B i)`. Supply

```text
N i : Module.Grassmannian (B i) (B i ⊗[R] M) k.
```

The compatibility hypothesis requires equality of the two mapped
Grassmannian elements for every `i,j`, every commutative `R`- and
`A`-algebra `C` with compatible scalar tower and
`IsLocalization.Away (f i * f j) C`, and every pair of `A`-algebra
homomorphisms `ρ₁ : B i →ₐ[A] C`, `ρ₂ : B j →ₐ[A] C`. The maps used in
that equality are `ρ₁.restrictScalars R` and `ρ₂.restrictScalars R`.
`Cocycle` abbreviates precisely this proposition.

The theorem concludes that there exists exactly one
`N₀ : Module.Grassmannian A (A ⊗[R] M) k` satisfying

```text
∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i)) N₀ = N i.
```

Neither `M` nor `A ⊗[R] M` is assumed finite, finitely presented, free,
or projective. These properties are required only of the local quotients
as encoded by the Grassmannian elements. There is no nontriviality
hypothesis on the rings, no positivity assumption on `k` or `n`, and no
requirement that `f` be injective. An empty cover must still satisfy the
unit-ideal hypothesis.

## Construction and proof

Write `l_i : A ⊗[R] M →ₗ[A] B i ⊗[R] M` for `l R M A (B i)`.
On pure tensors it sends `a ⊗ m` to `algebraMap A (B i) a ⊗ m`.
The structure-map lemmas prove composition in a scalar tower and identify
the kernel of Mathlib's `baseChangeMkQ` with the localized submodule.
`map_toSubmodule'` explicitly reconciles the supplied algebra structure
with the structure induced by a quantified algebra homomorphism.

The glued kernel and its quotient are

```text
K  = ⋂ i, l_i⁻¹((N i).toSubmodule),
Q₀ = (A ⊗[R] M) / K.
```

These are `glued` and `Q0`. The intersection uses restriction of scalars
of the local kernels to `A`; `mem_glued` gives its elementwise criterion.
The following steps prove that `K` has the required quotient properties.

1. `exists_pow_smul_mem` clears one overlap denominator. If `l_i m`
   belongs to the `i`th kernel, localize `B j` at the image of `f i`.
   The cocycle makes the image of `m` vanish in the corresponding
   localized `j`th quotient. The localization zero criterion supplies an
   exponent `a` with `l_j (f i ^ a • m)` in the `j`th kernel.
2. `localized'_glued` proves that localizing `K` at `f i` gives exactly
   `(N i).toSubmodule`. One inclusion follows from the definition.
   For the reverse, express a local element as a fraction, clear its
   denominator, and choose an exponent for each `j` using step 1.
   Their finite supremum works for all `j`, giving a numerator in `K`.
3. `gq` identifies each local quotient as a localized module of `Q₀`.
   The auxiliary choice `idx` selects an original index for each element
   of `Set.range f`, allowing repeated cover elements. Mathlib's
   `Module.Finite.of_localizationSpan'` and
   `Module.FinitePresentation.of_localizationSpan'` give finiteness and
   finite presentation of `Q₀`. Each local quotient is finite projective
   and hence finitely presented.
4. `projective_localizedModule` transports local projectivity to
   `LocalizedModule.Away (f i) Q₀` through the canonical equivalence
   between the supplied and standard localization rings. Every prime
   avoids some `f i`, by the unit-ideal condition. The basic-open
   free-locus criterion and `Module.freeLocus_eq_univ_iff`, using the
   finite presentation already proved, give `Module.Projective A Q₀`.
5. `baseChangeEquiv` identifies `B i ⊗[A] Q₀` with the `i`th local
   quotient. For each prime of `A`, choose a covering localization and a
   prime above it. Mathlib's rank base-change and linear-equivalence
   formulas transfer `(N i).rankAtStalk_eq`, proving stalk rank `k`.

`gluedGr` packages `K` with the proved finiteness, projectivity and
rank fields. In the exported theorem, the kernel/localization comparison
and step 2 show that its Grassmannian base changes are the specified
`N i`. For uniqueness, any other candidate has the same localized
submodules. `Submodule.eq_of_isLocalized'_span` gives equality of the
global kernels, and Grassmannian extensionality gives equality of the
elements.

## Scope and adaptation

This pair supplies the finite principal-localization descent input needed
to apply the algebra-functor sheaf extension to the quotient Grassmannian
functor. It does not yet construct a representing scheme for that functor
or a projective embedding. The division-CM target still requires an actual
moduli construction, admissibility, smoothness, projectivity and the
natural comparison with the existing normalized CM presheaf.

Worker 344 adapted the original solution and wrapper for Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`:

- Replace the aggregate Mathlib and `P2M.Util` imports with the four
  focused Mathlib imports in the paired Lean file. Replace the generated
  `P2MW` namespace, `p2m_reactivate` and wrapper dispatch with the ordinary
  helper namespace `Module.Grassmannian.PrincipalDescent` and exported
  theorem name. The helper namespace was originally `GrassSheafS1b`.
- Use the current `TensorProduct.inductionOn` in two proofs. Its pure
  tensor and sum cases include zero, so the two explicit old zero cases
  are removed.
- Change one proof-local `letI` to `let` and eleven proof-local `haveI`
  declarations to `have`. The same local algebra and scalar-tower
  structures, and the same local instances, are used.
- Remove the duplicated `omit [CommRing A] in` and the unused
  `IsLocalization.map_id_mk'` simplification argument.

The exported signature is byte-identical to the original wrapper's
signature. The actual localized kernels, quotient maps, exponent
argument and local-to-global quotient proofs are retained. These edits
add no hypotheses and change no universes or conclusions.

The original distribution is released under
[Apache License 2.0](../../../licenses/Anthropic-FLT/LICENSE);
its [NOTICE](../../../licenses/Anthropic-FLT/NOTICE) and
[attribution table](../../../licenses/Anthropic-FLT/ATTRIBUTION.md)
are retained. Those three files are byte-identical to the pinned
distribution. The table has no separate entry for these two source files.
