# Relative derivations on schemes

For an arbitrary morphism `f : X ⟶ S` of `Scheme.{u}`, the type
`Langlands.Scheme.RelativeDerivation f M` has an actual `X.Modules` object as
its target. It is Mathlib's `PresheafOfModulesOfCommRing.Derivation` applied to
the underlying module presheaf, the inverse-image functor on opens, and the
structure morphism `f.c : O_S ⟶ f_* O_X`. It consists of additive maps on every
open of `X`, compatible with restriction, satisfying the Leibniz rule and
vanishing on the image of every base section on an open of `S`.

This is the local-section presentation of the relative derivations of the
Stacks Project, Section 17.28, Definitions 17.28.1 and 17.28.10, specialized
to schemes as in Section 29.33, Definition 29.33.1. A section of the inverse
image sheaf `f⁻¹O_S` is locally represented by a base section on an open `U`
of `S`, restricted to an open `V ⊆ f⁻¹U`. The implemented lemma
`RelativeDerivation.app_base_restrict` proves vanishing on each such
representative. Since the target is a sheaf, local vanishing gives vanishing
on the image of every inverse-image-sheaf section. Conversely, that latter
vanishing condition includes the base sections on `f⁻¹U`. This explains
the agreement with the inverse-image definition; this file does not formalize
an equivalence with a separate Lean inverse-image-sheaf derivation type.

`RelativeDerivation.app` exposes the local additive maps.
`app_add`, `app_mul`, `app_restrict`, and `app_base` are direct specializations
of Mathlib's derivation laws. `app_base_restrict` follows by restriction
compatibility and preservation of zero. `postcomp` uses the underlying
morphism of module presheaves of an actual sheaf morphism. Its identity and
composition laws follow by extensionality on local sections.
`relativeDerivationFunctor` packages this operation as a functor to `Type u`,
as in the discussion after Definition 17.28.1 and in Lemma 29.33.2.

No cotangent sheaf, universal property, pullback map of cotangent sheaves,
base-change theorem, or quasicoherence assertion is supplied by this file.
It is the definition interface for those subsequent constructions.

## Sources

- Registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
  content SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`:
  `08RL.html`, Definitions 17.28.1 and 17.28.10 and the discussion following
  Definition 17.28.1; `01UM.html`, Definition 29.33.1 and Lemma 29.33.2.
- Implementation uses Mathlib at commit
  `5ed2965256430c3649e86755f9576b54eca72435`,
  `Algebra/Category/ModuleCat/Differentials/Presheaf.lean` and
  `AlgebraicGeometry/Modules/Sheaf.lean`.
