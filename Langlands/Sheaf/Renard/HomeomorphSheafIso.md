# Isomorphisms of sheaves over a homeomorphism

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This file covers the last two paragraphs of II.2.5, printed pp.42–43 / PDF pp.48–49:

> Soit γ : X → Y un homéomorphisme entre espaces topologiques t.d. Ceci induit un
> isomorphisme d'algèbres D(Y) ≃ D(X) grâce auquel nous identifions D(X) et
> D(Y)-modules. Soient X et Y deux espaces topologiques t.d. et soient F, E deux
> faisceaux dans C^∞_X-Mod(X) et C^∞_Y-Mod(Y) respectivement. Un isomorphisme entre F
> et E est donc la donnée d'un homéomorphisme γ : X → Y et d'un isomorphisme de
> D(X)-modules entre F_c(X) et E_c(Y). Il est clair que ceci induit un isomorphisme de
> C-espaces vectoriels F_x → E_γ(x) pour tout x ∈ X. Si γ : F → E est un tel
> isomorphisme, on note encore γ : E_c(Y)* → F_c(X)* son transposé.

The file gives this definition, the stalk isomorphisms and the transpose. Everything
here is either a definition or proved in the file. It adds no proposition for a later
proof task.

## Setting

A sheaf in `C^∞_X-Mod(X)` is the published
`VectorSheafScalars.VectorSheaf X`, a Mathlib sheaf of complex vector spaces. The
II.2.5 Proposition (`VectorSheafScalars`) makes these the same objects. Its compact
sections `F_c(X)` are the published `CompactSupport.submodule F.presheaf`, a
`Submodule ℂ` of the global sections. Renard's `D(X)` is the published pointwise test
algebra `PointwiseTestAlgebra.Carrier X`. It acts on `F_c(X)` by the published instance
of `CompactSectionTestModule`. As there, `X` and `Y` live in `Type`. The test-algebra
part (`testComap`, `testRingEquiv`, `transportModule`) is universe-polymorphic.

Renard assumes throughout that `X` and `Y` are t.d. (totally disconnected and locally
compact). The definitions below do not need this. The results that use it take
`hX : Langlands.Topology.IsLocallyProfinite X` (and `hY` for `Y`), the Library's
predicate for t.d. spaces.

## The algebra isomorphism `D(Y) ≃ D(X)`

- `testComap γ : D(Y) →ₙₐ[ℂ] D(X)` sends `g` to `g ∘ γ`. Its values are given by
  `testComap_apply`. It is Mathlib's `LocallyConstant.comap` along `γ`; compact support
  is preserved by Mathlib's `HasCompactSupport.comp_homeomorph`.
- `testComap_symm_testComap` and `testComap_testComap_symm` show that `testComap γ.symm`
  is inverse to `testComap γ`. `testRingEquiv γ : D(Y) ≃+* D(X)` packages Renard's
  algebra isomorphism. It is also complex-linear, since `testComap γ` is.
- `transportModule γ M` is the identification of `D(Y)`-modules with `D(X)`-modules.
  A `D(Y)`-module `M` becomes a `D(X)`-module by `f · m = (f ∘ γ⁻¹) · m`
  (`transportModule_smul`). It is a definition, not a global instance, since it depends
  on `γ`.

## The definition

`SheafIso F E`, for `F : VectorSheaf X` and `E : VectorSheaf Y`, is a structure with
three fields:

- `homeomorph : X ≃ₜ Y`, the homeomorphism `γ`;
- `sectionEquiv`, an additive isomorphism `F_c(X) ≃ E_c(Y)`;
- `map_smul'`: `sectionEquiv (f • s) = (f ∘ γ⁻¹) • sectionEquiv s` for all `f ∈ D(X)` and
  compact sections `s`. This is `D(X)`-linearity when `E_c(Y)` is a `D(X)`-module through
  `D(X) ≃ D(Y)`.

The section isomorphism is additive, as in the published nondegenerate module
categories (`NonUnitalModuleHom`): an isomorphism of `D(X)`-modules is an additive
bijection that commutes with the action. Complex linearity is not part of the data. On
t.d. spaces it follows from `D(X)`-linearity (below). Renard does not say whether
"isomorphisme de D(X)-modules" includes complex linearity. On t.d. spaces the two
readings give the same structures.

Basic API:

- `map_smul` restates the field. `map_testComap_smul` gives the version with
  `g ∈ D(Y)`: `Φ((g ∘ γ) · s) = g · Φ(s)`.
- `toModuleHom` is the section isomorphism as a published `NonUnitalModuleHom` of
  `D(X)`-modules, with `transportModule` on the target (`toModuleHom_apply`).

The following are not in the source. They check that the notion behaves as an
isomorphism:

- `refl F` is the identity over `Homeomorph.refl X`.
- `symm Φ : SheafIso E F` is the inverse over `γ⁻¹` (`symm_homeomorph`,
  `symm_sectionEquiv`).
- `trans Φ Ψ` is the composite over `γ` followed by `γ'` (`trans_homeomorph`,
  `trans_sectionEquiv`).
- `ofIso φ`, for an ordinary isomorphism `φ : F ≅ G` of sheaves on `X`, is the
  isomorphism over the identity of `X`. Its section map is the published
  `CompactSupport.map φ.hom` (`ofIso_sectionEquiv_apply`). Its test-linearity is the
  published `CompactSectionTestModule.compactSectionMap`.

## Complex linearity

`map_complex_smul hX` proves `Φ(c • s) = c • Φ(s)` for `c ∈ ℂ`, when `X` is t.d. The
published `CompactSectionTestModule.isNondegenerate` gives an idempotent `e ∈ D(X)` with
`e · s = s`. Then `c • s = (c • e) · s`, `D(X)`-linearity moves `c • e` across `Φ`, and
complex linearity of `testComap` and of the action on `E_c(Y)` finishes the computation.

`linearEquiv hX` is the section isomorphism as a complex-linear equivalence
`F_c(X) ≃ₗ[ℂ] E_c(Y)` (`linearEquiv_apply`, `linearEquiv_symm_apply`).

## Stalks

Renard says it is clear that `Φ` induces complex isomorphisms `F_x → E_{γ(x)}`. The file
builds them from the Remark just before this passage, which describes stalks as
quotients of compact sections. The Remark is published as
`CompactSectionStalks.stalkQuotientMap`, with the bijectivity statement
`CompactSectionStalksStatement.StalkQuotientComparison`, proved as
`CompactSectionStalks.stalkQuotientComparison` (`CompactSectionStalksProof`).

- `vanishingSpan_le_comap hX x`: `Φ` sends the generators `f · s` with `f(x) = 0` to
  `(f ∘ γ⁻¹) · Φ(s)` with `(f ∘ γ⁻¹)(γ(x)) = 0`. So it sends the published
  `vanishingSpan F x` into `vanishingSpan E (γ x)`.
- `map_vanishingSpan hX hY x`: the image is exactly `vanishingSpan E (γ x)`. The reverse
  inclusion applies the previous lemma to `symm Φ`.
- `quotientEquiv hX hY x` is the induced complex isomorphism of quotients
  `F_c(X)/⟨f · φ, f(x) = 0⟩ ≃ E_c(Y)/⟨g · ψ, g(γ(x)) = 0⟩` (Mathlib's
  `Submodule.Quotient.equiv`). `quotientEquiv_mk` gives its values on classes.
- `stalkQuotientEquiv hZ G z` is the published comparison map as a linear equivalence
  (`LinearEquiv.ofBijective` with `stalkQuotientComparison`). `stalkQuotientEquiv_mk`
  gives its values on classes: the germ of the section.
- `stalkEquiv hX hY x : F.presheaf.stalk x ≃ₗ[ℂ] E.presheaf.stalk (γ x)` is Renard's stalk
  isomorphism. It is the inverse comparison at `x`, then `quotientEquiv`, then the
  comparison at `γ(x)`. Stalks are Mathlib's colimit stalks.
- `stalkEquiv_germ`: `stalkEquiv` sends the germ at `x` of a compact section `s`
  (published `CompactGerms.germ`) to the germ at `γ(x)` of `Φ(s)`.
- `eq_stalkEquiv`: every complex-linear map `F_x → E_{γ(x)}` with this germ property
  equals `stalkEquiv`. Every germ at `x` comes from a compact section, by the published
  `CompactGerms.germ_surjective`. So the stalk isomorphism is determined by `Φ` and does
  not depend on the route through the quotients.

## Transposes

`transpose hX : E_c(Y)^* ≃ₗ[ℂ] F_c(X)^*` is the transpose `T ↦ T ∘ Φ` of `linearEquiv hX`
(Mathlib's `LinearEquiv.dualMap`). Here `^*` is Mathlib's algebraic dual
`Module.Dual ℂ`, as in Renard's definition of distributions on `F` (printed p.42 / PDF
p.48: "il s'agit ici du dual algébrique"). Renard writes the transpose as `γ` again;
the file calls it `transpose`. Since `Φ` is an isomorphism, the transpose is a linear
equivalence, not only a linear map.

- `transpose_apply`: `transpose hX T s = T (Φ s)`.
- `transpose_testComap_smul`: for `g ∈ D(Y)`,
  `⟨transpose T, (g ∘ γ) · s⟩ = ⟨T, g · Φ(s)⟩`. This is the compatibility of the
  transpose with the test actions that define the module structure on distributions.

This file does not define the space of distributions on `F` or its
`C^∞(X)`-module structure (the Definition on printed p.42). That item belongs to
Worker 1222's part of Task 1222. `transpose` works on the plain algebraic dual, which is
the underlying space of that definition. Compatibility of the transpose with the
`C^∞`-module structure can be stated once that definition is published.

## Provenance and scope

The structure `SheafIso` and the transpose follow the source directly. The source's
"Il est clair" is made explicit through the published Remark comparison. The following
are internal additions with no source counterpart: `testRingEquiv` as a packaged ring
isomorphism, `toModuleHom`, the operations `refl`, `symm`, `trans`, `ofIso`, the uniqueness
lemma `eq_stalkEquiv`, and `transpose_testComap_smul`. The additive section field with
derived complex linearity is a formalization choice, explained above.

Worker 4 wrote this file for Task 1222. Worker 1222 assigned this II.2.5 item to them.
