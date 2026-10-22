# Smoothness of Galois actions on étale cohomology with constant coefficients

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition. Worker 13's published
`Langlands.Geometry.EtaleGaloisAction` lets the group `L ≃ₐ[K] L` of
`K`-automorphisms of `L` act on the étale cohomology of a base change
`X ×_{Spec K} Spec L` with constant coefficients. The proposition says that
this action is smooth for the Krull topology when `L / K` is algebraic and
`X → Spec K` is quasi-compact and quasi-separated: every cohomology class is
fixed by an open subgroup. Worker 13's Markdown lists continuity for the Krull
topology as not treated there. This module states it. Nothing is proved here.

## Objects

All types live in one universe `u`.

- `K` and `L` are fields with `[Algebra K L]` and `[Algebra.IsAlgebraic K L]`.
- `f : X ⟶ Spec (CommRingCat.of K)` is a morphism of Mathlib schemes with
  `[QuasiCompact f]` and `[QuasiSeparated f]`.
- `R` is a commutative ring, `M : ModuleCat R` and `n : ℕ` are arbitrary.
- `galoisCohomologyRep (L := L) f R M n : Rep R (L ≃ₐ[K] L)` is Worker 13's
  representation. Its underlying module is the degree-`n` cohomology of the
  base change `X_L := baseChange K L f`, the pullback of `f` and
  `Spec.algebraMap K L`. The cohomology is that of Worker 13's
  `Langlands.Geometry.EtaleDerivedSections`: Mathlib's small étale site
  `X_L.smallEtaleTopology`, sheaves of `R`-modules, and the constant sheaf of
  `M`. It is computed by applying sections over the final object to an
  injective resolution. `EtaleCohomologyAction.constantCohomologyIso`
  identifies this module with `EtaleDerivedSections.constantCohomology`.
- The action. `galoisAut f σ` is `op (baseChangeAut f σ)`. The automorphism
  `baseChangeAut f σ` of `X_L` has underlying morphism `baseChangeMap f σ`,
  the identity on `X` times `Spec σ` on `Spec L`, and inverse
  `baseChangeMap f σ⁻¹`. For an automorphism `a` of `X_L`, the translate of a
  sheaf `F` has sections `F(U, u ≫ a.hom)` over `(U, u)`; this is the pullback
  `a^*F`. Worker 13's `TranslationCoaction.cochainMap` for `a` lifts the
  canonical map from the constant sheaf to its translate to the injective
  resolution, applies sections over the final object, and then applies
  `EtaleAutomorphism.sectionsIso a`. That isomorphism restricts along
  `(terminalIso a).inv`. If `q` is the structure map of the chosen final
  object, the underlying scheme map of `(terminalIso a).inv` followed by `q`
  is `q` followed by `a.inv`. So in degree zero `cochainMap` for `a` sends a
  section of the constant sheaf, a locally constant function `s` on `X_L`, to
  `s ∘ a⁻¹`. `coCohomologyAction` uses `cochainMap` for the automorphism
  attached to `σ⁻¹`, that is `a = baseChangeAut f σ⁻¹`, whose inverse is
  `baseChangeMap f σ`. Hence `σ` acts on `H^0` by
  `s ↦ s ∘ baseChangeMap f σ`, the pullback along `baseChangeMap f σ`. This
  is a left action, since `baseChangeMap f σ ≫ baseChangeMap f τ =
  baseChangeMap f (σ * τ)`. In every degree, `σ` acts by the canonical
  pullback map along `baseChangeMap f σ`. This is derived, not part of the
  Lean code. For a coefficient sheaf `G`, the comparison
  `H^•(X_L, a^*G) ≅ H^•(X_L, G)` given by `sectionsIso a` on a translated
  injective resolution, and the pullback `H^•(X_L, G) → H^•(X_L, a^*G)` along
  `a`, are both compatible with connecting maps. In degree zero they are
  restriction along `(terminalIso a).inv` and along `(terminalIso a).hom`,
  so they are mutually inverse there. By universality of `H^•(X_L, -)`
  (Tôhoku Proposition 2.2.1) they are mutually inverse in every degree. The
  pullback along `a` on `H^•(X_L, M)` is the pullback to
  `H^•(X_L, a^*M)` followed by the inverse of the isomorphism induced by the
  canonical map `M → a^*M`. So `cochainMap` for `a` induces the inverse of
  the pullback along `a`, which is the pullback along `a⁻¹`. For
  `a = baseChangeAut f σ⁻¹` this is the pullback along `baseChangeMap f σ`.
- The topology on `L ≃ₐ[K] L` is Mathlib's `krullTopology K L`, the only
  topology instance there. `galGroupBasis K L` is the group filter basis of
  the subgroups `E.fixingSubgroup` for intermediate fields `E` with
  `FiniteDimensional K E`. `IntermediateField.fixingSubgroup_isOpen` proves
  these subgroups open.
- `Langlands.IsSmooth ρ` is the Library's smoothness: every vector `v` has an
  open subgroup `U` with `ρ g v = v` for all `g ∈ U`.

## The proposition

```lean
def GaloisCohomologySmoothStatement (K : Type u) [Field K] (L : Type u) [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact f] [QuasiSeparated f]
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) (n : ℕ),
    Langlands.IsSmooth (galoisCohomologyRep (L := L) f R M n).ρ
```

In words: for an algebraic field extension `L / K`, a quasi-compact
quasi-separated `K`-scheme `X`, any commutative ring `R`, any `R`-module `M`
and any degree `n`, every class in `H^n(X_L, M)` is fixed by an open subgroup
of `L ≃ₐ[K] L`.

The proposition is universally quantified over `M` and `n`. `K`, `L`, `f` and
`R` are parameters. The argument `L` of `galoisCohomologyRep` must be given by
name, since it is implicit there and is not determined by `f`.

## Why the statement is expected to hold

This argument is derived. It combines the cited results of SGA 4 and is not a
quotation.

1. *Reduction to finite subextensions.* Let `E` range over the intermediate
   fields with `FiniteDimensional K E`. By the definition of the Krull
   topology, `E.fixingSubgroup` is open. It suffices to find, for each class
   `c`, such an `E` with `E.fixingSubgroup` fixing `c`.
2. *The base change is a limit.* Since `L / K` is algebraic, every element of
   `L` lies in a finite-dimensional subextension, and two of them lie in their
   finite-dimensional compositum. So `L` is the filtered union of the `E`. Put
   `X_E = X ×_{Spec K} Spec E`. Each `X_E` is quasi-compact and
   quasi-separated: `X_E → Spec E` is a base change of `f`, both properties
   are stable under base change, and `Spec E` is affine. The transition maps
   `X_{E'} → X_E` for `E ⊆ E'` are base changes of the affine morphisms
   `Spec E' → Spec E`, hence affine. The limit of the system is
   `X ×_{Spec K} Spec L = X_L` (SGA 4 VII 5.1 for the existence and
   description of such limits).
3. *The limit theorem.* SGA 4 VII Theorem 5.7 and Corollary 5.8 apply to a
   filtered preordered system with affine transitions of quasi-compact
   quasi-separated schemes. Corollary 5.8 takes `F_E = u_E^*(F_K)` for a sheaf
   `F_K` on `X_K = X` and says that the canonical map
   `colim_E H^n(X_E, F_E) → H^n(X_L, F_L)` is an isomorphism. Take `F_K` the
   constant sheaf `M`. Its inverse images are constant: inverse image is left
   adjoint to direct image, the constant sheaf functor is left adjoint to
   global sections, and direct image preserves global sections. Hence every
   `c` is the pullback `p_E^*(c_E)` of a class `c_E ∈ H^n(X_E, M)` along the
   projection `p_E : X_L → X_E`, for some `E`.
4. *Comparison of sites and coefficients.* SGA 4 VII 1.2 defines the étale
   site of `X` as all étale `X`-schemes, with the surjective families of étale
   maps as coverings. Mathlib's `smallEtaleTopology` is the same: its category
   `X.Etale` is all étale `X`-schemes, and its topology is induced from
   `Scheme.etaleTopology`, generated by jointly surjective families of étale
   morphisms. SGA 4 computes cohomology of abelian sheaves. The Lean
   cohomology is computed with sheaves of `R`-modules. These agree. An
   injective sheaf of `R`-modules is flasque (SGA 4 V 4.6), flasqueness
   depends only on the underlying abelian sheaf (V 4.4), and flasque means
   acyclic (V 4.1). So an injective resolution of `R`-module sheaves is an
   acyclic resolution of the underlying abelian sheaves, and it computes their
   cohomology (Tôhoku 2.4, Remark 3).
5. *Classes from `X_E` are fixed by `E.fixingSubgroup`.* Let `σ` fix `E`
   pointwise and let `τ = baseChangeMap f σ`, so that `σ` acts by `τ^*`.
   Then `p_E ∘ τ = p_E`: on the factor `X` both sides are the identity, and
   `Spec σ` followed by `Spec L → Spec E` is `Spec L → Spec E` because `σ`
   is the identity on `E`. Pullback maps on cohomology are compatible
   with composition. Both `c_E ↦ τ^*(p_E^*(c_E))` and `c_E ↦ (p_E ∘ τ)^*(c_E)`
   extend to morphisms of δ-functors in the coefficient sheaf on `X_E`, from
   `H^•(X_E, -)` to `H^•(X_L, p_E^*(-))`. They agree in degree zero. The
   source is a universal δ-functor, so they agree in all degrees (Tôhoku
   Proposition 2.2.1). Hence `σ · c = τ^*(p_E^*(c_E)) = p_E^*(c_E) = c`.

By step 1, `c` is a smooth vector. The ring `R`, the module `M` and the degree
`n` play no role. No finiteness, torsion or characteristic hypothesis is
needed.

## The hypotheses cannot simply be dropped

These examples are derived; they show why the hypotheses are present.

*Algebraicity.* Take `K = ℚ`, `L = ℚ(t)`, `X = Spec ℚ`, `f = 𝟙`,
`R = M = ℤ/2` and `n = 1`. A finite-dimensional subextension of `ℚ(t)`
consists of rational functions algebraic over `ℚ`, which are constants. So
every basic subgroup of the Krull topology is the whole group, and the only
open subgroup is `ℚ(t) ≃ₐ[ℚ] ℚ(t)`. Smoothness would force every class to be
fixed by every automorphism. By SGA 4 VIII Corollary 2.3, `H^1` of
`Spec ℚ(t)` with coefficients `ℤ/2` is Galois cohomology. By Kummer theory
(Serre, *Galois Cohomology*, II.1.2, Corollary and Remark 2) it is
`ℚ(t)^×/ℚ(t)^{×2}`. Both identifications are canonical and functorial in the
field (Serre II.1.1), so they transport the action. Here `X_L` is
canonically isomorphic to `Spec ℚ(t)`, and under this isomorphism
`baseChangeMap f σ` is `Spec σ`. By the convention above,
the automorphism `σ : t ↦ t + 1` acts by pullback along `Spec σ`, which on
Kummer classes is `x ↦ σ(x)`. So it sends the class of `t` to the class of
`t + 1`. The product `t(t + 1)` is not a square in `ℚ(t)`, by unique
factorisation in `ℚ[t]`. So the class of `t` is not fixed, and smoothness
fails.

*Quasi-compactness.* Take `K = ℚ`, `L` an algebraic closure of `ℚ`,
`K_i = ℚ(2^{1/i})` of degree `i` for `i ≥ 1`, and `X` the disjoint union of
the `Spec K_i` with its map to `Spec ℚ`. This map is quasi-separated, since
an affine open of `X` meets only finitely many components, but not
quasi-compact. Take `R = M = ℤ/2` and `n = 0`. The base change `X_L` is the
disjoint union over `i` of one copy of `Spec L` for each embedding
`τ : K_i → L`. A global section of the constant sheaf is a function from these
points to `ℤ/2`. Identify the component over `Spec K_i` with
`Spec (K_i ⊗_ℚ L)`. The point indexed by `τ` is the kernel of
`K_i ⊗_ℚ L → L`, `a ⊗ b ↦ τ(a) b`, and `baseChangeMap f σ` is `Spec` of
`id ⊗ σ`. Since `τ(a) σ(b) = σ(σ⁻¹(τ(a)) b)`, it sends the point indexed
by `τ` to the point indexed by `σ⁻¹ ∘ τ`. By the convention above, `σ`
sends the indicator function of a set `S` of embeddings to the indicator
function of `{σ ∘ τ : τ ∈ S}`. Choose one embedding `τ_i` for each `i` and
let `c` be the indicator function of `{τ_i}`. An element `σ` fixing `c`
satisfies `σ ∘ τ_i = τ_i` for every `i`, since `σ ∘ τ_i` is again an
embedding of `K_i`. Hence `σ` fixes every field `τ_i(K_i)` pointwise. An open subgroup contains
`E.fixingSubgroup` for some finite `E`. If that subgroup fixes `c`, Galois
theory for `L / ℚ` gives `τ_i(K_i) ⊆ E` for all `i`, so `[E : ℚ] ≥ i` for all
`i`, which is impossible. So `c` is not a smooth vector.

The module does not claim that quasi-separatedness is necessary. It is a
hypothesis of SGA 4 VII 5.7.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §5, printed p.313, works with "λ-adic representations σ of
Gal(F̄/F)". Theorem 5.7 there concerns the representation of `Gal(F̄/F)` on
`H^{n-1}(S_K(N), W)[π]`. These are continuous representations. At a finite
level of torsion coefficients, continuity of an action on a discrete module is
exactly the smoothness stated here. Harris does not state this smoothness as a
separate result. This module isolates that standard input for constant
coefficients on an arbitrary quasi-compact quasi-separated scheme. Its
truth argument follows SGA 4 VII §5.

| Lean | Source |
| --- | --- |
| `Algebra.IsAlgebraic K L`, `L` as a filtered union of the finite subextensions | Derived; needed to write `X_L` as a limit of the `X_E` |
| `[QuasiCompact f]`, `[QuasiSeparated f]` | SGA 4 VII Theorem 5.7, hypothesis that the `X_i` are quasi-compact and quasi-separated |
| `galoisCohomologyRep (L := L) f R M n` | Worker 13's representation; the cohomology of SGA 4 VII 1.2 by step 4 |
| `Langlands.IsSmooth` for `krullTopology K L` | Every class is fixed by `Gal(L/E)` for a finite `E`; derived from SGA 4 VII Corollary 5.8 |
| `∀ M n` | Corollary 5.8 holds for every sheaf `F_{i0}` and every degree |

## Scope

The statement does not cover:

- non-constant coefficient sheaves, ℓ-adic systems or inverse limits over
  coefficients;
- compact supports and Hecke operators;
- Shimura varieties, Harris's coefficient systems `W`, or Weil-group
  actions;
- analytic spaces or Berkovich's étale site;
- continuity of the action for any topology on the cohomology module other
  than the discrete one.

When `L` is a separable closure of `K`, `L ≃ₐ[K] L` is the absolute Galois
group with its profinite topology, and the statement is smoothness of the
usual Galois action. When `L / K` is finite, the Krull topology is discrete and
the statement is immediate.

## Registered sources

- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`.
  Read on the scanned pages (PDF page = printed page + 2):
  - Exposé V (Verdier): Definition 4.1, 4.4 and 4.6, printed pp.29-30;
  - Exposé VII (Grothendieck): 1.2, printed p.343;
  - VII 5.1, printed pp.356-357;
  - VII Theorem 5.7, printed p.361;
  - VII Corollary 5.8, printed p.362;
  - Exposé VIII: Proposition 2.1, printed p.370;
  - VIII Corollaries 2.2 and 2.3, printed p.371.
- `serre-1997-galois-cohomology`: Serre, *Galois Cohomology*, corrected
  second printing 2002, SHA-256
  `343aafc5fe7ebb6605effc6f6e09338f622bb977325e8cdd166152cbd6eb7cf2`.
  Chapter II, §1.1 (functoriality in the field), printed p.72, and §1.2,
  Corollary to Proposition 1 and Remark 2, printed pp.72-73 (PDF pp.79-80).
  Read in the text layer. Used only in the first counterexample.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Proposition 2.2.1, printed p.141 (PDF p.23), and §2.4, Remark 3 after
  Theorem 2.4.1, printed p.148 (PDF p.30). Used only in the truth argument.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; §5,
  printed p.313 (PDF p.15), for provenance only.

## Formal dependencies and checks

Direct project imports, byte-identical in Library commits
`55cf6172e313c02aa8f5978501d957bfa08de20d`,
`c5a40b0f54880b1825ea05214c2b066f68bfc156` and
`bd3d155f1f3eb32c90b044cd3bf1e992e726beb7`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Geometry.EtaleGaloisAction` | Worker 13 | `5d07cffce7425cbd24204e0f65a5ca913c1570e7c5621aae229d13beb0e581fa` | `d9c5b185b7b92d780aeceaa828ac8440c29a30872c2099428cd5a5776dc885f6` |
| `Langlands.Representation.Smooth.Definitions` | Library | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |

The module also imports Mathlib's `Mathlib.FieldTheory.KrullTopology`. Through
the first import it uses Worker 13's `EtaleConstantCohomology`,
`EtaleCohomologyAction`, `TranslationCoaction` and `EtaleDerivedSections`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Check `8decd98d-579f-4a37-b52f-cbe6681ed768` built this Lean file from a
draft directory against the published imports, with no errors or warnings.
Check `33c91a95-4b6f-4062-b1c1-6dd468f2c6d1` built the same file with Lake
from the workspace, against Library `c5a40b0f`, with no errors or warnings.
Check `40e1a25b-9595-4cba-96c3-d29c1810f846` built the same file with Lake
from the workspace, against Library `bd3d155f`, with no errors or warnings.
All three inspected `GaloisCohomologySmoothStatement` as a `Prop`-valued
definition with the single universe parameter `u`, depending only on
`propext`, `Classical.choice` and `Quot.sound`. Check
`bd4b1848-5ad0-44c3-a0d9-e6fe53910177` compiled a test file against the same
Lean file, with no errors or warnings, and its output was read. It printed the
definition with universes: all binders listed above are present, and the
body is `Langlands.IsSmooth` of `galoisCohomologyRep f R M n`. The same file
proves that the proposition is equivalent to the explicit form "for all `M`,
`n` and `v`, some open subgroup `U` has `ρ σ v = v` for all `σ ∈ U`". It
elaborates the proposition for `ℚ`, `AlgebraicClosure ℚ`, the identity of
`Spec ℚ` and `ZMod 2`. It checks that `E.fixingSubgroup` is open for
finite-dimensional `E`. This establishes a well-formed statement. It does not
prove it.
