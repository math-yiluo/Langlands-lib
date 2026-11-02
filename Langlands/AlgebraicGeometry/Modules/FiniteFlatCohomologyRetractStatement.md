# Cohomology retraction along a finite flat morphism of invertible rank

`FiniteFlatCohomologyRetractStatement` says the following. Let `K` be a field
and `f : X → Y` a morphism of `K`-schemes. Suppose `f` is finite, flat and
locally of finite presentation, and has constant rank `d` with `d` nonzero in
`K`. Then for every quasi-coherent `𝒪_Y`-module `M` and every degree `n`, the
`K`-module `Hⁿ(Y, M)` is a retract of the `K`-module `Hⁿ(X, f^* M)`.

## The objects in the statement

- `K : Type u` is an arbitrary field in an arbitrary universe `u`.
- `X Y : Over (Spec (CommRingCat.of K))` are `K`-schemes: schemes `X.left`
  and `Y.left` with structure morphisms `X.hom` and `Y.hom` to `Spec K`.
- `f : X ⟶ Y` is a morphism in the over category, so its underlying scheme
  morphism `f.left : X.left ⟶ Y.left` satisfies `f.left ≫ Y.hom = X.hom`
  (`Over.w f`).
- `IsFinite f.left`, `Flat f.left` and `LocallyOfFinitePresentation f.left`
  are Mathlib's morphism properties of schemes in `AlgebraicGeometry`. By
  Stacks Lemma 02KB, together they say that `f.left` is finite locally free.
- `d : ℕ` with `(d : K) ≠ 0` says that `d` is nonzero in `K`. Equivalently,
  `d ≠ 0`, and the characteristic of `K` does not divide `d` when it is
  positive.
- `∀ y : Y.left, f.left.finrank y = d` is the constant-rank hypothesis. It
  uses Mathlib's `Scheme.Hom.finrank` from
  `Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`. For finite flat `f`
  it is computed over affine opens. On `Spec R ← Spec A` it is the rank of
  `A` localized at the prime `y` (`Scheme.Hom.finrank_SpecMap_algebraMap`
  gives `Module.rankAtStalk A y`). Here that is the degree `d` of the finite
  locally free sheaf `f_* 𝒪_X` (Stacks Definition 02KA). If `Y` is empty,
  the condition holds vacuously, and so does the conclusion, since `X` is
  then empty too.
- `M : Y.left.Modules` is a sheaf of `𝒪_Y`-modules, and `M.IsQuasicoherent`
  is Mathlib's `SheafOfModules.IsQuasicoherent`. `M` is otherwise arbitrary:
  it need not be a line bundle, coherent or locally free.
- `(Scheme.Modules.pullback f.left).obj M` is Mathlib's actual module
  pullback `f^* M` on `X`.
- `DerivedSections.relativeCohomology Y.hom n` is the Library's cohomology
  functor `Hⁿ(Y, -) : Y.Modules ⥤ ModuleCat K`. It is the `n`-th right
  derived functor of global sections, regarded as a `K`-module through
  `Y.hom`. The same holds for `X.hom` on `X`. Every `n : ℕ` is allowed,
  including `n = 0`.
- `Retract A B` is Mathlib's `CategoryTheory.Retract` in `ModuleCat K`: a
  pair of `K`-linear maps `i : A ⟶ B` and `r : B ⟶ A` with `i ≫ r = 𝟙 A`.
  The statement asserts only that such a pair exists (`Nonempty`).

The statement does not claim that `i` is the canonical pullback map
`DerivedSections.relativeCohomologyPullback`. It also claims nothing about
a trace map on sheaves, and nothing about the cohomology being finite
dimensional or vanishing.

## Comparison with the sources

**Mumford–Fogarty–Kirwan.** The statement is the splitting step in the
field-case proof of *Geometric Invariant Theory*, 3rd edition (1994),
Proposition 6.13 (i). That is printed p. 124, one-based PDF p. 137 of the
registered Chapter 6 file, source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
There `A` is an abelian variety of dimension `g` over a field and `ψ_k` is
multiplication by `k`, which is finite flat of degree `k^{2g}`. The text
first identifies `Hⁱ(A, ψ_{k*} ψ_k^* L) ≅ Hⁱ(A, ψ_k^* L)`. It then argues
that when the characteristic does not divide `k`, `L` is a direct summand
of `ψ_{k*} ψ_k^* L`, with section given by the unit map `i` and retraction
given by `k^{-2g}` times the trace. Applying `Hⁱ` gives the retraction of
cohomology.

The Lean statement abstracts this argument. `ψ_k` becomes any finite flat,
locally finitely presented `f` over a field. `k^{2g}` becomes its constant
rank `d`. "Characteristic does not divide `k`" becomes `(d : K) ≠ 0`. For
`d = k^{2g}` the source's condition implies `(k^{2g} : K) ≠ 0` for every
`g`, and the two conditions are equivalent when `g > 0`. When `g = 0` the
degree is `1` and the rank condition holds automatically, even if the
characteristic divides `k`. The Lean statement keeps this case and adds no
positive-dimension hypothesis. The line bundle `L` becomes any
quasi-coherent `M`. The source's argument uses nothing special to abelian
varieties or line bundles, so it proves this generalization unchanged; see
the proof obligations below. Two things are weaker than the source: the
Lean statement records only the retraction of cohomology, not the
sheaf-level direct-summand decomposition, and it does not identify the
section with a canonical map.

The consumer is task `6a5c4a64-6809-4f94-b35e-87cbc8a8b432`. It applies the
statement to `f = (GroupScheme.multiplication B.toGrp (k : ℤ)).hom.hom`, a
morphism in `Over (Spec K)` from the abelian variety to itself. The rank
`k^{2g}` comes from the published `polarizedFiniteFlatRank`. Finiteness
comes from `multiplication_isFinite_of_ne_zero`, and flatness and finite
presentation come from étaleness (`multiplication_etale_of_field`).

**Stacks Project** (commit `a04446e5`).

- Section 29.49, tag 02K9, `morphisms.tex` line 12351 in registered folder
  `stacks-affine-morphisms-relative-vanishing-a04446e5`.
  Definition 02KA: `f` is finite locally free of degree `d` if `f` is
  affine and `f_* 𝒪_X` is finite locally free of rank `d`. Lemma 02KB:
  finite locally free is equivalent to finite, flat and locally of finite
  presentation. So the three Lean hypotheses are the source's finite
  locally free condition. Finite presentation is a convenient hypothesis
  rather than an essential one. A finite flat module over a local ring is
  free, so Algebra Lemma 10.78.2 (tag 00NX, condition (8)) shows that a
  finite flat module with locally constant rank is already finite
  projective. The consumer can supply finite presentation because étale
  morphisms are locally of finite presentation.
- Lemma 01SB (`lemma-affine-equivalence-modules`, `morphisms.tex`
  line 1896): for affine `f`, `f_*` is an equivalence from quasi-coherent
  `𝒪_X`-modules onto quasi-coherent `f_* 𝒪_X`-modules. Locally, on
  `Spec A → Spec R` with `M = Ñ`, this gives `f_* f^* M = (A ⊗_R N)~`.
- Projection formula, Cohomology Lemma 20.54.2 (tag 01E8, `cohomology.tex`
  line 13843 in registered folder
  `stacks-flasque-affine-vanishing-kunneth-a04446e5`):
  `E ⊗ R^q f_* F ≅ R^q f_*(f^* E ⊗ F)` when `E` is finite locally free on
  the target. With `E = M`, `F = 𝒪_X` and `q = 0` this gives
  `M ⊗ f_* 𝒪_X ≅ f_* f^* M`, which covers MFK's line bundle `L`. For an
  arbitrary quasi-coherent `M` the lemma's hypothesis fails. The proof
  instead uses the affine-local description `(A ⊗_R N)~` from 01SB, which
  holds for every quasi-coherent `M` because `f` is affine.
- Coherent Lemma 30.2.4 (tag 089W, `coherent.tex` line 202 in the same
  folder): for affine `f` and quasi-coherent `F`,
  `Hⁱ(X, F) = Hⁱ(S, f_* F)`. This is MFK's identification
  `Hⁱ(A, ψ_{k*} ψ_k^* L) ≅ Hⁱ(A, ψ_k^* L)`.

## Expected proof obligations

1. **Affine pushforward.** `IsFinite f.left` gives `IsAffineHom f.left`.
   Show that `f^* M` is quasi-coherent. The Library proves this for
   morphisms of spectra (`Langlands.Scheme.Modules.isQuasicoherent_affinePullback`,
   `Modules/AffinePullbackQuasicoherent`); the general case is local on `X`.
   Then `DerivedSections.affinePushforwardCohomologyIso f.left Y.hom (f^* M) n`
   (`Modules/AffinePushforwardEulerCharacteristicProof`), rewritten with
   `Over.w f : f.left ≫ Y.hom = X.hom`, identifies
   `Hⁿ(X, f^* M) ≅ Hⁿ(Y, f_* f^* M)` as `K`-modules.
2. **Section.** Let `η : M ⟶ f_* f^* M` be the unit of
   `Scheme.Modules.pullbackPushforwardAdjunction f.left`.
3. **Trace.** Construct a morphism of `𝒪_Y`-modules `t : f_* f^* M ⟶ M`.
   On an affine open `V = Spec R` with `f⁻¹ V = Spec A` it is
   `Tr_{A/R} ⊗ id : A ⊗_R M(V) → M(V)`, and the local pieces must glue
   along restrictions. Mathlib's `LinearMap.trace` (hence `Algebra.trace`)
   is defined as `0` on modules without a finite basis
   (`Mathlib/LinearAlgebra/Trace.lean`). So the trace must be defined on
   opens where `A` is free, which exist by 02KB, and glued using
   `Algebra.trace_localization`
   (`Mathlib/RingTheory/Localization/NormTrace.lean`). `finiteFlatPushforwardStructure`
   (`Modules/FiniteFlatPushforwardStructureProof`) supplies the
   quasi-coherence of `f_* 𝒪_X` and finite flatness of its affine sections.
   The Library's `localSectionTrace` (`AlgebraicGeometry/LocalSectionTrace`)
   takes traces of sheaf endomorphisms on a finite free chart, independent
   of the chart (`localSectionTrace_trivialization_independent`). For a
   global endomorphism the traces agree on common smaller chart opens
   (`localSectionTrace_overlap` in `AlgebraicGeometry/LocalTraceTransport`).
   Applied to multiplication by sections of `f_* 𝒪_X`, these tools may help
   build the trace `f_* 𝒪_X ⟶ 𝒪_Y` on free charts.
4. **Composite is multiplication by `d`.** Show `η ≫ t = d • 𝟙_M`. Locally,
   `m ↦ 1 ⊗ m ↦ Tr_{A/R}(1) m`, and `Tr_{A/R}(1) = d` on opens where `A` is
   free of rank `d` (`Algebra.trace_algebraMap`). The rank of `A` there is
   `d` by the `finrank` hypothesis
   (`Scheme.Hom.finrank_SpecMap_algebraMap`,
   `Scheme.Hom.isLocallyConstant_finrank`).
5. **Retraction in cohomology.** `Hⁿ(Y, -)` is an additive functor to
   `ModuleCat K` whose values are `K`-modules. Applying it to `η` and `t`
   gives `K`-linear maps whose composite is `d • 𝟙`, which is invertible
   because `(d : K) ≠ 0`. Let `e : Hⁿ(X, f^* M) ≅ Hⁿ(Y, f_* f^* M)` be the
   iso of step 1. Take `i = Hⁿ(η) ≫ e.inv` and
   `r = e.hom ≫ (d : K)⁻¹ • Hⁿ(t)`. Then `i ≫ r = 𝟙`. Alternatively,
   rescale `t` by `d⁻¹` on the sheaf level, since `d` is invertible in
   every `𝒪_Y(V)` through `K → 𝒪_Y(V)`.
