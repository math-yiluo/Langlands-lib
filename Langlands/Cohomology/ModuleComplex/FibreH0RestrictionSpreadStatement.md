# Spreading out a degree-zero restriction isomorphism from a fibre

The Prop-valued declaration
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement.{u}` is
the commutative-algebra core of the proofs of Stacks Lemmas 0BF1 and 0BF2. It is a
statement only; this file proves nothing. Worker 950 prepared the draft,
Worker 1119 requested its arbitrary-field interface, and Worker 1154 checked
the source correspondence and completed this documentation. It is a prerequisite of the proof task `e969f1c2-7aa6-4731-abaa-2f7455f32265`
(`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`).

## Complete statement

Write `K ⊗ T = (baseChange φ).obj K` for a ring map `φ : R →+* T`, where
`Langlands.Cohomology.ModuleComplex.baseChange` is the published ordinary
termwise extension of scalars, `Hⁱ(·) = HomologicalComplex.homology · i`, and
`Hⁱ(ψ ⊗ T) = HomologicalComplex.homologyMap ((baseChange φ).map ψ) i`, a
morphism in `ModuleCat T` applied to elements through `.hom`.

For every `R : Type u` with `[CommRing R]`, cochain complexes
`K K₁ K₂ : CochainComplex (ModuleCat.{u} R) ℤ` with `IsStrictlyPerfect K`,
`IsStrictlyPerfect K₁` and `IsStrictlyPerfect K₂` (bounded, with finite projective
terms), chain maps `ψ₁ : K ⟶ K₁` and `ψ₂ : K ⟶ K₂`, a field `k : Type u` and a
ring map `φ₀ : R →+* k`, assume:

1. `IsZero (Hⁱ(K ⊗ k))`, `IsZero (Hⁱ(K₁ ⊗ k))` and `IsZero (Hⁱ(K₂ ⊗ k))` for every
   integer `i < 0`;
2. for every `T : Type u` with `[CommRing T]` and every `φ : R →+* T`, there are
   `T`-linear equivalences `H⁰(K₁ ⊗ T) ≃ₗ[T] T` and `H⁰(K₂ ⊗ T) ≃ₗ[T] T`
   (asserted by `Nonempty`, with no compatibility between different `T`);
3. `H⁰(ψ₁ ⊗ k)` is bijective;
4. every `c ∈ H¹(K ⊗ k)` with `H¹(ψ₁ ⊗ k) c = 0` and `H¹(ψ₂ ⊗ k) c = 0` is zero.

Then there is `r : R` with `φ₀ r ≠ 0` such that for every `T : Type u` with
`[CommRing T]` and every `φ : R →+* T` with `IsUnit (φ r)`, the map
`H⁰(ψ₁ ⊗ T)` is bijective.

The field `k` is arbitrary: it need not be the residue field of the prime
`ker φ₀`. All carriers lie in an arbitrary universe `u`, and `R` is not assumed
noetherian, local or reduced.

## Source and specialization

Registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, Stacks
Project git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, file
`more-morphisms.tex`: the proof of [Lemma 0BF1](https://stacks.math.columbia.edu/tag/0BF1),
`lemma-H1-O-picard-flat-proper`, lines 9453–9516, and its variant for several restrictions, the proof
of [Lemma 0BF2](https://stacks.math.columbia.edu/tag/0BF2),
`lemma-H1-O-multiple-picard-flat-proper`, lines 9543–9619.
After representing `E = Rf_*ℒ` and `Eᵢ = Rfᵢ_*𝒪` near `s` by finite free
complexes
`𝒪_S → 𝒪_S^{h₁} → …` and `𝒪_S → 𝒪_S^{hᵢ,₁} → …` (More on Algebra, Lemma
`lemma-lift-perfect-from-residue-field`, [tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD), `more-algebra.tex` lines
19593–19629 of the registered source `stacks-perfect-complexes-a04446e5`), and the
restriction maps by chain maps with components `aᵢ, bᵢ`, the proof argues:

- `aᵢ ⊗ κ(s)` is an isomorphism, hence `aᵢ` is an isomorphism after shrinking;
- injectivity of `H¹(X_s, 𝒪) → ⊕ H¹(X_{i,s}, 𝒪)` gives a nonzero `h₁ × h₁`
  minor of `⊕ bᵢ` at `s`, hence `(b₁, …, bₙ)` is injective after shrinking;
- since `ℒᵢ = 𝒪_{Xᵢ}`, the differentials `dᵢ` vanish; so `d = 0` from
  `(b₁, …, bₙ) ∘ d = (⊕ dᵢ) ∘ (a₁, …, aₙ)`, and the trivializing section of
  `ℒ_s` lifts to a section of `ℒ` over `X`.

Specialization. The statement takes `n = 2` and the algebraic content only:

- `K`, `K₁`, `K₂` stand for strictly perfect models of `E`, `E₁`, `E₂` over an
  affine neighbourhood `Spec R` of `s`, and `ψ₁`, `ψ₂` for chain maps representing
  the restrictions; `φ₀ : R → k` stands for `R → κ(s)`, and inverting `r` is the
  shrinking of `S`. The formal statement allows any field-valued point
  `φ₀ : R → k`, including one whose residue field is a proper subfield of `k`.
- Hypothesis 1 records that these are derived global sections, with no
  cohomology in negative degrees. Hypothesis 2 is the universal degree-zero
  comparison `H⁰(X_{i,T}, 𝒪) = T` behind "`dᵢ = 0` since `ℒᵢ = 𝒪`" (in the
  source, the hypotheses of Lemma 0BDP include `𝒪_T → p_*𝒪_{X_T}` an isomorphism
  for every base change). Hypothesis 3 retains the source condition
  that `a₁ ⊗ κ(s)` is an isomorphism, which follows from `s ∈ Z`. The source
  has this condition for every restriction; only the first is needed for the
  degree-zero conclusion stated here. Hypothesis 4 is the injectivity of
  `H¹(X_s, 𝒪) → H¹(X_{1,s}, 𝒪) ⊕ H¹(X_{2,s}, 𝒪)`.
- The conclusion is the source's degree-zero consequence: after shrinking, the
  degree-zero cohomology of `E` maps isomorphically to that of `E₁` after any
  further base change. In the geometric application this is the bijectivity of
  `Γ(X_U, ℒ) → Γ(X_{1,U}, ℒ|) = Γ(U, 𝒪)`, which lets the trivializing section
  of `ℒ` on the fibre lift, after using the separate geometric comparisons.

The universal isomorphisms in hypothesis 2 record less data than the source's
canonical maps: the proposition asks only for their existence. They still
supply the rank-one condition needed in the local algebra argument. For
example, in a minimal model over the local ring `A = Rₚ` the negative terms
vanish and the degree-zero term of each target has rank one. Its degree-zero
homology is therefore the kernel of `dᵢ : A → Mᵢ¹`. Hypothesis 2 applied to
`R → A` makes this kernel free of rank one. If its generator is `t ∈ A`,
the inclusion of the kernel shows that multiplication by `t` on `A` is
injective. Since `Mᵢ¹` is free and `t • dᵢ(1) = 0`, it follows that `dᵢ = 0`.
This explains the abstract algebraic replacement for the source's use of the
trivial bundles `ℒᵢ`, without adding a choice of trivialization or a
minimal model to the hypotheses. This paragraph explains the design; it is
not a Lean proof.

The scope is also weaker than a geometric triviality theorem: it keeps two
restrictions, asks for an isomorphism only for the first in degree zero, and
uses the second only for joint detection in degree one. No conclusion about
the locally closed Picard loci or their scheme theoretic intersection is
included.

The minimal-model step, the identification of residue cohomology of the models
with `F ⊗ k`, and the reduction from an arbitrary field `k` to the residue field
of `ker φ₀` (a field extension is faithfully flat) are obligations of a proof of
this proposition. The formal statement is an internal design derived from the
source, not a transcription.

## Scope

This is a statement only. It contains no geometry: the identification of the
complexes with derived sections, the restriction maps and their compatibility
with base change are the separate statement
`Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement`, proposed
alongside it. The equivalences between ordinary scalar extension of the
strictly perfect representatives and the source's derived operations belong
to those comparison and proof obligations. It asserts nothing about `ψ₂` in degree zero, nor about degrees
other than zero after base change.
