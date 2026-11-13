# Abstract inputs for the integral identification of Renard VII.3.4

Author: Worker 48. Module `Langlands.Representation.Intertwining.PQIntegralIdentificationAbstract`.

This helper module holds four independent groups of abstract facts used by the proof of
Renard VII.3.4 in `Langlands.Representation.Intertwining.PQIntegralIntertwiningOperatorProof`.
None of them mentions group schemes, induced representations or the double coset `P Q`. They are
internal lemmas. The literature does not state them separately; the provenance of each is given
below. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, VII.3.4, printed pp.235–236 / PDF pp.241–242 (literature ID
`renard-2026-representations-groupes-reductifs-padiques`).

## 1. Right invariance of integrals over a complement (`Langlands.QuotientIntegration`)

Setting: a locally compact topological group `Γ`, subgroups `H, K`, and a homeomorphism
`m : H × K ≃ₜ Γ` with `m (h, k) = h k`. `K` carries a right-invariant regular Haar measure `μK`.
The left quotient `H \ Γ` carries a regular measure `ν` that every right translation preserves.

- `exists_ne_zero_map_factorQuotientHomeomorph_symm`: if `ν ≠ 0`, transporting `ν` to `K` along
  the inverse of the Library chart `factorQuotientHomeomorph` (`K ≃ₜ H \ Γ`, `k ↦ H k`) gives
  `a • μK` with `a ≠ 0`. The Library lemma `exists_smul_map_factorQuotientHomeomorph_symm` gives
  the multiple `a`. If `a = 0`, mapping back would make `ν` zero.
- `integral_mul_right_of_leftInvariant`: if `ν ≠ 0` and `φ : Γ → ℂ` is left `H`-invariant, then
  for every `g ∈ Γ`, `k ↦ φ(k g)` is `μK`-integrable exactly when `k ↦ φ(k)` is, and
  `∫_K φ(k g) dμK = ∫_K φ(k) dμK`. The function `φ` descends to `ψ` on `H \ Γ`. Both integrals are
  `a⁻¹` times integrals of `ψ` against `ν`, and `ν` is right invariant.

This is the step "l'égalité entre les deux intégrales provient de la décomposition
`U = (U ∩ N)(U ∩ N̄)`" of Renard's proof, used here for right invariance under `U`.

## 2. Integrals read against linear forms (`Langlands.DualIntegral`)

The representation spaces are plain complex vector spaces without topology, so the integral of a
vector-valued function is defined by testing against all linear forms.

- `HasDualIntegral μ F w` for `F : X → W` and `w ∈ W`: for every linear form `ℓ`, `ℓ ∘ F` is
  `μ`-integrable and `ℓ(w) = ∫ ℓ(F x) dμ`.
- `HasDualIntegral.unique`: the value is unique, since linear forms separate points.
- `dualIntegral μ F`: the value if one exists, and `0` otherwise (chosen with `Classical.choice`).
  `HasDualIntegral.dualIntegral_eq` identifies it with any value, and
  `hasDualIntegral_dualIntegral` says the chosen value is one when a value exists.
- Closure properties: `hasDualIntegral_zero`, `HasDualIntegral.add`, `.smul`, `.map` (composition
  with a linear map), `.congr` (pointwise equal functions), `.sum` (finite sums).
- `HasDualIntegral.comp_measurableEmbedding`: if `e : X → Y` is a measurable embedding with
  `μ.map e = a • ν`, a value `w` of `F` against `ν` gives the value `a • w` of `F ∘ e` against `μ`.
- `hasDualIntegral_indicator`: `w` times the indicator of a measurable set `S` with `μ S < ∞` has
  value `μ.real S • w`.
- `exists_hasDualIntegral_of_isLocallyConstant`: a locally constant `F` vanishing off a compact
  set has a value, for a measure that is finite on compacts. On the compact set `F` takes finitely
  many values, so `F` is a finite sum of indicators of open fibres of finite measure.

## 3. Descent of linear maps (`Langlands.LinearDescent`)

- `descend φ hφ T h`: for a surjective linear map `φ : A → B` and a linear map `T : A → C` with
  `ker φ ≤ ker T`, the induced linear map `B → C`. It is `(ker φ).liftQ T h` composed with the
  inverse of `φ.quotKerEquivOfSurjective hφ`.
- `descend_apply`: `descend φ hφ T h (φ a) = T a`.
- `liftQ_mk_smul`: `S.liftQ L h (mk (c • a)) = c • L a`.

These are wrappers. They keep the concrete proof from rewriting through very large types.

## 4. Rigidity of natural surjections (`Langlands.SmoothRep`)

Setting: a topological group `M`, a function `Q` from smooth representations of `M` to
representations of `M`, linear maps `Qmap f : Q W → Q W'` for morphisms `f : W ⟶ W'`, and
equivariant linear equivalences `e W : Q W ≃ W` that are natural:
`e W' (Qmap f x) = f (e W x)`.

- `kerSmooth W T`, `kerSmoothι W T`: the kernel of an equivariant endomorphism `T` of a smooth
  representation, as a smooth representation, and its inclusion.
- `injective_of_natural_surjective`: let `I W : Q W → W` be equivariant, natural and surjective
  for every `W`. Then every `I W` is injective. Proof: `T_W = I_W ∘ e_W⁻¹` is a natural surjective
  equivariant endomorphism. On the kernel `K` of `T_W`, naturality along `K ↪ W` gives `T_K = 0`,
  while `T_K` is surjective, so `K = 0`.
- `character_eq_one_of_surjective`: let `I W : Q W → W` be surjective linear maps with
  `I_W(m x) = χ(m) W(m)(I_W x)` for one function `χ : M → ℂ` not depending on `W`. Then `χ = 1`.
  For the trivial representation on `ULift ℂ`, take `x` with `I x = 1`. Equivariance of `e`
  gives `m x = x`, so `1 = χ(m) · 1`.
- `exists_equiv_of_natural_surjective`: under the hypotheses of the two previous results
  (natural, surjective, twisted-equivariant `I`), every `I W` is an equivariant linear
  equivalence. Formally, there is `E : (Q W).ρ.Equiv W.representation` with `E x = I W x`.

Renard's text says that the natural isomorphism `F^{<1̄}/F^{≤1̄}(E) ≃ E` "est obtenu par passage
au quotient" from the integral, and calls this a special case of formula (VI.5.1.12). The present
route avoids that formula. The concrete proof applies `exists_equiv_of_natural_surjective` with
`e` the natural identification proved in the Library (`pqSupportGraded`).
