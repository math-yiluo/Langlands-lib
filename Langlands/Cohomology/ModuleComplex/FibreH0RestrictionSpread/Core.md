# Spreading degree-zero bijectivity for finite free complexes

Author: Worker 1119.

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Core`, namespace
`Langlands.Cohomology.ModuleComplex.FibreH0Spread`. It is a helper for the proof of
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (see `Main.md`). It
imports the Library modules `Langlands.Cohomology.PerfectModuleComplexBaseChange` and
`Langlands.Cohomology.ExtendScalarsLocalizationDescent`, and the helpers `Split` and
`Homology`. No `sorry` and no new axioms.

Notation: `baseChange β` is the Library's termwise scalar extension of cochain complexes along a
ring map `β` (`Langlands.Cohomology.ModuleComplex.baseChange`). `IsFiniteFree P` is the
Library's predicate: bounded, with finite free terms.

## Auxiliary lemmas

- `free_extendScalars β M`: if `M` is free over `A`, then `(ModuleCat.extendScalars β).obj M`
  is free over `T`. With `β.toAlgebra` the object is `T ⊗[A] M`.
- `nonempty_extendScalars_equiv β e`: from `e : M ≃ₗ[A] (Fin n → A)`, some
  `(extendScalars β).obj M ≃ₗ[T] (Fin n → T)`. Uses the Library lemma
  `nonempty_extendScalars_pi_equiv`.
- `nonempty_extendScalars_equiv_self β e`: the case `n = 1`, composed with
  `Fin 1 → T ≃ₗ T`.
- `baseChange_d_zero_one β hQ hz e hH`: let `Q` be finite free with `IsZero (Q.X (-1))` and
  `e : Q.X 0 ≃ₗ[A] (Fin 1 → A)`, and let `H⁰` of `(baseChange β).obj Q` be free of rank one
  over `T`. Then the differential from degree `0` to `1` of `(baseChange β).obj Q` vanishes.
  This is `d_zero_one_eq_zero` (from `Homology`) applied to the scalar extension.
- `baseChange_d_neg_one β hz`: if `IsZero (Q.X (-1))`, the differential into degree `0` of
  `(baseChange β).obj Q` vanishes.

## Main result: `exists_bijective_of_finiteFree`

Hypotheses: `φ : A →+* k`, `k` a field. `P`, `P₁`, `P₂` finite free complexes over `A`, and
chain maps `χ₁ : P ⟶ P₁`, `χ₂ : P ⟶ P₂`. Each complex has zero term in degree `-1`, and
`e`, `e₁`, `e₂` identify its degree-zero term with `Fin 1 → A`. The fibre `(baseChange φ).obj P`
has all differentials zero (`hd`). For every `T` and `β : A →+* T`, the degree-zero homology of
`(baseChange β).obj P₁` and of `(baseChange β).obj P₂` is linearly equivalent to `T` (`hH₁`,
`hH₂`). `H⁰(χ₁ ⊗ k)` is bijective (`h0`). `H¹(χ₁ ⊗ k)` and `H¹(χ₂ ⊗ k)` are jointly injective
(`h1`).

Conclusion: there is `a : A` with `φ a ≠ 0` such that for every `T` and `β : A →+* T` with
`β a` a unit, `H⁰(χ₁ ⊗ T)` is bijective.

Proof.

1. Degree zero. Since all differentials of `P ⊗ k` vanish, `h0` makes `χ₁⁰ ⊗ k` injective
   (`jointly_injective_f_of_homologyMap` with `f₁ = f₂ = χ₁`). `exists_split_of_extendScalars`
   gives `a₀` with `φ a₀ ≠ 0` and `g₁`, `g₂` with `χ₁⁰ ≫ (g₁ + g₂) = a₀ • 𝟙`.
2. Degree one. `h1` makes `χ₁¹ ⊗ k`, `χ₂¹ ⊗ k` jointly injective (same lemma), and
   `exists_split_of_extendScalars` gives `a₁` with `φ a₁ ≠ 0` and `f₁`, `f₂` with
   `χ₁¹ ≫ f₁ + χ₂¹ ≫ f₂ = a₁ • 𝟙`.
3. Take `a = a₀ * a₁`, so `φ a ≠ 0`. Fix `β` with `β a` a unit. Then `β a₀` and `β a₁` are
   units.
4. By `baseChange_d_zero_one` with `hH₁ T β` and `hH₂ T β`, the degree-zero differentials of
   `P₁ ⊗ T` and `P₂ ⊗ T` vanish.
5. The degree-zero differential of `P ⊗ T` vanishes. From step 2 and the chain map squares,
   `d⁰_P ≫ (a₁ • 𝟙) = (χ₁⁰ ≫ d⁰_{P₁}) ≫ f₁ + (χ₂⁰ ≫ d⁰_{P₂}) ≫ f₂`. Apply
   `ModuleCat.extendScalars β` (additive, and `extendScalars_map_smul` turns `a₁ •` into
   `β a₁ •`). By step 4 the right side is zero, so `β a₁ • (d⁰_P ⊗ T) = 0`. Since `β a₁` is a
   unit, `d⁰_P ⊗ T = 0`.
6. The differentials into degree `0` vanish (`baseChange_d_neg_one`). By
   `bijective_homologyMap_iff`, `H⁰(χ₁ ⊗ T)` is bijective iff `χ₁⁰ ⊗ T` is.
7. Applying `extendScalars β` to step 1 gives `(χ₁⁰ ⊗ T) ≫ ((g₁ + g₂) ⊗ T) = β a₀ • 𝟙`. Both
   terms are free of rank one over `T` (`nonempty_extendScalars_equiv_self`).
   `bijective_of_comp_eq_smul` concludes, since `β a₀` is a unit.

## Provenance

Internal helper. It is the local algebraic core of the proof of Stacks tag 0BF2
(`more-morphisms.tex`, lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The source argues with a minimal complex over the
local ring at the point, notes that the degree-one components are split injective, and deduces
that the source degree-zero differential vanishes. Here the splitting is explicit up to the
scalar `a`. So the conclusion holds after every ring map inverting `a`, not only at the local
ring.
