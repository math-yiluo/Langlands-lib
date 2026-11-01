# Spreading out a degree-zero restriction isomorphism from a fibre

Authors: Worker 1119 wrote this proof and its helper modules. The row-minor lemma in `Split` is
adapted from Worker 606 (see `Split.md`). Worker 950 designed the published statement and
proofread this note.

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Main`, namespace
`Langlands.Cohomology.ModuleComplex.FibreH0Spread`. It proves
`fibreH0RestrictionSpread : FibreH0RestrictionSpreadStatement.{u}`, the published statement
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (module of the same
name, imported unchanged). The proof is unconditional: it uses the published proofs
`primeMinimalPerfect` and `primeFreeHomotopyDescent` through `Model`, and assumes no unproved
Library proposition. No `sorry` and no new axioms.

Notation: `K ⊗_γ T` is `(baseChange γ).obj K`, the Library's termwise scalar extension along
`γ : R →+* T`. `Hⁱ` is `HomologicalComplex.homology` in degree `i`.

## Auxiliary lemmas

- `exists_hasModel_rank hK p`: `exists_hasModel` with the rank function named `n` and
  `n i = finrank_{κ(p)} Hⁱ(K ⊗ κ(p))` recorded as an equation.
- `eq_finrank_of_nonempty_equiv`: over a field `F`, `M ≃ₗ[F] (Fin n → F)` gives
  `n = finrank F M`.
- `baseChange_comp_d_eq_zero β ι hd`: if all differentials of `Q ⊗_β B` vanish, then all
  differentials of `Q ⊗_{ι ∘ β} C` vanish. The functor `baseChange ι` sends zero maps to zero
  maps, and `baseChangeCompIso β ι` identifies `Q ⊗_{ι ∘ β} C` with `(Q ⊗_β B) ⊗_ι C`.
- `d_eq_zero_of_finrank e hn β γ hγ hrank`: let `P` be a model of `K` along `α` (homotopy
  equivalence `e`, ranks `n`), let `β : A →+* F` be a map to a field with `β ∘ α = γ`, and
  suppose `n i = finrank_F Hⁱ(K ⊗_γ F)` for all `i`. Then every differential of `P ⊗_β F`
  vanishes. Proof: the term `(P ⊗_β F)^i` has dimension `n i`
  (`nonempty_extendScalars_equiv`). Its homology has dimension `n i`
  (`nonempty_homology_equiv_of_model` and `hrank`). So `d_eq_zero_of_finrank_homology` gives
  `d^{i, i+1} = 0`. The other differentials vanish by the complex shape.
- `nonempty_homology_equiv_fin e hn β γ hγ hd i`: if all differentials of `P ⊗_β T` vanish,
  then `Hⁱ(K ⊗_γ T) ≃ₗ[T] (Fin (n i) → T)`. It composes `nonempty_homology_equiv_of_model`,
  the inverse of `termIsoHomology`, and `nonempty_extendScalars_equiv`.
- `fibre_data e hn ρ γ hγ hrank ι φ₀ hφ`: let `ρ : A →+* F` with `ρ ∘ α = γ`, `ι : F →+* k`
  with `ι ∘ ρ ∘ α = φ₀`, and suppose the ranks `n` are the homology dimensions over `F`. Then all
  differentials of `P ⊗_{ι ∘ ρ} k` vanish, and `n i = finrank_k Hⁱ(K ⊗_{φ₀} k)` for all `i`.
  The first part combines the two previous lemmas. The second uses
  `nonempty_homology_equiv_fin` over `k` and `eq_finrank_of_nonempty_equiv`.
- `isZero_X_of_isZero_homology hn i hrank hz`: if `n i = finrank_k M` and `M` is zero, then
  `n i = 0`, and the term `P.X i ≃ₗ[A] (Fin 0 → A)` is zero.
- `nonempty_X_equiv_of_homology hn i hrank hM`: if `n i = finrank_k M` and `M ≃ₗ[k] k`, then
  `n i = 1` and `P.X i ≃ₗ[A] (Fin 1 → A)`.

## Main theorem: `fibreH0RestrictionSpread`

Take `R`, strictly perfect `K`, `K₁`, `K₂`, chain maps `ψ₁ : K ⟶ K₁`, `ψ₂ : K ⟶ K₂`, a field
`k` with `φ₀ : R →+* k`, and the hypotheses of the statement: negative fibre homology vanishes
(`hneg`, `hneg₁`, `hneg₂`), universal rank-one `H⁰` of `K₁`, `K₂` (`hH₁`, `hH₂`), `H⁰(ψ₁ ⊗ k)`
bijective (`h0`), and `H¹(ψ₁ ⊗ k)`, `H¹(ψ₂ ⊗ k)` jointly injective (`h1`).

1. Let `p = ker φ₀`, a prime ideal. Then `x ∉ p` iff `φ₀ x ≠ 0`.
2. `exists_hasModel_rank` for `K`, `K₁`, `K₂` gives `r₀`, `r₁`, `r₂ ∉ p` and models with
   ranks `n`, `n₁`, `n₂` equal to the homology dimensions over `κ(p)`. Let
   `r = r₀ * r₁ * r₂`, so `φ₀ r ≠ 0`. `HasModel.of_dvd` moves all three models to
   `A = Localization.Away r`, with `α = algebraMap R A`: finite free complexes `P`, `P₁`, `P₂`
   over `A` with homotopy equivalences `e`, `e₁`, `e₂` and term ranks `n`, `n₁`, `n₂`.
3. The image of `r` in `κ(p)` is nonzero, hence a unit
   (`Ideal.algebraMap_residueField_eq_zero`). This gives `ρ = IsLocalization.Away.lift r :
   A →+* κ(p)` with `ρ ∘ α = algebraMap R κ(p)`. Since `p = ker φ₀` and `φ₀` sends `R \ p` to
   units, `ι = Ideal.ResidueField.lift p φ₀ : κ(p) →+* k` exists, with
   `ι ∘ algebraMap R κ(p) = φ₀` (`Ideal.ResidueField.lift_algebraMap`). Let `φ = ι ∘ ρ`; then
   `φ ∘ α = φ₀`.
4. `fibre_data` for the three models: all differentials of `P ⊗_φ k` vanish (`hd`), and
   `n`, `n₁`, `n₂` are the homology dimensions over `k`.
5. Term shapes. By `hneg` at `-1` and `isZero_X_of_isZero_homology`, the terms of `P`, `P₁`,
   `P₂` in degree `-1` are zero. By `hH₁ k φ₀`, `hH₂ k φ₀` and `nonempty_X_equiv_of_homology`,
   the degree-zero terms of `P₁`, `P₂` are free of rank one. `H⁰(ψ₁ ⊗ k)` is bijective, so
   `H⁰(K ⊗ k) ≃ₗ[k] H⁰(K₁ ⊗ k) ≃ₗ[k] k` (`LinearEquiv.ofBijective` with `hH₁ k φ₀`). Hence the
   degree-zero term of `P` is free of rank one too.
6. Universal `H⁰` of `P₁`, `P₂`: for `β : A →+* T`, `H⁰(P₁ ⊗_β T) ≃ H⁰(K₁ ⊗_{β ∘ α} T) ≃ T`
   (`nonempty_homology_equiv_of_model`, `hH₁ T (β.comp α)`), and likewise for `P₂`.
7. Apply `exists_bijective_of_finiteFree` (from `Core`) to `φ`, the three models, and the
   transported maps `χⱼ = e.hom ≫ (baseChange α).map ψⱼ ≫ eⱼ.inv`. Its fibre hypotheses come
   from `h0` and `h1` by `bijective_homologyMap_iff_of_model` and
   `jointly_injective_homologyMap_of_model` (with `φ ∘ α = φ₀`). It gives `a : A` with
   `φ a ≠ 0` such that `H⁰(χ₁ ⊗_β T)` is bijective whenever `β a` is a unit.
8. Clear denominators: `IsLocalization.Away.surj r a` gives `m` and `s : R` with
   `a * α r ^ m = α s`. The required element is `r * s`. Its image under `φ₀` is
   `φ₀ r * φ (a) * φ₀ r ^ m ≠ 0`.
9. Let `φT : R →+* T` with `φT (r * s)` a unit. Then `φT r` and `φT s` are units. Let
   `β = IsLocalization.Away.lift r : A →+* T`, so `β ∘ α = φT`. Then
   `β a * β (α r) ^ m = φT s` is a unit, so `β a` is a unit. Step 7 gives bijectivity of
   `H⁰(χ₁ ⊗_β T)`, and `bijective_homologyMap_iff_of_model` transfers it to `H⁰(ψ₁ ⊗_{φT} T)`.

## Provenance and relation to the source

This proves the published statement, whose Markdown records its derivation from Stacks tag
0BF2 (`more-morphisms.tex`, statement lines 9518–9541 and proof lines 9543–9619, registered
source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The route follows the source: minimal finite free
complexes near the point, vanishing of the target degree-zero differentials from universal
rank-one `H⁰`, splitting of the degree-one components, vanishing of the source degree-zero
differential, and the degree-zero component being an isomorphism on the fibre and hence after
shrinking (`Core`, steps 1 and 7). It differs in two ways. The fibre field `k` is reached
through the residue field `κ(p)` of `p = ker φ₀` by the map `ι`. Minimality is used over
`κ(p)` and pushed to `k`, so no faithful flatness argument is needed. Also, the splittings are
explicit up to a scalar, so the conclusion holds after every ring map inverting one element,
rather than only at the local ring.
