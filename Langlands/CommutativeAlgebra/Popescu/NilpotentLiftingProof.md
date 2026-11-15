# Proof: lifting smooth factorizations along a nilpotent ideal

`Langlands.CommutativeAlgebra.Popescu.NilpotentLifting.nilpotentLifting :
NilpotentLiftingStatement.{u}` proves the statement
`Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingStatement` (Stacks Project,
*Smoothing Ring Maps*, Proposition 5.3, Tag 07CM) for every universe `u`. It is
`nilpotentLifting_of` applied to
`Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract.standardSmoothRetract`, the
proof of `StandardSmoothRetractStatement` (Stacks 07CH). `nilpotentLifting_of` proves 07CM
under the hypothesis `StandardSmoothRetractStatement.{u}`. The proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Route

The proof follows Stacks 07CK (Lemma 5.1), 07CL (Lemma 5.2) and 07CM (Proposition 5.3),
with one change. Stacks first reduces to `I² = 0` by induction on the nilpotency order.
That reduction needs `Λ / I^k Λ` to have property PT over `R / I^k` at each stage, so the
induction runs through several rings. The Lean proof stays over `R`. It pushes an element
`h ∈ I^k B` into `I^(k+1) B'` one step at a time and stops when `I^N = 0`. As a result the
ideal `J` of Stacks 5.1 need not be finitely generated, and only single elements are
killed.

Throughout, `R → Λ` is flat, `I ⊆ R` is nilpotent, and `Λ / IΛ` has property PT over
`R / I` (`HasSmoothFactorizations`).

1. **Smooth lift of a standard smooth algebra** (`exists_smooth_lift_of_presentation`).
   Take a submersive presentation `P` of an `R / I`-algebra `S` with variables `ι` and
   relations `σ`. Lift the relations to `v_j ∈ R[ι]`. Then
   `B₀ = R[ι] / (v_j)` carries the pre-submersive presentation
   `Algebra.PreSubmersivePresentation.naive`, with Jacobian `d ∈ B₀`. Its composite with
   `PreSubmersivePresentation.localizationAway` has Jacobian `d · d`
   (`comp_jacobian_eq_jacobian_smul_jacobian`, `localizationAway_jacobian`), which is a unit
   in `B = B₀[1/d]`. So `B` is standard smooth, hence smooth, over `R`. Evaluation at
   `P.val` gives `B₀ → S` sending `d` to the Jacobian of `P`, which is a unit. It therefore
   extends to `π : B → S` (`IsLocalization.liftAlgHom`). `π` is surjective, and
   `ker π ⊆ I B` because `ker(R[ι] → (R / I)[ι]) = I R[ι]` (`MvPolynomial.ker_map`) and the
   reduced relations span the kernel of `P` (`span_range_relation_eq_ker`).

2. **Nakayama for a nilpotent ideal** (`surjective_of_surjective_mod`). If an `R`-algebra
   map `f : B → T` is surjective modulo `I T`, then `range f + I^n T = T` for every `n`, by
   induction on `n`. Taking `I^n = 0` shows that `f` is surjective.

3. **Covers (Stacks 07CK).**
   - `exists_smooth_cover`: if `A / IA` is standard smooth over `R / I`, then there is a
     smooth `R`-algebra `B` and a surjection `θ : B → A` with `ker θ ⊆ I B`. Apply step 1 to
     `A / IA` to get `π : B → A / IA`. Lift `π` along the nilpotent thickening
     `A → A / IA` by formal smoothness (`Algebra.FormallySmooth.liftOfSurjective`). The
     result `θ` is surjective by step 2, and `ker θ ⊆ ker π ⊆ I B`.
   - `nonempty_algEquiv_reduction`: let `B̄ = (C / IC)[t] / (ḡ_i)` with lifts
     `g_i ∈ C[t]`, and let `A' = C[t, δ] / (rel_i)` with `rel_i ≡ g_i` modulo `I`. Then
     `A' / IA' ≅ B̄[δ]` as `R / I`-algebras. The maps in both directions are built
     explicitly; `A'` enters only through a surjection `p` with `ker p = (rel_i)`.
   - `exists_cover_of_presentation`: this is the construction in the proof of Stacks 5.1.
     Lift the images of the `t_k` in `Λ / IΛ` to `λ_k ∈ Λ`. Write
     `ψ(g_i)(λ) = Σ_l ε_il μ_il` with `ε_il ∈ I` (`exists_sum_of_mem_map`). Set
     `A' = C[t, δ_il] / (g_i − Σ_l ε_il δ_il)`, with `γ : C → A'` the structure map and
     `δ : A' → Λ` given by `t_k ↦ λ_k`, `δ_il ↦ μ_il`. Then `δ ∘ γ = ψ`. `A' / IA' ≅ B̄[δ]`
     is standard smooth (`IsStandardSmooth.trans`, `of_algEquiv`), so `exists_smooth_cover`
     gives a smooth `B'` and `θ : B' ↠ A'` with `ker θ ⊆ I B'`.
   - `exists_cover`: for `C` finitely presented over `R` and `ψ : C → Λ`, property PT
     modulo `I` factors `C / IC → B₀ → Λ / IΛ` with `B₀` smooth over `R / I`. Here
     `C / IC` is finitely presented over `R / I` through
     `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. 07CH (the hypothesis `hS4`)
     replaces `B₀` by a standard smooth `B̄` with a retraction `B̄ → B₀`. `B̄` is finitely
     presented over `C / IC` (`of_restrict_scalars_finitePresentation`), which gives the
     presentation that `exists_cover_of_presentation` needs.

4. **One step (the computation in Stacks 07CL)** (`exists_step`). Let `B` be smooth over
   `R`, `φ : B → Λ`, `h ∈ I^k B` and `φ h = 0`. Then there are a smooth `B'`,
   `α : B → B'` and `β : B' → Λ` with `β ∘ α = φ` and `α h ∈ I^(k+1) B'`.
   Write `h = Σ ε_l s_l` with `ε_l ∈ I^k`. By the equational criterion for flatness
   (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`), `φ(s_l) = Σ_j a_lj y_j` with
   `Σ_l ε_l a_lj = 0`. Let `C = B[x] / (s_l − Σ_j a_lj x_j)`, mapping to `Λ` by `φ` and
   `x_j ↦ y_j`. Apply `exists_cover` to get `θ : B' ↠ A'`, `γ : C → A'` and
   `δ : A' → Λ`. Lift `B → C → A'` through `θ` to `α : B → B'` (formal smoothness of `B`;
   `ker θ` is nilpotent by `isNilpotent_of_le_map`), and set `β = δ ∘ θ`. With `y'_j`
   lifting the images of the `x_j`, `z_l = α(s_l) − Σ_j a_lj y'_j` lies in `ker θ ⊆ I B'`.
   So `α h = Σ_l ε_l z_l + Σ_j (Σ_l ε_l a_lj) y'_j = Σ_l ε_l z_l ∈ I^(k+1) B'`.

5. **Conclusion (Stacks 07CL and 07CM).**
   - `exists_kill_one`: induction on `k` with step 4, starting from `I^0 B = B`, gives a
     factorization `B → B' → Λ` of `φ` with `α h ∈ I^k B'` for every `k`. Taking `k = N`
     with `I^N = 0` gives `α h = 0`.
   - `exists_kill_family`: induction on the number `m` of elements `h_1, …, h_m` killed by
     `φ`. Kill `h_1, …, h_(m−1)` first, then the image of `h_m`.
   - `nilpotentLifting_of`: let `A` be finitely presented over `R` and `f : A → Λ`.
     `Algebra.FinitePresentation.out` gives a surjection `p : R[x_1, …, x_n] → A` whose
     kernel is generated by `h_1, …, h_m`. `R[x_1, …, x_n]` is smooth over `R`. Apply
     `exists_kill_family` to `f ∘ p` and the `h_i` to get `α : R[x] → B'` killing `ker p`.
     `α` descends to `A → B'` (`AlgHom.liftOfSurjective`), and `β` composed with it is `f`.

## Auxiliary declarations

All are in namespace `Langlands.CommutativeAlgebra.Popescu.NilpotentLifting`:
`aeval_map_mk`, `exists_smooth_lift_of_presentation`, `surjective_of_surjective_mod`,
`exists_sum_of_mem_map`, `exists_smooth_cover`, `nonempty_algEquiv_reduction`,
`exists_cover_of_presentation`, `exists_cover`, `isNilpotent_of_le_map`, `exists_step`,
`exists_kill_one`, `exists_kill_family` and `nilpotentLifting_of`. They serve only this
proof and are not claimed as Library results.
