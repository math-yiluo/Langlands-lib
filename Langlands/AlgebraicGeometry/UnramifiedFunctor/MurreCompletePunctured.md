# Completeness of finite algebras and pro-representability on complete local rings

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletePunctured`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. It supports the proof of Step 2a
of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I, Step 2a).
Two inputs of the lifting argument in `MurreCompleteStar` are proved here: rings obtained from a
finite algebra over the complete ring `R` are complete, and `ξ_y` is pro-representable on all
complete local noetherian `R`-algebras.

## Section `Finite`

* `isAdicComplete_of_finite`: let `M` be a finite module over a noetherian ring `A` that is
  `I`-adically complete. Then `M` is `I`-adically complete. The proof uses Mathlib's
  `AdicCompletion.of_bijective_iff`: the map `M → M̂` is the composite of
  `M ≅ Â ⊗_A M` (from `A ≅ Â`) with `AdicCompletion.ofTensorProduct`, which is bijective for
  finite modules over noetherian rings
  (`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`).
* `isAdicComplete_map_of_finite`: a finite `A`-algebra `S` is complete for the ideal `I S`. For
  every `n`, the submodules `I^n • S` (over `A`) and `(I S)^n` (over `S`) have the same elements,
  so the Hausdorff and precompleteness conditions transfer from the previous item.

## Section `Complete`

Let `R` be complete local noetherian, and let `Y k`, `q k`, `e k` be as in `MurreCompleteChart`.

* `residueQuotₐ I hI`: the `R`-algebra map `κ(A) → κ(A/I)` for a proper ideal `I` of a local
  ring `A`. `residueQuotₐ_comp` says it is compatible with the residue maps.
* `chart_lift_complete` (pro-representability): take a complete local noetherian `R`-algebra `A`
  with local structure map and `η ∈ F(Spec A)`. Suppose the restriction of `η` to the residue
  field comes from `ξ_y` along some `σ : B_y → κ(A)`. Then `η` is the restriction of `ξ_y` along
  some `ψ : B_y → A`.

  Proof. `A/m_A^(n+1)` kills `m^(n+1)`, because `m` maps into `m_A`. `chart_lift`
  (`MurreCompleteChart`) gives maps `ψ_n : B_y → A/m_A^(n+1)` restricting `ξ_y` to the images of
  `η`. They are compatible by `chart_inj_level`. Since `A` is complete, they define
  `ψ = IsAdicComplete.liftAlgHom`. The restrictions of `ξ_y` along `ψ` and of `η` agree on every
  `A/m_A^n`, so they are equal by the uniqueness half of (F3) (`adic_unique`).
