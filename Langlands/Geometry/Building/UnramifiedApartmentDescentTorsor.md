# Galois-fixed translations descend to the largest split subtorus

Author: Worker 4356.

Lean module: `Langlands.Geometry.Building.UnramifiedApartmentDescentTorsor`.

Let `K/k` be a Galois extension that need not be finite, `T` an affine `k`-torus of finite
type, `t : S → T` its largest split subtorus, and `jT : T → G` a homomorphism into an affine
`k`-group. This module proves three things.

1. Two `Aut(K/k)`-fixed points of an apartment class of `(G_K, T_K)` differ by the push-forward
   of a real cocharacter of `S`.
2. The torus-then-field restriction to `(G, S)` is injective on such fixed points.
3. Both statements hold in the setting of `UnramifiedValuationDescentStatement`, with
   `K = inertiaFixedField F`. Statement 2 is clause 3 of that statement.

The Library already has the corresponding vector statement for finite Galois `K/k`:
`exists_descentCocharacterMap_sub_mem` (module `QuasiSplitApartmentShifts`). Its proof averages
over the finite Galois group. The maximal unramified extension is infinite, so this module
uses a different argument. A character of `T_K` fixed by the whole Galois group descends to
`k`. The roots of `T_K` have finite Galois orbits, which replaces the finite group.

## Galois-invariant characters (namespace `Langlands.GroupScheme`)

- `eq_zero_of_characterRestrict_baseChange_of_eq_id`: let `b : X → X` be a base map with
  `b = 𝟙`, and `f : H → G` a homomorphism whose character restriction is injective. A character
  of `G_b` whose restriction along `f_b` vanishes is zero. Proof: substitute `b = 𝟙`, transport
  along the published `baseChangeIdIso`, and use the naturality of the identity comparison
  `Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso`.
- `baseMap_self_eq_id`: `Spec(k → k)` is the identity.
- `IsLargestSplitSubtorus.galoisInvariant_character_eq_zero`: with `K/k` Galois, a character
  `χ` of `T_K` that is fixed by every `σ : K ≃ₐ[k] K` and restricts to zero on `S_K` is zero.

  Proof. Regard `χ` as a rational character `ψ` of the base change (`baseChangedCharacter`).
  Galois invariance and the published `tensorConj_tensorValue_baseChangedCharacter` show that
  the universal tensor value of `ψ` is fixed by every `σ`. The published
  `AffineCharacterTowerDescent.fixedDescend`, applied to the tower `k → k → K`, gives a
  character `ψ_k` of `T` base-changed along `k → k`. Its existence uses
  `InfiniteGalois.mem_range_algebraMap_iff_fixed`, so `K/k` may be infinite. By
  `characterRestrict_fixedDescend`, `ψ_k` restricts to zero on `S`. The published
  `IsLargestSplitSubtorus.characterRestrict_injective` and the identity-base-change lemma give
  `ψ_k = 0`. Finally `valueE_fixedDescend` and `ext_valueE` give `ψ = 0`, so `χ = 0`.

## Finite orbits and vanishing (namespace `Langlands.Geometry.Building`, section `Descent`)

- `evalAt k T w`: the integral linear form `χ ↦ eval T χ w`, defined through the published
  pairing `pair`. `evalAt_apply` identifies its values.
- `galoisRepresentation_eq_of_galoisRootAction_eq`: if `σ` and `τ` induce the same permutation
  of the roots of `T_K` (published `galoisRootAction`), they act equally on the integral span
  of the roots. The proof is induction on the span.
- `finite_range_galoisRepresentation`: if the roots are finite, every character in their
  integral span has a finite Galois orbit, because the orbit map factors through the finite
  type `Equiv.Perm` of the roots.
- `eval_eq_zero_of_mem_span`: characters in the integral root span annihilate the root
  annihilator.
- `eval_eq_zero_of_characterRestrict_eq_zero`: let `w : V(T_K)` satisfy
  `σ w - w ∈ rootAnnihilator` for every `σ` (published `galoisCocharacterAction`). If `χ` is in
  the integral root span and restricts to zero on `S_K`, then `χ(w) = 0`.

  Proof. Let `s` be the sum of the finite Galois orbit of `χ`. Each `σ` permutes the orbit, so
  `s` is Galois invariant. Restriction is Galois equivariant (published
  `rationalCharacters.characterRestrict_galoisRepresentation`), so every orbit element
  restricts to zero, and so does `s`. Hence `s = 0` by the previous section. For an orbit
  element, `(σχ)(w) = χ(σ⁻¹w) = χ(w)` (published `eval_galoisCocharacterAction_right`, and
  `σ⁻¹w - w` lies in the annihilator). So `0 = s(w) = |orbit| · χ(w)`, and `χ(w) = 0`.
- `exists_descentCocharacterMap_sub_mem_of_isGalois`: under the same hypotheses, with `S`
  split and finitely many roots, there is `v : V(S)` with
  `w - descentCocharacterMap k K t hS v ∈ rootAnnihilator`.

  Proof. Let `R` be the roots. Define the integral maps `Ψ : (R →₀ ℤ) → X^*(S_K)`,
  `c ↦ Σ c_α (α restricted to S_K)`, and `ℓ₀ : (R →₀ ℤ) → ℝ`, `c ↦ Σ c_α α(w)`. The previous
  lemma, applied to `Σ c_α α`, gives `ker Ψ ≤ ker ℓ₀`. So `ℓ₀` factors through the range of
  `Ψ` (`Submodule.liftQ`, `LinearMap.quotKerEquivRange`). It extends to all of `X^*(S_K)`
  because `ℝ` is an injective `ℤ`-module (Mathlib's `Module.Baer.of_divisible` and
  `Module.Baer.extension_property`). Extend it `ℝ`-linearly (`LinearMap.liftBaseChange`). The
  published pairing of the split torus `S_K` is perfect (`isPerfPair_of_isSplitTorus`), so the
  extension is `pair · u` for some `u : V(S_K)`. Then `α(w) = (α|S_K)(u)` for every root `α`.
  With `v` the preimage of `u` under `splitCocharacterBaseChange`, `descentCocharacterMap v`
  is the push-forward of `u`, and `pair_cocharacterMapReal` gives the claim.

## Apartments (section `ApartmentTorsor`)

Let `D : KPApartmentData j_K ω`, and suppose `j_K` is a monomorphism.

- `KPApartmentData.exists_descent_vadd_of_galoisFixed`: for Galois-fixed `x y : D.Apartment`
  there is `v : V(S)` with `y = descentCocharacterMap k K t hS v +ᵥ x`. Proof: `y = w +ᵥ x` by
  equipollence. The published `RootFunctionFamily.galoisAction_vadd` and the fixedness of `x`
  and `y` give `σ w +ᵥ x = w +ᵥ x`, so `σ w - w` lies in the annihilator
  (`IsRootDatumValuation.vadd_eq_vadd_iff`). Then apply the previous section.
- `torusFieldRestricted_eq_vadd_of_eq_descent_vadd` (assuming `G` smooth): if
  `ψ = descentCocharacterMap v +ᵥ φ`, the torus-then-field restriction of `ψ` is `v +ᵥ` that
  of `φ`. The proof uses the published `torusRestrictedRootFunctionFamily_congr`,
  `torusRestrictedRootFunctionFamily_vadd` and `RootFunctionFamily.fieldRestrict_vadd`.
- `descentCocharacterMap_mem_rootAnnihilator_of_vadd_eq`: let `t_K ≫ j_K = i_K` for
  `i : S → G`. Suppose the order is given by a homomorphism `ω : Kˣ →* Multiplicative ℝ` that
  is nonzero on some unit of `k`, and `φ` is split-torus compatible for it. If
  `v +ᵥ φ' = φ'` for the torus-then-field restriction `φ'` of `φ`, then
  `descentCocharacterMap v` annihilates every root `α` of `T_K`.

  Proof. Write `α(descentCocharacterMap v) = (α|S_K)(v_K)` (published
  `eval_descentCocharacterMap`). If `α|S_K = 0` there is nothing to prove. Otherwise
  `α|S_K` is a root of `i_K`, because `Lie(G)_α ⊆ Lie(G)_{α|S_K}` (published
  `weightSpace_le_comp`). It is the base change of a character `a` of `S`
  (`IsSplitTorus.characterLattice_baseChange_bijective`), and `a` is a root of `i`
  (`mem_roots_baseChange_iff`). The published
  `torusFieldRestrictedRootFunctionFamily_image_infinite` gives `g` with `φ'(a, g) ≠ ⊤`.
  Comparing `φ'(a, g) + a(v) = φ'(a, g)` gives `a(v) = 0`, and
  `eval_splitCocharacterBaseChange` finishes.
- `KPApartmentData.eq_of_torusFieldRestricted_eq`: Galois-fixed points with equal restrictions
  are equal. By the first item, `y = descentCocharacterMap v +ᵥ x`. By the second, the
  restriction of `y` is `v +ᵥ` that of `x`. By the third, `descentCocharacterMap v` is in the
  annihilator, so `y = x` (`vadd_eq_self_iff`).

## The unramified setting (section `Unramified`)

Here `F` is a nonarchimedean local field and `K = inertiaFixedField F`.

- `unramifiedTorus_structure`: assume `G` is connected reductive and affine, `iS : S → G` is
  a maximal split torus, `f : S → T` with `f ≫ iT = iS`, and `iT_K` is a maximal split torus of
  `G_K`. Then `T` is affine and locally of finite type, `T` is a torus, and `f` is a largest
  split subtorus.

  Proof. Affineness descends from `T_K` along the fpqc map `Spec K → Spec F` (Mathlib's
  `MorphismProperty.of_pullback_snd_of_descendsAlong` with the published
  `fieldExtension_fpqc`). Closedness of `iT` descends by the published
  `IsClosedSubgroup.of_baseChange_of_isAffine`, so `T` is of finite type over `F`. `T` is a
  torus by `IsTorus.of_baseChange`. Finally the published `IsMaximalSplitTorus.of_comp` and
  `isLargestSplitSubtorus` apply.
- `unramified_exists_descent_vadd_of_galoisFixed`: the torsor statement for every
  `D : KPApartmentData iT_K ω`. The roots of `T_K` are finite by
  `IsSplitTorus.finite_relativeRoots`.
- `unramified_eq_of_torusFieldRestricted_eq`: clause 3 of
  `UnramifiedValuationDescentStatement`, for
  `D : KPApartmentData iT_K (IntegerValuation.order (MaximalUnramified.valuation F))`. The
  order is the homomorphism `orderUnits` followed by the cast `ℤ → ℝ`. A unit of `F` of order
  one exists by `Plancherel.fieldOrderUnits_surjective` and
  `MaximalUnramified.orderUnits_base_eq_fieldOrderUnits`.

## Provenance

The statements are the affine-space structure of `A(S) = A(T_K)^Γ` underlying Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §9.6 (Construction 9.6.1 and Lemma 9.6.3, printed
pp. 364–366). The descent of Galois-invariant characters to the largest split subtorus is the
standard fact that `X^*(T)^Γ ⊗ ℚ` restricts isomorphically to `X^*(S) ⊗ ℚ` for the maximal
split subtorus `S` of `T`. The Lean proof avoids a finite splitting field. It uses the
infinite-Galois descent of characters already in the Library, finite Galois orbits of roots,
and the injectivity of `ℝ` as a `ℤ`-module.
