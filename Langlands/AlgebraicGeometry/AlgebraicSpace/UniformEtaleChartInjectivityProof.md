# Uniform injectivity of affine étale charts over normed extensions: proof

Author: Worker 196.

`uniformEtaleChartInjectivity` proves `UniformEtaleChartInjectivityStatement`
(`UniformEtaleChartInjectivityStatement.lean`). Let `K` be a nontrivially normed field, `X` a
separated algebraic space over `Spec K`, `U` an affine scheme locally of finite type over `K` and
`a : h_U → X` an étale map. The proof gives one finite family
`f : Fin n → AffineCoordinateRing K U`. For every `R > 0` it gives `δ = 1 / (m R + 1) > 0`,
where `n = m + m`. Let `L/K` be any normed extension field and `p, q ∈ U(L)`. Suppose the `f_i`
values of `p` and of `q` have norm at most `R`, corresponding values differ in norm by less than
`δ`, and `p`, `q` have the same image in `X(L)`. Then `p = q`.

## Provenance

The statement is a derived internal prerequisite, not a numbered result of the literature. The
proof follows the idempotent route in the context of Task 5366. The only imported result outside
the statement's import closure is the Library port
`P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.solution`
(module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top`).
That port is from the Anthropic Lean formalisation of Fermat's Last Theorem. It is imported by
its Lean name and not changed.

## Implemented proof

Notation: `W = pairPullback a a` is the scheme that represents `U ×_X U`. Its projections are
`pr₁ = pairPullbackFst a a` and `pr₂ = pairPullbackSnd a a`. For an `L`-point `w`, the
evaluation `φ_w` is `(affineSchemePointEquiv K _ L w).toAlgHom`. The lemmas below are in file
order, in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`.

1. `closure_range_pullback_appTop_eq_top`. Let `S`, `X`, `Y` be affine schemes with maps
   `f : X ⟶ S` and `g : Y ⟶ S`. The global sections of `pullback f g` are generated as a ring
   by the images of `Γ(X)` and `Γ(Y)` under the two projections. The FLT port proves this when
   the two factors are `Spec Γ(X)` and `Spec Γ(Y)`. The proof transports it along
   `θ = pullback.map … X.isoSpec.hom Y.isoSpec.hom (𝟙 S)`. The map `θ'` in the other
   direction, built from the `isoSpec.inv` maps, satisfies `θ ≫ θ' = 𝟙`. On global sections
   this reads `θ.appTop ∘ θ'.appTop = id`, so `θ.appTop` is surjective.
   It sends each generator `pr_i^*(x)` to a generator `pr_i^*(isoSpec.hom^* x)`. The image of
   the closure is the closure of the images (`RingHom.map_closure`), which gives the claim.
2. `exists_sum_fst_mul_snd`. Every element `E` of `AffineCoordinateRing K (U ⊗ U)` has the form
   `∑_{j < m} fst^*(α_j) · snd^*(β_j)`. The algebra map
   `Algebra.TensorProduct.productMap (fst^*) (snd^*)`, from `A ⊗[K] A` with
   `A = AffineCoordinateRing K U`, has range containing `fst^* z = Φ(z ⊗ 1)` and
   `snd^* z = Φ(1 ⊗ z)`. By step 1, applied to `U.hom` and `U.hom` over the affine `Spec K`,
   this range is everything. Induction on the tensor turns a preimage into a finite sum: a pure
   tensor gives a one-term sum, and two sums are concatenated with `Fin.append`.
3. `isAffine_tensor_self`. `(U ⊗ U).left` is `pullback U.hom U.hom`, which is affine.
4. `isAffine_pairPullback_and_surjective`. Suppose `X` is separated and `U` is affine. The
   published `isClosedImmersion_pairPullbackLift` makes `ι = lift pr₁ pr₂ : W ⟶ U ⊗ U` a closed
   immersion into an affine scheme. Mathlib's `IsClosedImmersion.isAffine_surjective_of_isAffine`
   then shows that `W.left` is affine and `ι.left.appTop` is surjective.
5. `pairPullback_ringPoint_ext`. Field-valued points of `W` with equal projections are equal
   (`ext_app_of_isPullback` for `pairPullback_isPullback`).
6. `exists_diagonal_idempotent` (the diagonal idempotent). Let `a` be étale and let `U` and `W`
   be affine. There is `e ∈ AffineCoordinateRing K W` with two properties for every field `L/K`
   and every `w : ringTest K L ⟶ W`. If `φ_w(e) ≠ 0`, then `w ≫ pr₁ = w ≫ pr₂`. If
   `w ≫ pr₁ = w ≫ pr₂`, then `φ_w(e) = 1`. The proof:
   - The diagonal `d : U ⟶ W` comes from the pullback lift of `(𝟙, 𝟙)`, through the full
     functor `schemeYoneda`. It satisfies `d ≫ pr₁ = d ≫ pr₂ = 𝟙`.
   - `pr₂` is étale (`etale_pairPullbackSnd`), so its section `d.left` is an open immersion
     (`isOpenImmersion_of_section`).
   - `d.left ≫ pr₁.left = 𝟙` is a closed immersion, and `pr₁.left` is a map of affine schemes,
     hence separated. So `d.left` is a closed immersion (`IsClosedImmersion.of_comp`).
   - The range `S` of `d.left` is therefore clopen. So is its preimage `T` under
     `W.isoSpec.inv` in `PrimeSpectrum Γ(W, ⊤)`. Mathlib's
     `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` gives an idempotent `e` with
     `basicOpen e = T`.
   - For each `x` in `Spec L`, `affineSchemePointEquiv_spec` identifies
     `W.isoSpec.hom (w.left x)` with `Spec.map φ_w x = comap φ_w x`. The prime of `x` is `⊥`,
     because `L` is a field. Hence `w.left x ∈ S ↔ φ_w(e) ≠ 0`.
   - If `φ_w(e) ≠ 0`, the range of `w.left` lies in the range of the open immersion `d.left`.
     So `w.left` factors through `d.left` (`IsOpenImmersion.lift_fac`), and then
     `w ≫ pr₁ = w ≫ pr₂`.
   - Conversely, if the projections agree, step 5 gives `w = (w ≫ pr₁) ≫ d`. So `w` lands in
     `S` and `φ_w(e) ≠ 0`. Since `φ_w(e)² = φ_w(e)` in the field `L`, it follows that
     `φ_w(e) = 1`.
7. `affineSchemePointEquiv_comp_apply`. `φ_{p ≫ f}(z) = φ_p(f^* z)`. This is a restatement of
   the published `affineSchemePointEquiv_natural`.
8. `uniformEtaleChartInjectivity`, the main theorem.
   - Steps 4 and 6 give `e`. Step 4 gives `E` on `U ⊗ U` with `ι^* E = e`. Step 2 writes
     `E = ∑_j fst^*(α_j) · snd^*(β_j)`.
   - By step 7 and `ι ≫ fst = pr₁`, `ι ≫ snd = pr₂`, every `L`-point `w` of `W` satisfies
     `φ_w(e) = ∑_j φ_{w≫pr₁}(α_j) · φ_{w≫pr₂}(β_j)`.
   - The proof takes `n = m + m` and `f = Fin.append α β`. For `R > 0` it takes
     `δ = 1 / (m R + 1)`.
   - Let `p` and `q` be as in the statement. `exists_app_of_isPullback` gives a point `w` of `W`
     with projections `p` and `q`, and a point `w₀` with projections `p` and `p`.
   - Step 6 gives `φ_{w₀}(e) = 1`, that is, `∑_j p(α_j) p(β_j) = 1`.
   - If `φ_w(e) = 0`, then `∑_j p(α_j) q(β_j) = 0`. Subtracting the two sums gives
     `1 = ∑_j p(α_j) (p(β_j) − q(β_j))`. By the triangle inequality and multiplicativity of the
     norm, `1 ≤ m · R · δ = m R / (m R + 1) < 1`, a contradiction.
   - So `φ_w(e) ≠ 0`. Step 6 then gives `p = w ≫ pr₁ = w ≫ pr₂ = q`.

## Scope

- The theorem keeps every quantifier of the statement: the universe `u`, every nontrivially
  normed field `K`, and every normed extension field `L`. That includes extensions of infinite
  degree and incomplete, archimedean or nonarchimedean ones.
- The family `f` is chosen before `R`. The radius `δ` depends only on `m` and `R`, and is chosen
  before `L`.
- No completeness, henselian, finite-degree or nonarchimedean hypothesis is added.
- The proof uses only part of the hypotheses:
  - the bound for `p` on the first `m` coordinates;
  - the closeness hypothesis on the last `m` coordinates;
  - the same-image hypothesis.
- The bound for `q` and the instance `LocallyOfFiniteType U.hom` are not used. Step 2 needs
  only that every tensor is a finite sum of pure tensors.
- The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
