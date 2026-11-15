# Zero-value root jumps descend, given an abstract Galois descent of jumps

Module `Langlands.Geometry.Building.UnramifiedZeroJumpDescentAssembly`.

This module reduces `Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement` (module
`UnramifiedAffineRootRestrictionReduction`) to a descent principle for zero-value filtration
jumps. It contains no `def` and no new statement.

Notation. `K/k` is a field extension, `b = algebraBaseMap k K`, and `S_K`, `T_K`, `G_K`, `f_K`,
`iS_K`, `iT_K` and `α_K` are the base changes along `b`. `IsRootFiltrationJump i ψ a r` (module
`RootJumpLiftNonMultipliable`) is `U_{a,ψ,r} ⊈ U_{a,ψ,r+} · U_{2a}`.
`RootFunctionFamily.fieldRestrict ψ` is the family `a ↦ (g ↦ ψ_{a_K}(g_K))` on `(G, S)`.

## The three hypotheses

For a family `ψ` of root functions of `(G_K, S_K)` and a root `α` of `(G, S)`, write
`U = rootGroupPoints iS_K α_K`.

- (H1) For `g, h ∈ U`, `min (ψ_{α_K} g) (ψ_{α_K} h) ≤ ψ_{α_K} (g h⁻¹)`.
- (H2) For `σ ∈ Aut(K/k)` and `g ∈ U`, `ψ_{α_K} (σ g) = ψ_{α_K} g`, where `σ g` is
  `rationalConjugate k K G σ g`.
- (H3) For `t ∈ characterValuationKernel v S_K` (every rational character of `S_K` has
  `v`-valuation one at `t`) and `g ∈ U`, `ψ_{α_K} (t g t⁻¹) = ψ_{α_K} g`, where `t` also
  denotes its image in `G_K(K)` under `iS_K`.

## Results

### Core, over an arbitrary field extension

`isRootFiltrationJump_torusFieldRestricted_of_descent`. Data: `iS : S ⟶ G` (a monomorphism),
`iT : T ⟶ G` and `f : S ⟶ T` with `groupHom f ≫ iT = iS`; `S` split over `k` and `T_K` split
over `K`; opposite factor pairs for `iT_K` and for `iS`; a valuation `v` of `K` with values in
`ℤₘ₀`; a centralizer datum `C` for `iT_K`; a valuation `φ` of the root datum of
`(G_K, T_K)` that satisfies V6 for `(v, C)` and is fixed by every `σ ∈ Aut(K/k)`; a root `χ` of
`(G_K, T_K)` and a root `α` of `(G, S)` with `f_K ≫ χ = α_K`; and a jump of `χ` at `0` for `φ`.
Hypothesis `hdesc`: every family `ψ` of root functions of `(G_K, S_K)` that satisfies (H1),
(H2) and (H3) for `α` and has a jump of `α_K` at `0` gives a jump of `α` at `0` for
`fieldRestrict ψ`. Conclusion: a jump of `α` at `0` for
`torusFieldRestrictedRootFunctionFamily hS hT hE hφ f_K`, the torus restriction of `φ`
followed by field restriction (module `RootValueTorusFieldRestriction`).

Proof.

1. `groupHom f_K ≫ iT_K = iS_K` (functoriality of base change).
2. `α_K` is a root of `(G_K, S_K)` (`mem_roots_baseChange_iff`), and no `n • α_K` with `n ≥ 3`
   is a root. Otherwise `n • α` would be a root of `(G, S)`
   (`mem_roots_baseChange_iff`), which contradicts
   `RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two`.
3. The jump of `χ` gives a jump of `α_K` at `0` for the torus restriction
   `ψ = torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ f_K`
   (`isRootFiltrationJump_torusRestricted_of_isRootFiltrationJump`, module
   `TorusRestrictedRootJump`). Its base is `groupHom f_K ≫ iT_K`, which step 1 rewrites to
   `iS_K`.
4. `ψ` satisfies (H1), (H2) and (H3): these are
   `torusRestrictedRootFunctionFamily_min_le_mul_inv`,
   `torusRestrictedRootFunctionFamily_rationalConjugate` (from the Galois fixedness of `φ`) and
   `torusRestrictedRootFunctionFamily_conj_of_mem_characterValuationKernel` (from V6, with
   `C.j`, `C.s`, `C.bijective`, `C.isRepresentedBy` and `C.comp_eq`), all from module
   `TorusRestrictedRootInvariance`, after the rewrite of step 1.
5. `hdesc` gives a jump of `α` at `0` for `fieldRestrict ψ`, which is by definition
   `torusFieldRestrictedRootFunctionFamily hS hT hE hφ f_K`.

### The target, given the descent principle

`unramifiedZeroJumpDescent_of_galoisDescent (hdesc) : UnramifiedZeroJumpDescentStatement.{u}`.
Hypothesis `hdesc`: for every nonarchimedean local field `F`, every connected reductive `G`, every
maximal split torus `iS : S ⟶ G`, every root `α` of `(G, S)` and every family `ψ` of root
functions of `(G_K, S_K)` with `K = inertiaFixedField F` (the maximal unramified extension),
(H1), (H2) and (H3) for `v = MaximalUnramified.valuation F` and a jump of `α_K` at `0` for `ψ`
give a jump of `α` at `0` for `fieldRestrict ψ`.

Proof. After introducing the data of the target statement (`F`, `G`, `S`, `iS`, `T`, `iT`, `f`,
`hiT`, `hE`, `D`, `C`, the V6 hypothesis `hΩ`, the fixed point `x`, `χ`, `α` and the jump of `χ`),
opposite factor pairs for `iS` come from
`RelativeRoot.exists_oppositeFactorPair_of_componentReductivity` with the published
`RelativeRoot.kernelCentralizerComponentReductive`. The core result applies with `k = F`,
`K = inertiaFixedField F`, `v = MaximalUnramified.valuation F`, `φ = x.val`
(`D.isRootDatumValuation_of_mem x.mem`), V6 from `hΩ x.val x.mem`, Galois fixedness from the
hypothesis that `x` is fixed, and `hdesc` specialized to `F, G, S, iS, α`. The family `φ x` of the
statement is `torusFieldRestrictedRootFunctionFamily` with these arguments, so the conclusion
of the core is the goal. The declaration needs `maxHeartbeats 6400000`.
