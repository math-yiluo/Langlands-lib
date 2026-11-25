# Semilinear coordinates on rational root-group points: the proof

## Purpose and provenance

This module is internal to the proof of
`Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement`. It proves the
proposition `Langlands.Geometry.Building.RootGroupLinearization` of the module
`RootGroupLinearization`. It introduces no new statement. Its main theorem supplies the
hypothesis `RootGroupLinearization` of the Galois descent of filtration jumps (module
`UnramifiedZeroJumpGaloisDescent`) in `UnramifiedZeroJumpDescentProof` and
`UnramifiedZeroJumpForwardDescent`.

Mathematically it collects standard facts about the root groups of a split torus (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, §2.6.8, printed p. 95/PDF p. 126):
`U_a / U_{2a}` and `U_{2a}` are vector groups over
the base field, their coordinates commute with the Galois action on coefficients, and the torus
acts on them through `a` and `2a`. The proof below is the Library's coordinate theory of root
groups over `k`, read at the `k`-scheme `Spec K`.

## Main theorem

`Langlands.Geometry.Building.rootGroupLinearization`. Let `k`, `K` be fields with
`[Algebra k K]`, `S` a commutative `k`-group scheme, and `G` a `k`-group scheme with
`[IsAffineHom G.X.hom]` and `[Smooth G.X.hom]`. Let `iS : S.toGrp ⟶ G` be a homomorphism whose
underlying scheme morphism is a monomorphism (`[Mono iS.hom.hom.left]`), with
`hS : IsSplitTorus S.toGrp` and `hE : RelativeRoot.HasOppositeFactorPairs iS`. Let
`α ∈ relativeRoots iS` and let `v` be a valuation on `K` with values in a linearly ordered
commutative group with zero. Then `RootGroupLinearization iS α v` holds.

## Auxiliary declarations

In the namespace `Langlands.Geometry.Building.RootGroupLinearizationProof`:

* `specTest k K`: the `k`-scheme `Spec K`, defined as `algSpec` of the `k`-algebra `K`.
  `specAut k K σ` is the `k`-automorphism `Spec σ` for `σ ∈ Aut(K/k)`.
* `sectionValue k K`: the ring isomorphism `Γ(Spec K) ≃+* K` given by `Scheme.ΓSpecIso`.
  `sectionValue_specAut`: pulling back a global section along `Spec σ` acts as `σ` on `K`. This
  is `Scheme.ΓSpecIso_naturality`.
* `conjugate_eq`: the coefficient action `GaloisPoint.conjugate` of `σ` on `K`-points is
  precomposition with `Spec σ` (by definition).
* `specAut_comp_gm_symm`: if `σ c = c` for a unit `c`, then the point of `𝔾_m` given by `c` is
  fixed by precomposition with `Spec σ`.
* `pointCoords e v`: for a `k`-group `V` with vector coordinates
  `e T : (T ⟶ V) ≃* Multiplicative (Γ(T)^n)`, the coordinates in `K^n` of a point
  `v : Spec K ⟶ V`. The lemmas `pointCoords_mul`, `pointCoords_eq_zero_iff`,
  `pointCoords_specAut` and `pointCoords_act` state that they are additive and vanish only at
  `1`. Natural coordinates (`IsNaturalVectorCoordinates`) are `σ`-semilinear. Weight-`a`
  coordinates (`IsWeightVectorCoordinates`) scale by the character value `a(s)` under the torus
  action of a point `s : Spec K ⟶ S`.
* `liftCoords jU F g`: for a homomorphism `jU : U ⟶ G` and `F` defined on points of `U`, the
  value of `F` at a lift of `g : Spec K ⟶ G` through `jU`, and `0` when there is no lift
  (classical choice). `liftCoords_comp`: if `jU` is a monomorphism, then
  `liftCoords jU F (y ≫ jU) = F y`.
* `mem_rootGroupPoints_baseChange_iff`: a `K`-point `x` of `G_K` lies in
  `rootGroupPoints (i_K) (α_K)` if and only if the `k`-scheme point
  `baseChangeCoeffEquiv k K G x : Spec K ⟶ G` lies in the root subgroup functor
  `RelativeRoot.subgroup i α`. This uses `RelativeRoot.subgroup_baseChange` and
  `SubgroupFunctor.mem_baseChange`. `mem_rootGroupPoints_baseChange_iff_exists` restates this
  for a representative `jU` of the root functor: the point lifts through `jU`.
* `rationalCoords jU F`: `liftCoords` composed with `baseChangeCoeffEquiv`, a map on `G_K(K)`.
  For a representative `jU` of the root functor of `a`:
  * `rationalCoords_mul`: it is additive on `U_{a_K}(K)` if `F` is additive;
  * `rationalCoords_eq_zero_iff`: it vanishes at `x` exactly when `x` lies in a given subgroup
    functor `D`, if `F` vanishes exactly on the lifts landing in `D`;
  * `rationalConjugate_mem`: `U_{a_K}(K)` is stable under `rationalConjugate`;
  * `rationalCoords_rationalConjugate`: it is `σ`-semilinear if `F` is;
  * `rationalCoords_conj`: if `T` corresponds to `s ≫ iS` with `s : Spec K ⟶ S`, then
    conjugation by `T` preserves `U_{a_K}(K)` and multiplies the coordinates by `a(s)`, if `F`
    has weight `a`. This uses `RelativeRoot.subgroupAction_act_comp`.

In the namespace `Langlands.Geometry.Building`:

* `exists_unitCocharacterPoint iS ν v hc`: for a cocharacter `ν` of `S` and a unit `c` with
  `v c = 1`, a point `t ∈ characterValuationKernel v S_K` whose image `T` in `G_K(K)`
  corresponds to the `k`-scheme point `ν(c) ≫ iS`. `T` is fixed by every `σ` with `σ c = c`. The
  point comes from `exists_mem_characterValuationKernel_baseChangeCoeffEquiv_eq` (module
  `UnramifiedFixedPointRootDescent`). The fixedness comes from
  `baseChangeCoeffEquiv_rationalConjugate` and `specAut_comp_gm_symm`.
* `characterValue_unitCocharacterPoint`: `a(ν(c)) = c ^ ⟨a, ν⟩`, by
  `CoordinateWeights.characterValue_cocharacter`.

## Proof of the main theorem

By `RelativeRoot.HasOppositeFactorPairs.nat_multiple_le_two`, no multiple `n α` with `n ≥ 3` is
a relative root. `mem_roots_baseChange_iff` transfers the root `2α` to `2α_K` and back, so
`doubleRootGroupPoints (i_K) (α_K)` is `U_{2α_K}(K)` when `2α` is a root and `⊥` otherwise. The
proof splits on whether `2α` is a root.

**`2α` is a root (`d = 1`).** `RelativeRoot.subgroup_has_smooth_closed_representative` gives
representatives `jU : U → G` of the root functor of `α` and `j₂ : U₂ → G` of the root functor of
`2α`. `RelativeRoot.nonempty_doubleRootCommutatorPairing` gives a pairing package `C`, with a
quotient map `C.q : U → V` whose kernel is the root functor of `2α`.
`exists_bilinear_coordinates` gives natural weight coordinates `eV` on `V` (weight `α`) and `e₂`
on `U₂` (weight `2α`). Set `q = rationalCoords jU (pointCoords eV ∘ C.q)` and
`e = rationalCoords j₂ (pointCoords e₂)`. The kernel condition for `q` uses
`mem_range_kernelι_iff` and the fppf-quotient property of `C.q`. Injectivity of `e` holds
because `j₂` is a monomorphism. The torus point is `exists_unitCocharacterPoint` for the coroot
`ν` of `2α` (`RelativeRoot.HasOppositeFactorPairs.rootCoroot`). Since `⟨2α, ν⟩ = 2`, we get
`⟨α, ν⟩ = 1`, so `ν(c)` scales `q` by `c` and `e` by `c²`.

**`2α` is not a root (`d = 2`, `m = 0`).** Then `α` has no higher multiples among the roots, and
`RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots` gives natural weight-`α`
coordinates `eU` on a representative `jU : U → G`. Set `q = rationalCoords jU (pointCoords eU)`
and `e = 0` with values in `K^0`. All conditions on `e` hold because `K^0` is a subsingleton.
`q` vanishes exactly at `1 = ⊥` because `jU` is a monomorphism. The torus point is
`exists_unitCocharacterPoint` for the coroot `ν` of `α`, with `⟨α, ν⟩ = 2`, so `q` scales by
`c²`.

## Implementation notes

All coordinate work happens in generic lemmas, which are stated before the main theorem, over
the test scheme `Spec K`. The main theorem only instantiates them. The file sets
`backward.isDefEq.respectTransparency false` (and its `.types` variant), as the imported module
`RootGroupLinearization` does.
