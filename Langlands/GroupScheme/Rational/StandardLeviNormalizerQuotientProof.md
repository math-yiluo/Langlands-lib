# Proof of Renard V.4.3.3: `W(M, M)/W_M ≃ N_G(M)/M` for standard Levi subgroups

Module `Langlands.GroupScheme.Rational.StandardLeviNormalizerQuotientProof`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.

The main theorem is `standardLeviNormalizerQuotient`. Its type is exactly the published
statement `Langlands.GroupScheme.StandardLeviNormalizerQuotientStatement`, from
`Langlands.GroupScheme.Rational.StandardLeviWeylStatements` (Renard 2026, V.4.3, (V.4.3.3),
printed p.119 / PDF p.125). It adds no hypothesis. Worker 131 wrote this proof for Task 5688.

Setting: `k` is a nonarchimedean local field, `G` a connected reductive group over `k`,
`i : T ⟶ G` a maximal split torus, `ν` a generic cocharacter and `I` a finite set of simple
relative roots. `L_I(k)` is `levi i ν I`, `N(k)` is `normalizerPoints i`, `Z(k)` is
`centralizerPoints i`, `W = N(k)/Z(k)` is `relativeWeylGroup i`, and `W_I` is
`standardRelativeWeylGroup i ν (rootSet i ν I)`, the image of `L_I(k) ∩ N(k)` in `W`.

## Helpers (namespace `StandardLeviNormalizerQuotient`)

- `conj_mem_of_map_eq`, `inv_conj_mem_of_map_eq`, `map_conj_mul_eq` are elementary group
  theory. Suppose `H.map (MulAut.conj g) = H` for a subgroup `H` of a group `Γ`. Then `g z g⁻¹`
  and `g⁻¹ z g` lie in `H` for every `z ∈ H`, and `H.map (MulAut.conj (m * g)) = H` for every
  `m ∈ H`.
- `comp_innerIso_hom_base`: on base points the inner automorphism `G.innerIso g` is
  `x ↦ g x g⁻¹`. This is the published `comp_innerIso_hom` together with `constantPoint_self`.
- Connected reductivity of the standard Levi is supplied by the first conjunct of the published `standardLeviSplitComponentStatement`.

## Clause 1: `mk_mem_standardRelativeWeylGroup_iff`

For `n ∈ N(k)`: `[n] ∈ W_I ↔ n ∈ L_I(k)`.

- (←) is the definition of `W_I`: `n` itself is a witness.
- (→) Membership gives `n' ∈ N(k) ∩ L_I(k)` with `[n'] = [n]`. `QuotientGroup.eq` gives
  `n'⁻¹ n ∈ Z(k)`. The published `centralizerPoints_le_levi` gives `Z(k) ⊆ L_I(k)`, so
  `n = n' (n'⁻¹ n) ∈ L_I(k)`.

## Clause 2: `exists_normalizerPoint_of_map_conj_eq`

Let `g ∈ G(k)` with `g L_I(k) g⁻¹ = L_I(k)`, and write `J = rootSet i ν I`.
`hrep := Standard.isRepresentedBy_leviHom i ν J` says that the closed subgroup
`Standard.leviHom : Standard.leviScheme i ν J ⟶ G` represents `standardLevi i ν J` on every
test scheme.

1. **The conjugate torus lies in the Levi.** Let `i' = i ≫ Int(g)`. A `k`-point of its
   range is `g (t ≫ i) g⁻¹` for a point `t` of `T` (`comp_innerIso_hom_base`). Here
   `t ≫ i ∈ L_I(k)` by the published `torusPoints_le_levi`. Since `g` normalizes `L_I(k)`,
   `g (t ≫ i) g⁻¹ ∈ L_I(k)`. So the `k`-points of `range i'` lie in those of
   `range Standard.leviHom`. The torus `T` is split, hence smooth, affine and connected
   (published `IsSplitTorus.smooth`, `IsSplitTorus.isAffineHom`,
   `IsSplitTorus.connectedSpace`). `leviHom` is a closed subgroup
   (`Standard.isClosedSubgroup_leviHom`). The published density criterion
   `SubgroupFunctor.range_le_of_localField_points` therefore gives
   `range i' ≤ standardLevi i ν J` on every test scheme.
2. **Two maximal split tori of the Levi.** `i'` is a maximal split torus of `G`
   (`IsMaximalSplitTorus.comp_iso`), and so is `i`. Also `range i ≤ standardLevi i ν J`,
   by the published `range_le_torusCentralizer` and `torusCentralizer_le_standardLevi`.
   Factor both through the representative with `hrep.factorHom`, getting
   `f, f₀ : T ⟶ Standard.leviScheme i ν J` with `f ≫ leviHom = i'` and `f₀ ≫ leviHom = i`.
   Both factors are maximal split tori of the Levi scheme
   (`IsMaximalSplitTorus.isMaximalSplitTorus_factorHom`).
3. **Conjugacy in the Levi.** The Levi scheme is connected reductive
   (the first conjunct of `standardLeviSplitComponentStatement`). The published `maximalSplitTorusConjugacy` gives a
   point `m` of the Levi scheme and an automorphism `e` of `T` with
   `f ≫ Int(m) = e ≫ f₀`. Let `m' = m ≫ leviHom ∈ G(k)`; `m' ∈ L_I(k)` because `hrep`
   identifies the range of `leviHom` with `standardLevi`. Inner automorphisms commute with
   group homomorphisms (published `innerIso_hom_comp`). Composing with `leviHom` therefore gives
   `i ≫ Int(g) ≫ Int(m') = e ≫ i`, that is `i ≫ Int(m' g) = e ≫ i` (`innerIso_mul_hom`).
   Repackaging `e` as an automorphism of the commutative group scheme `T` (as in the
   published `RelativeWeylAbsoluteRestrictionProof`) shows `n := m' g ∈ N(k)`.
4. **Conclusion.** `n L_I(k) n⁻¹ = L_I(k)` by `map_conj_mul_eq`, since `m' ∈ L_I(k)` and `g`
   normalizes `L_I(k)`. Finally `n⁻¹ g = g⁻¹ m'⁻¹ g ∈ L_I(k)` by `inv_conj_mem_of_map_eq`.

This is Renard's argument for surjectivity: maximal split tori are conjugate in `M`. In
the source `g A_∅ g⁻¹` is a maximal split torus of `g M g⁻¹ = M`. The Lean statement only
says that `g` normalizes `M(k)`, so step 1 recovers the scheme-level containment from the
Zariski density of rational points of the split torus.

## Main theorem: `standardLeviNormalizerQuotient`

The proof introduces the data, installs `hG.isAffineHom` and the monomorphism instance of
the split torus, and combines clause 1 and clause 2.

## Dependencies

Published results used: `centralizerPoints_le_levi`, `torusPoints_le_levi`,
`Standard.isRepresentedBy_leviHom`, `Standard.isClosedSubgroup_leviHom`,
`SubgroupFunctor.range_le_of_localField_points`, `IsSplitTorus.smooth`,
`IsSplitTorus.isAffineHom`, `IsSplitTorus.connectedSpace`, `IsMaximalSplitTorus.comp_iso`,
`IsMaximalSplitTorus.isMaximalSplitTorus_factorHom`,
`SubgroupFunctor.IsRepresentedBy.factorHom_comp`, `range_le_torusCentralizer`,
`torusCentralizer_le_standardLevi`, `maximalSplitTorusConjugacy`,
`standardLeviSplitComponentStatement`, `innerIso_hom_comp`, `innerIso_mul_hom`,
`comp_innerIso_hom`, `constantPoint_self`. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.
