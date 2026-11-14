# Galois-fixed characters of a torus in an anisotropic group

Module `Langlands.GroupScheme.Rational.AnisotropicGaloisFixedCharacters`.

## Contents

Throughout, `k` is a field, `G` is a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`
and `[LocallyOfFiniteType G.X.hom]`, and `T` is a commutative group scheme over `Spec k`. For a
field extension `L/k`, `T_L` is the published base change
`(CommGroupScheme.baseChange (algebraBaseMap k L)).obj T`. The definitions used are:

- `IsTorus T.toGrp` (module `Langlands.GroupScheme.Torus.Lattice`): `T` becomes a split torus
  after base change to some field extension of `k`.
- `IsAnisotropic G` (module `Langlands.GroupScheme.Rational.SplitTorus`): the split rank of `G`
  is zero, i.e. `G` contains no nontrivial closed split torus.
- `IsClosedSubgroup i` for `i : T.toGrp ⟶ G` (module `Langlands.GroupScheme.Reductive.Basic`):
  the underlying morphism of schemes is a closed immersion.
- `characterLattice.galoisRepresentation k L T` (module
  `Langlands.GroupScheme.Torus.LatticeGalois`):
  the action of `σ : L ≃ₐ[k] L` on the character lattice `X^*(T_L)` by transport along `Spec σ`.

### Results

- `isTorus_of_isSplitTorus_baseChange K h`: if `T_K` is a split torus for some field extension
  `K/k` (`h : IsSplitTorus (T_K).toGrp`), then `IsTorus T.toGrp`. This is the definition of
  `IsTorus` with the base change written as `CommGroupScheme.baseChange`.
- `IsAnisotropic.galoisFixed_character_eq_zero hG hi hT L ψ hfix`: let `G` be anisotropic,
  `i : T.toGrp ⟶ G` a closed subgroup (`hi`) with `T` a torus (`hT : IsTorus T.toGrp`), and
  `L/k` a Galois extension (`[IsGalois k L]`, finite or infinite). If a character
  `ψ : characterLattice T_L` satisfies `galoisRepresentation k L T σ ψ = ψ` for every
  `σ : L ≃ₐ[k] L`, then `ψ = 0`.

The field `L` need not split `T`.

## Provenance

The module is derived; it combines two standard facts about tori. A. Borel, *Linear Algebraic
Groups*, 2nd ed. (1991), §8.14 (printed p. 120, PDF p. 131) calls a `k`-torus anisotropic when
`X(T)_k = X(T)^Γ` is trivial, with `Γ = Gal(k_s/k)`. §8.15 (printed pp. 120–121, PDF
pp. 131–132) constructs the largest split subtorus `T_d` of `T`. The result is the special case
needed in the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Theorem 10.3.1 (printed p. 392, PDF p. 423). There `G` is anisotropic, so a torus of `G` has no
nonzero Galois-fixed character. The Lean statement differs from Borel's in three ways:

- `L` is any Galois extension, not a separable closure.
- Anisotropy is assumed for the ambient group `G` (split rank zero), not for `T`.
- The conclusion is stated in the Library character lattice of `T_L`.

## Proof notes

- The instances `IsAffineHom` and `LocallyOfFiniteType` for `T` come from those of `G` through
  the closed immersion `i` (`Over.w`).
- `exists_largestSplitSubtorus` (module `Langlands.GroupScheme.Rational.TorusSplitPart`) gives a
  largest split subtorus `f : S ⟶ T`. Then `f ≫ i` is a split subtorus of `G`, so
  `IsAnisotropic.subsingleton_hom_of_isSplitSubtorus` makes the rational characters of `S`
  trivial.
- `ψ` is regarded as an actual rational character `ψ'` of the base change of `T` to `L`
  (`baseChangedCharacter`, module `Langlands.GroupScheme.Lie.RootOrbitCharacterDescent`).
  By `tensorConj_tensorValue_baseChangedCharacter` and `hfix`, its universal tensor value in
  `L ⊗[k] Coord T` is fixed by every `σ : L ≃ₐ[k] L`.
- `fixedDescend` (module `Langlands.GroupScheme.Rational.AffineCharacterTowerDescent`, which
  uses `InfiniteGalois.mem_range_algebraMap_iff_fixed`, so `L/k` may be infinite) descends `ψ'`
  to a character `χ` of the self-base change of `T` to `k`. Transporting `χ` along
  `GaloisPointComparison.selfBaseChangeIso` gives a character `χ₀` of `T`.
- `χ₀ = 0`: its restriction to `S` is zero because the characters of `S` are trivial, and
  `IsLargestSplitSubtorus.characterRestrict_injective` (module
  `Langlands.GroupScheme.Torus.SplitPartCharacters`; it uses `IsTorus T.toGrp`) shows that
  restriction to `S` is injective. Transporting back gives `χ = 0`.
- Finally `ψ' = 0` by `ext_valueE` over `L`-algebras, since `valueE_fixedDescend` says that
  `ψ'` and `χ = 0` have the same values. Lean accepts `ψ' = 0` as a proof of the goal `ψ = 0`
  by unfolding the definition of `baseChangedCharacter`.
