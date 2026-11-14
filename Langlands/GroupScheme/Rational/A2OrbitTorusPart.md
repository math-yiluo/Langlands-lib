# Torus parts of rational opposite products over a splitting field

Author: Worker 4348.

Module `Langlands.GroupScheme.Rational.A2OrbitTorusPart`.

## Results

- `mem_normalizerPoints_groupHom_comp e j hn` (namespace `Langlands.GroupScheme`): let `e` be
  an isomorphism of commutative group schemes. A point normalizing `j` also normalizes
  `groupHom e.hom ≫ j`. If `σ` normalizes for `j`, then `e ≪≫ σ ≪≫ e.symm` normalizes for the
  composite.
- `rationalExtend_injective'` (namespace `GaloisCompatiblePinningData`): scalar extension of
  rational points is injective. This uses `GaloisPoint.extend_injective` and
  `baseChangeCoeffEquiv_rationalExtend`.
- `exists_rationalTorusPart … hic hjc hS ha0 hline hcent F xm w hXq hYp hXK hX₀K hX hX1 hX₀
  hX₀1 hAB hAB₀`.

## The main theorem

Setting:
- `D : GaloisCompatiblePinningData k K G`, with `G` locally of finite type;
- `t : S ⟶ D.torus`;
- the composite `groupHom t ≫ D.inclusion` and `D.inclusion` are closed subgroups (`hic`,
  `hjc`);
- `S` is split and `a ≠ 0`;
- `hline : RestrictsToMultipliableLine (restrictMap t) p.rootDatum a_K`;
- `D.inclusion` represents the centralizer of the composite (`hcent`).

Let `F` be any piece family over `a_K`, `xm l` root parametrizations of the merged roots
`F.lm l`, and `w l` units of `K`. Let `X, X₀ ∈ G(k)` satisfy:

- `rationalExtend X = F.tripleProd Xq (fun l => xm l (w l)) Yp`, with `Xq l ∈ U_{q_l}` and
  `Yp l ∈ U_{p_l}`;
- `rationalExtend X₀ = F.tripleProd 1 (fun l => xm l 1) 1`;
- `X` and `X₀` are nontrivial points of the relative root group of `a`;
- `(A, B)` and `(A₀, B₀)` are opposite factor pairs of `X` and `X₀` over `k`
  (`RelativeRoot.IsOppositeFactorPair` for the composite and `a`).

Then there is a point `x` of the pinned torus with

```text
rationalExtend (A X B (A₀ X₀ B₀)⁻¹) = p.inclusion(x),
```

and for every character `ω` with `⟨ω, q_l^∨⟩ = 0` for all `l`,
`charEval ω x = ∏ₗ (w l)^⟨ω, p_l^∨⟩`.

## Proof

1. Scalar extension carries `X`, `X₀` into the base-changed relative root group of `a`, and
   `A, B, A₀, B₀` into that of `-a`. This uses `rationalExtend_mem_rootGroupPoints`. The
   composite `groupHom (restrictMap t) ≫ p.inclusion` is the base change of
   `groupHom t ≫ D.inclusion` (`groupHom_restrictMap_comp_inclusion`).
2. The opposite products `A X B` and `A₀ X₀ B₀` normalize the composite. Scalar extension
   keeps this (`normalizerPointsFieldExtend`). They also normalize `D.inclusion`
   (`mem_normalizerPoints_of_torusCentralizer`), hence its base change. Since
   `p.inclusion = groupHom D.torusIso.hom ≫ (base change of D.inclusion)` (`D.inclusion_eq`),
   `mem_normalizerPoints_groupHom_comp` shows they normalize `p.inclusion`.
3. Nontriviality survives scalar extension, by `rationalExtend_injective'`.
4. The monomorphism instances come from the closed-subgroup hypotheses and
   `IsClosedSubgroup.baseChange`.
5. Apply `exists_oppositeProducts_torusPart` (module `Rational.PieceTorusCharacter`) to the
   scalar extensions. Scalar extension is multiplicative, so
   `rationalExtend (A X B (A₀ X₀ B₀)⁻¹)` is the corresponding ratio over `K`.

## Provenance

This is internal glue between the `K`-level computation of `Rational.PieceTorusCharacter` and
`k`-rational opposite pairs. It makes no new mathematical assertion.

The affine-morphism version `rationalExtend_injective'` reuses `Langlands.Geometry.Building.rationalExtend_injective_of_isAffine` after inferring the affineness of the total space.
