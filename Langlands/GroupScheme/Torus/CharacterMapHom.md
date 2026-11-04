# Homomorphisms into split tori from additive maps of character lattices

Author: Worker 277.

This module works over `Spec k` for a commutative ring `k` that is an
integral domain. `T` is an arbitrary commutative group scheme over `Spec k`,
and `T'` is a split torus there (`IsSplitTorus T'.toGrp`). Characters are the
actual homomorphisms to `𝔾_m`, collected in `characterLattice`. No field,
finiteness, smoothness or isogeny hypothesis is used.

## Statements

- `IsSplitTorus.exists_hom_of_characterMap`: for every additive map
  `F : characterLattice T' →+ characterLattice T` there is a homomorphism
  `t : T ⟶ T'` with `t ≫ χ = F χ` for every character `χ` of `T'`.
- `IsSplitTorus.homOfCharacterMap`: a chosen such homomorphism.
- `IsSplitTorus.homOfCharacterMap_comp` (simp lemma): character pullback
  along `homOfCharacterMap F` is `F`.
- `IsSplitTorus.eq_homOfCharacterMap`: every homomorphism `t : T ⟶ T'` whose
  character pullback is `F` equals `homOfCharacterMap F`.
- `IsSplitTorus.existsUnique_hom_of_characterMap`: the homomorphism with
  character pullback `F` exists and is unique.

So, for a split torus `T'`, character pullback `t ↦ (χ ↦ t ≫ χ)` is a
bijection from `T ⟶ T'` onto the additive maps
`characterLattice T' →+ characterLattice T`. The module states existence,
uniqueness and the chosen inverse; it does not package this as an
equivalence or a functor.

## Proof

Choose a splitting `T' ≅ 𝔾_m^I` with `I` finite and turn it into an
isomorphism `eC` of commutative group schemes
(`CommGroupScheme.isoOfGroupIso`). Write `proj i` and `single i` for the
coordinate characters and cocharacters of `𝔾_m^I`. Let
`ψ i = eC.hom ≫ proj i` be the coordinate characters of `T'`.

Over a domain every endomorphism of `𝔾_m` is a power map:
`gmEndEquiv k : End(𝔾_m) ≃+ ℤ`, and `eq_gmEndEquiv_zsmul` writes each
endomorphism as `m • 𝟙`. For a character `χ` of `T'` let
`n χ i = gmEndEquiv k (single i ≫ eC.inv ≫ χ)`. Then
`single i ≫ eC.inv ≫ χ = n χ i • 𝟙`. The coordinate decomposition
`∑ i, proj i ≫ single i = 𝟙` (`splitTorus.sum_proj_comp_single`), inserted
between `eC.hom` and `eC.inv ≫ χ`, gives `χ = ∑ i, n χ i • ψ i`. The
composition is additive in each variable (`Preadditive`).

Define `t = (∑ i, F (ψ i) ≫ single i) ≫ eC.inv`. For every character `χ`,
`t ≫ χ = ∑ i, F (ψ i) ≫ (single i ≫ eC.inv ≫ χ) = ∑ i, n χ i • F (ψ i)`.
Additivity of `F` turns this into `F (∑ i, n χ i • ψ i) = F χ`.

Uniqueness is the published character separation for maps into split tori,
`IsSplitTorus.hom_ext_of_characters` (module `Torus/CharacterIsomorphism`).
The chosen homomorphism `homOfCharacterMap` uses `Classical.choose` of the
existence theorem.

## Provenance

This is a derived result. Its source is Milne, *Algebraic Groups* (2017),
Theorem 12.9(a), printed p.233 / PDF p.249. There `M ↦ D(M)` is a
contravariant equivalence from finitely generated commutative groups to
diagonalizable algebraic groups over a field, with quasi-inverse `G ↦ X(G)`.
Its full faithfulness gives `Hom(M, M') ≅ Hom(D(M'), D(M))`. Milne proves
this by reducing to cyclic groups, where `End(𝔾_m) ≅ ℤ`.

The Lean result covers the part of that full faithfulness needed here, and
under different hypotheses. The target `T'` must be split, so `T' ≅ D(ℤ^I)`.
The source `T` is any commutative group scheme over a domain, not
necessarily diagonalizable. The proof follows Milne's reduction to the
coordinates of `𝔾_m^I`, using `End(𝔾_m) ≅ ℤ` (`gmEndEquiv`, module
`Torus/Lattice`). In the split central Isogeny Theorem it builds the torus
map `t : T ⟶ T'` from the weight map of a root-datum morphism.
