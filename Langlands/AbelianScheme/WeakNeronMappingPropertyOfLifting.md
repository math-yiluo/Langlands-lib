# The weak Néron mapping property from lifting over ramification index one

The module `Langlands.AbelianScheme.WeakNeronMappingPropertyOfLifting` proves the weak
Néron mapping property `Langlands.AbelianScheme.WeakNeronMappingProperty` for a separated
scheme `W` of finite type over a discrete valuation ring `R`. The hypothesis is a morphism
`h : W ⟶ X` to a proper `R`-scheme `X` which is an isomorphism on generic fibres and
through which points over extensions of ramification index one lift. This is the
situation of the smooth locus of a smoothening of a proper model (BLR §3.6, Lemma 5).

## Source and licence

Bosch, Lütkebohmert and Raynaud, *Néron Models* (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`). In §3.5, Proposition 3 with its proof
(printed pp. 74–75), BLR prove the weak Néron property of a weak Néron model that is
already given: a finite family of smooth separated models into which every `K^sh`-point
extends. They argue with the schematic closure of a graph. The weak Néron model of an
abelian variety itself comes from a smoothening of a proper model, by §1.3 (printed
pp. 16–17), §3.1, Corollary 4 (printed pp. 61–62), and the paragraph before §3.5,
Definition 1 (printed p. 74). This module proves the single-model weak Néron mapping
property under other hypotheses: a proper model `X`, and the lifting of §3.6, Lemma 5
(printed p. 79), for `h`. It uses that the local rings of a smooth `R`-scheme at the
generic points of its special fibre have ramification index one over `R` (§3.6,
Definition 1 and the remark after it, printed p. 78). Over such a local ring, the
valuative criterion of properness for `X` extends the generic-fibre morphism, and the
lifting hypothesis moves the extension to `W`.

The Lean proofs adapt three files of the Anthropic Lean formalization of Fermat's Last
Theorem, commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (literature ID
`anthropic-flt-complete-lean-source-6e837e75`):

- `P2M/Sol/S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.lean`,
- `P2M/Sol/S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth.lean`,
- `P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean`.

The ports of these files are in the Library under `Langlands.AnthropicFLT.P2M.Sol`. They
are licensed under the Apache License, Version 2.0, Copyright 2026 Anthropic, PBC; the
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` files are in `licenses/Anthropic-FLT/`. The Lean
file carries the modification notice.

Changes against the FLT files:

- The FLT lemmas extend morphisms into a proper `R`-scheme `X`. Here the target is a
  separated `R`-scheme `W` of finite type, and the hypotheses are a morphism `h : W ⟶ X`
  to a proper `X` that is an isomorphism on generic fibres, together with
  `RamificationIndexOneLifting`. The valuative criterion for `X` produces a point of `X`
  over the stalk of the test scheme; the lifting hypothesis moves it to `W`; and
  `eq_of_comp_eq` checks that the lift has the right generic point.
- The FLT local extension lemma needs a quasi-compact test scheme. Its adaptation
  `exists_nhds_extension_of_quasiCompact` keeps that hypothesis, and
  `exists_nhds_extension` removes it by restricting to an affine open neighbourhood.
- The gluing step of the FLT `exists_opens_extension` lemma becomes
  `weakNeronMappingProperty_of_lifting`, whose conclusion is the weak Néron mapping
  property.
- The step "a point lies in the domain of a rational map once the map extends over the
  stalk" is separated out of the FLT valuative-criterion lemma as
  `mem_domain_toRationalMap_of_lift`.

## Declarations

All declarations are in the namespace `Langlands.AbelianScheme.WeakNeronLifting`.

- `RamificationIndexOneLifting R f h` for `f : X ⟶ Spec R` and `h : W ⟶ X`: for every
  discrete valuation ring `R'` in the same universe with a local homomorphism `R → R'`
  satisfying `IsRamificationIndexOne R R'`, every `a : Spec R' ⟶ X` over `Spec R` (that
  is, `a ≫ f` is `Spec` of the algebra map) has the form `a' ≫ h`.
- `mem_domain_toRationalMap_of_lift`: on an integral scheme `X` over `S`, a point `x` lies
  in the domain of the rational map of a partial map `f : X ⇢ Y` (with `Y` locally of
  finite type over `S`) if some `l : Spec 𝒪_{X,x} ⟶ Y` over `S` restricts at the generic
  point to `f.fromFunctionField`.
- `mem_range_of_ne_closedPoint`: a point of `Spec R` other than the closed point is the
  image of the point of `Spec K`.
- `eq_of_comp_eq`: if `h ≫ f = w` and `h` is an isomorphism on generic fibres, two
  morphisms `α β : Z ⟶ W` with `α ≫ h = β ≫ h`, `α ≫ w = β ≫ w` and `α ≫ w` landing in
  the generic point of `Spec R` are equal. They factor through the generic fibre of `W`,
  where composition with the isomorphism `pullback.map … h …` is injective.
- `mem_opensRange_pullbackFst_of_ne_closedPoint`: a point of `T` not over the closed
  point lies in the image of the generic fibre `T ×_R Spec K ⟶ T`.
- `exists_nhds_extension_of_quasiCompact` and `exists_nhds_extension`: let `f : X ⟶ Spec R`
  be proper, `w : W ⟶ Spec R` locally of finite type and separated, `h ≫ f = w` with `h`
  an isomorphism on generic fibres and `RamificationIndexOneLifting R f h`. Let
  `t : T ⟶ Spec R` be smooth, `uK` a morphism of generic fibres from `T` to `W` over
  `Spec K`, and `η` a generic point of the closed fibre of `T`. Then there are an open
  `U ∋ η` of `T` and a morphism `U ⟶ W` over `Spec R` whose generic fibre is the
  restriction of `uK`. The first lemma assumes `t` quasi-compact.
- `weakNeronMappingProperty_of_lifting`: under the hypotheses on `f`, `w` and `h` above,
  `WeakNeronMappingProperty R K w` holds.

## Proofs as implemented

`exists_nhds_extension_of_quasiCompact`. The scheme `T` is noetherian and reduced (its
stalks are domains, by the Library's
`AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`),
and the stalk at `η` is a discrete valuation ring
(`AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes`). Let `ξ`
be the image of the generic point of `Spec 𝒪_{T,η}`; then `ξ` lies over the generic point
of `Spec R`, and the only irreducible component of `T` through `η` is the closure of `ξ`.
The open `U₀`, the complement of the other components, is irreducible and contains `η`
and `ξ`, so it is an integral scheme. Over the dense open `D` of points of `U₀` in the
generic fibre, `uK` defines a partial map `f₀ : U₀ ⇢ W`. Next:

1. The valuative criterion of existence for the proper `f` extends
   `f₀.fromFunctionField ≫ h` to `l₀ : Spec 𝒪_{U₀,η} ⟶ X` over `Spec R`.
2. By `SmoothDvrStalk.stalk_isRamificationIndexOne`, the stalk `𝒪_{U₀,η}` with
   `stalkStructureMap` is a discrete valuation ring of ramification index one over `R`.
   `RamificationIndexOneLifting` gives `l : Spec 𝒪_{U₀,η} ⟶ W` with `l ≫ h = l₀`, and `l`
   lies over `Spec R`.
3. The restriction of `l` to the function field agrees with `f₀.fromFunctionField` after
   composition with `h` and lies over the generic point of `Spec R`. So the two maps are
   equal by `eq_of_comp_eq`.
4. By `mem_domain_toRationalMap_of_lift`, `η` lies in the domain of the rational map of
   `f₀`. The partial map on that domain lies over `Spec R`, because it agrees with `f₀` on
   the dense open `D`. Its domain, viewed in `T`, is the required neighbourhood. Its
   generic fibre is the restriction of `uK`, which is checked on the two projections of
   the fibre product exactly as in the FLT file.

`exists_nhds_extension`. Choose an affine open `T₀ ∋ η`. The morphism `T₀ ⟶ Spec R` is
smooth and quasi-compact, and `η` is still a generic point of the closed fibre of `T₀`.
Apply the previous lemma to `T₀` and the restriction of `uK`, then transport the open
and the morphism along `T₀ ⟶ T` (`Scheme.Hom.isoImage`). The comparison of generic fibres
reduces to the identity `pullback.map` of the composite of the two open immersions.

`weakNeronMappingProperty_of_lifting`. The closed fibre of `T` is a quasi-sober space;
for each of its irreducible components `Z`, apply `exists_nhds_extension` at the generic
point of `Z`. Together with the morphism given by `uK` on the generic fibre of `T`, these
local morphisms are defined on the opens of a cover of their union `V`. Two of them agree
on each overlap: the overlap is smooth, hence flat, over `R`, `w` is separated, and both
morphisms have the same generic fibre. This is checked with the Library's
`NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated`. They therefore
glue (`Scheme.Opens.iSupOpenCover`, `glueMorphisms`) to `v : V ⟶ W` over `Spec R`. The
open `V` contains the generic fibre of `T` and the generic point of every component of
the closed fibre, and the generic fibre of `v` is the restriction of `uK`.
