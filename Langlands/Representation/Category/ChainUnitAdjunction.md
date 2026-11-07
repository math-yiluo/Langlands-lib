# Second adjointness from the unit of the chain (VI.9.6.3)

Module `Langlands.Representation.Category.ChainUnitAdjunction`, namespace
`Langlands.SmoothRep`.

## Source and purpose

Renard 2026, VI.9.6 (printed p.202, PDF p.208), deduces second adjointness (VI.9.6.1)
from the chain (VI.9.6.3)

`Hom_G(V, (i τ)~) ≃ Hom_G(V, i(τ~)) ≃ Hom_M(r V, τ~) ≃ Hom_M(τ, (r V)~) ≃ Hom_M(τ, r̄(V~))`.

The module `FrobeniusChainAdjunction` packages this chain as an adjunction
`A' : L ⋙ D.rightOp ⊣ D ⋙ R`, and `PairingAdjunction` turns `A'` into `L ⊣ R` under a
naturality condition `hN2` on its counit. This module gives a second route to `L ⊣ R`,
from the unit of `A'`. Its condition is checked one `τ` at a time: the unit of `A'` at `τ`,
a morphism `τ ⟶ R((L τ)~~)`, factors through `R` of bidual evaluation
`L τ ⟶ (L τ)~~`. Renard's text does not state this condition. It is internal to this
formalization. Nothing in this module constructs `F`, `C` or `Ψ`, or proves (VI.9.6.1)
for parabolic induction.

## Setting

`G` and `M` are groups with topologies, `G` a topological group; `M` is a topological group
in the section on Frobenius reciprocity. `L : M(M) ⥤ M(G)` and `R : M(G) ⥤ M(M)` are
arbitrary functors between categories of smooth complex representations (coefficient
universe `0`). `D` is the smooth contragredient functor `contragredientFunctor`,
`bidualHom V : V ⟶ V~~` is bidual evaluation, and `contragredientHom f` is the transpose
of `f`. `contragredientAdjunction` is Lemma I.4.2.1, `D.rightOp ⊣ D`. The hypotheses
used are:

- `hG : CompactOpenCofinal G`: compact open subgroups of `G` form a neighborhood basis of
  the identity;
- `hR : PreservesShortExact R`: `R` preserves short exact sequences.

No exactness of `L` is assumed.

## Declarations

Section `UnitForm`, for a natural transformation `η : 𝟭 ⟶ L ⋙ R`:

- `unitHom_bijective hG hR η hbij τ π`: if `g ↦ η_τ ≫ R g` is bijective on morphisms
  `L τ ⟶ V~` into every smooth contragredient (`hbij`), then it is bijective on morphisms
  `L τ ⟶ π` into every smooth `π`.
- `adjunctionOfDualUnit hG hR η hbij : L ⊣ R`, built with `Adjunction.mkOfHomEquiv` from
  the bijections of `unitHom_bijective`. `adjunctionOfDualUnit_unit_app` states that its
  unit at `τ` is `η_τ`.

Section `ChainUnit`, for an adjunction `A' : L ⋙ D.rightOp ⊣ D ⋙ R`:

- `comp_map_contragredientAdjunction_homEquiv A' η₀ hη₀ V t`: if
  `η₀ ≫ R (bidualHom (L τ)) = A'.unit.app τ` (`hη₀`), then for `t : (L τ)~ ⟶ V` in
  `M(G)ᵒᵖ`, `η₀ ≫ R g = A'.homEquiv τ (op V) t`, where `g : L τ ⟶ V~` is the image of `t`
  under `contragredientAdjunction.homEquiv`.
- `comp_map_bijective_of_unit A' η₀ hη₀ V`: under `hη₀`, `g ↦ η₀ ≫ R g` is bijective on
  morphisms `L τ ⟶ V~`.
- `unitLift_naturality hG hR A' η₀ hη₀ h`: a family `η₀ τ` satisfying `hη₀` at every `τ` is
  natural: `h ≫ η₀ τ' = η₀ τ ≫ R (L h)` for `h : τ ⟶ τ'`.
- `adjunctionOfChainUnit hG hR A' η₀ hη₀ : L ⊣ R`, which is `adjunctionOfDualUnit` for this
  natural family. `adjunctionOfChainUnit_unit_app` states that its unit at `τ` is `η₀ τ`.
- `nonempty_adjunction_of_chainUnit hG hR A' hU : Nonempty (L ⊣ R)`, where `hU` says: for
  every `τ` there is `η₀ : τ ⟶ R(L τ)` with `η₀ ≫ R (bidualHom (L τ)) = A'.unit.app τ`.

Section `Frobenius`, for `r : M(G) ⥤ M(M)`, `F : r ⊣ L`, `C : L.op ⋙ D_G ≅ D_M ⋙ L` and
`Ψ : D_G ⋙ R ≅ r.op ⋙ D_M`:

- `unit_frobeniusChainAdjunction F C Ψ τ`: the unit at `τ` of
  `frobeniusChainAdjunction F C Ψ` is the composite
  `bidualHom τ ≫ contragredientHom (F.counit.app τ~) ≫ contragredientHom (r (C.hom.app (op τ))) ≫ Ψ.inv.app (op (L τ)~)`,
  that is, `τ ⟶ τ~~ ⟶ (r(L(τ~)))~ ⟶ (r((L τ)~))~ ⟶ R((L τ)~~)`.
- `nonempty_adjunction_of_frobeniusChain_unit hG hR F C Ψ hU : Nonempty (L ⊣ R)`, where `hU`
  says: for every `τ` there is `η₀ : τ ⟶ R(L τ)` such that `η₀ ≫ R (bidualHom (L τ))` is
  the composite above.

## Proofs

`unitHom_bijective`. Injectivity: if `η_τ ≫ R g₁ = η_τ ≫ R g₂`, compose with
`R (bidualHom π)`. By `hbij` at `π~`, `g₁ ≫ bidualHom π = g₂ ≫ bidualHom π`. Bidual
evaluation is a monomorphism (`mono_bidualHom hG π`), so `g₁ = g₂`. Surjectivity: given
`k : τ ⟶ R π`, `hbij` at `π~` gives `h : L τ ⟶ π~~` with
`η_τ ≫ R h = k ≫ R (bidualHom π)`. Let `q = bidualCopresentationMap π` be the map
`π~~ ⟶ (coker(bidualHom π))~~`. By `hbij` at that contragredient, `h ≫ q = 0`, because
`η_τ ≫ R (h ≫ q) = k ≫ R (bidualHom π ≫ q) = 0`. The kernel fork
`bidualCopresentationIsLimit hG π` exhibits `bidualHom π` as a kernel of `q`, so `h` lifts
to `l : L τ ⟶ π`. Then `η_τ ≫ R l = k`, after cancelling `R (bidualHom π)`, which is a
monomorphism because `R` preserves injectivity (from `hR`) and `bidualHom π` is injective.

`adjunctionOfDualUnit`. The hom bijection is `Equiv.ofBijective` of the maps of
`unitHom_bijective`. Naturality on the left uses the naturality of `η`. Naturality on
the right is `R.map_comp`. The unit at `τ` is `η_τ ≫ R (𝟙 (L τ)) = η_τ`.

`comp_map_contragredientAdjunction_homEquiv`. Both hom bijections are written with their
units (`Adjunction.homEquiv_unit`); `hη₀` replaces the unit of `A'`, and the two sides
agree by `Functor.map_comp` and associativity.

`comp_map_bijective_of_unit`. By the previous lemma, `g ↦ η₀ ≫ R g` is the composite of
the inverse of `contragredientAdjunction.homEquiv` with `A'.homEquiv`, hence bijective.

`unitLift_naturality`. Cancel the monomorphism `R (bidualHom (L τ'))`. Both sides become
units of `A'` by `hη₀` and naturality of bidual evaluation (`bidualHom_naturality`), and
the claim is the naturality of the unit of `A'`.

`unit_frobeniusChainAdjunction`. Unfold `frobeniusChainAdjunction`,
`Adjunction.ofNatIsoRight`, `Adjunction.ofNatIsoLeft` and `Adjunction.comp_unit_app`. The
remaining identification is definitional.

`nonempty_adjunction_of_frobeniusChain_unit` is `nonempty_adjunction_of_chainUnit` for
`A' = frobeniusChainAdjunction F C Ψ`, with `hU` rewritten by
`unit_frobeniusChainAdjunction`.

## Use for VI.9.6

For second adjointness, with `P = M ⋉ U` and an opposite closed subgroup `O` of `G`, `L` is
normalized induction `i` from `M`, `r` the Jacquet functor along `U` and `R = r̄` the
Jacquet functor along `O`. `F` is Frobenius
reciprocity, `C` the duality `(i τ)~ ≅ i(τ~)` and `Ψ` the isomorphism (VI.9.6.2). The
condition `hU` asks that, for every `τ`, the unit of the chain `τ ⟶ r̄((i τ)~~)` takes
values in `r̄` of `i τ`. `nonempty_secondAdjunction_of_stableLift`
(`Aubert/General/SecondAdjointnessCell.lean`) applies
`nonempty_adjunction_of_frobeniusChain_unit` and proves `hU` there.
