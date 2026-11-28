# Gluing data along open subspaces, in relation form

This module defines the gluing data used by the gluing theorem `exists_glued`
(module `LocalizedOpenRelationGluing`) and proves the elementary facts about it.
All declarations are in `Langlands.Analytic.SaturatedAtlasPresentation`, the
analytic spaces are objects of `LocalizedCategory.{u, u, u}` over a complete
ultrametric normed field `K : Type u` (the valuation may be trivial).

## Definition

`LocalizedOpenRelation K` consists of

- an index type `M : Type u` and analytic spaces `Z m` (the pieces);
- for all `m n` an analytic space `S m n` with morphisms `a m n : S m n ⟶ Z m` and
  `b m n : S m n ⟶ Z n`, both open immersions (`openImmersion`);
- `refl`: a morphism `s : Z m ⟶ S m m` with `s ≫ a m m = 𝟙` and `s ≫ b m m = 𝟙`;
- `symm`: a morphism `s : S m n ⟶ S n m` exchanging the two projections;
- `trans`: for every test space `T` and maps `s : T ⟶ S m n`, `t : T ⟶ S n l` with
  `s ≫ b m n = t ≫ a n l`, a map `r : T ⟶ S m l` with `r ≫ a m l = s ≫ a m n` and
  `r ≫ b m l = t ≫ b n l`.

Since `a m n` is a monomorphism, `S m n` is determined as a subobject of `Z m`;
the data amount to open subspaces `a m n (S m n)` of `Z m` with isomorphisms
`b m n ∘ (a m n)⁻¹` onto open subspaces of `Z n`, and the three conditions are the
identity, inverse and cocycle conditions of gluing.

## Results

- `openImmersion.mono'` and `openImmersion.exists_lift`: an open immersion is a
  monomorphism, and a morphism whose points lie in the image of an open immersion
  factors through it (through `domainLift` and the isomorphism of the immersion).
- `a_self_eq_b_self`: `a m m = b m m`; `a m m` has the section of `refl` as inverse.
- `Rel f g` for `f : T ⟶ Z m`, `g : T ⟶ Z n`: some `s : T ⟶ S m n` has
  `s ≫ a = f` and `s ≫ b = g`. It is reflexive, symmetric and transitive
  (`Rel.refl`, `Rel.symm`, `Rel.trans`), stable under precomposition (`Rel.comp`),
  and functional (`Rel.unique`, `Rel.unique_left`: `a` and `b` are monomorphisms).
  On one piece it is equality (`rel_self_iff`).
- `domainSet m n`, the image of `a m n`, is open (`isOpen_domainSet`); a related
  morphism lands in it (`Rel.mem_domainSet`).
- `transfer n f hf`: for `f : T ⟶ Z m` with points in `domainSet m n`, the morphism
  `s ≫ b m n` for the lift `s` of `f` through `a m n`; `rel_transfer` and
  `Rel.eq_transfer` say that it is the unique morphism related to `f`.
- `PointRel` is the relation on the points of the pieces given by the points of
  `S m n`; `pointSetoid` is the resulting equivalence relation. Transitivity
  (`pointRel_trans`) applies `trans` to the open subspace of `S m n` on which `b m n`
  lands in the image of `a n l`, with the lift of that restriction through `a n l`.

## Provenance

Derived. The data are Berkovich's gluing data of analytic spaces along open
analytic domains, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, §1.3, printed p.24 / PDF p.21:
domains `Xᵢⱼ ⊂ Xᵢ` and isomorphisms `νᵢⱼ : Xᵢⱼ → Xⱼᵢ` with `Xᵢᵢ = Xᵢ`,
`νᵢⱼ(Xᵢⱼ ∩ Xᵢₖ) = Xⱼᵢ ∩ Xⱼₖ` and `νᵢₖ = νⱼₖ ∘ νᵢⱼ`, here in case a) of
Proposition 1.3.3 (all `Xᵢⱼ` open). The relation form, with `Xᵢⱼ` the image of
`a i j` and `νᵢⱼ = b i j ∘ (a i j)⁻¹`, and the conditions stated on morphisms from
arbitrary test spaces, is an implementation choice.
