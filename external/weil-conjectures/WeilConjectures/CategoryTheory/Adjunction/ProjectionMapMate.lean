/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Transport of the right adjoint projection map along a square of adjunctions

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions, with `F : D ⥤ C` and `F' : D' ⥤ C'`,
and let `N_D : D ⥤ D'`, `N_C : C ⥤ C'` be functors together with an isomorphism
`α : N_D ⋙ F' ≅ F ⋙ N_C`. The mate of `α` is the *base change map*
`β : G ⋙ N_D ⟶ N_C ⋙ G'`, that is `N_D (G M) ⟶ G' (N_C M)`.

Suppose that the four categories carry bifunctors `T_C, T_D, T_C', T_D'` (tensor products),
that `F` and `F'` carry comparisons `φ : F (a ⊗ b) ⟶ F a ⊗ F b` and `φ'`, and that `N_C` and
`N_D` carry isomorphisms `m : N (a ⊗ b) ≅ N a ⊗ N b` compatible with `φ`, `φ'` and `α`. We
show that `N_D` carries the right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` of
`CategoryTheory.Adjunction.rightAdjointProjectionMap` to the one of `adj'`, up to `m`, `α` and
`β`. In particular, if `β` is an isomorphism at `M` and at `M ⊗ F L`, then the projection map
of `adj'` at `(N_C M, N_D L)` is an isomorphism as soon as the projection map of `adj` at
`(M, L)` is.

We also give a criterion for `β` to be an isomorphism when `N_C` and `N_D` are themselves left
adjoints: the iterated mate of `α` is its conjugate, hence an isomorphism.

## Main results

- `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`: the comparison
  of the two projection maps.
- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv`: transport of the
  invertibility of the projection map.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso`: invertibility of the base change map.
- `CategoryTheory.Adjunction.isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc`: invertibility
  of a natural transformation `G ⋙ N_D ⟶ N_C ⋙ G'` with invertible mate, when `R ∘ N` decomposes
  as a finite biproduct of copies of the identity.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc`: invertibility of the
  base change map when `R ∘ N` only decomposes as a finite biproduct of copies of the identity.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor Limits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} (α : N_D ⋙ F' ≅ F ⋙ N_C)

section ProjectionMap

variable {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)
  (φ' : (postcompose₂.obj F').obj T_D' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj T_C')
  (m_C : (postcompose₂.obj N_C).obj T_C ≅ (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C')
  (m_D : (postcompose₂.obj N_D).obj T_D ≅ (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D')

/-- The compatibility of the comparisons `φ`, `φ'`, `m_C`, `m_D` with `α`: the two ways of
going from `N_C (F (a ⊗ b))` to `N_C (F a) ⊗ N_C (F b)` agree. -/
def ComparisonCompatible : Prop :=
  ∀ a b : D, N_C.map ((φ.app a).app b) ≫ (m_C.hom.app (F.obj a)).app (F.obj b) =
    α.inv.app ((T_D.obj a).obj b) ≫ F'.map ((m_D.hom.app a).app b) ≫
      (φ'.app (N_D.obj a)).app (N_D.obj b) ≫ (T_C'.map (α.hom.app a)).app _ ≫
        (T_C'.obj _).map (α.hom.app b)

variable {α φ φ' m_C m_D}

/-- The projection map of `adj` is carried by `N_D` to the projection map of `adj'`:
the square
```
N_D (G M ⊗ L) ──N_D(PF)──▶ N_D (G (M ⊗ F L)) ──β──▶ G' (N_C (M ⊗ F L))
     │                                                    │
     m_D                                     G'(m_C ≫ 1 ⊗ α⁻¹)
     ▼                                                    ▼
N_D (G M) ⊗ N_D L ──β ⊗ 1──▶ G' (N_C M) ⊗ N_D L ──PF'──▶ G' (N_C M ⊗ F' (N_D L))
```
commutes, where `β` is the mate of `α`. -/
lemma map_rightAdjointProjectionMap_comp_mateEquiv
    (H : ComparisonCompatible α φ φ' m_C m_D) (M : C) (L : D) :
    N_D.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫
        (mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)) ≫
        G'.map ((m_C.hom.app M).app (F.obj L) ≫ (T_C'.obj (N_C.obj M)).map (α.inv.app L)) =
      (m_D.hom.app (G.obj M)).app L ≫ (T_D'.map ((mateEquiv adj adj' α.hom).app M)).app _ ≫
        ((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app (N_D.obj L) := by
  apply (adj'.homEquiv _ _).symm.injective
  have hβ (X : C) : F'.map ((mateEquiv adj adj' α.hom).app X) ≫ adj'.counit.app (N_C.obj X) =
      α.hom.app (G.obj X) ≫ N_C.map (adj.counit.app X) :=
    mateEquiv_counit adj adj' α.hom X
  have hα := α.hom.naturality (((adj.rightAdjointProjectionMap φ).app M).app L)
  have hm := NatTrans.congr_app (m_C.hom.naturality (adj.counit.app M)) (F.obj L)
  have hφ' := NatTrans.congr_app (φ'.naturality ((mateEquiv adj adj' α.hom).app M))
    (N_D.obj L)
  dsimp at hα hm hφ'
  rw [homEquiv_counit, homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, counit_naturality, counit_naturality_assoc]
  erw [adj'.map_rightAdjointProjectionMap_app_app_comp_counit φ' (N_C.obj M) (N_D.obj L)]
  rw [reassoc_of% hφ', ← NatTrans.comp_app, ← T_C'.map_comp, hβ]
  dsimp
  rw [reassoc_of% (hβ _), reassoc_of% hα, ← N_C.map_comp_assoc]
  erw [adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L]
  rw [N_C.map_comp, Category.assoc, reassoc_of% hm, reassoc_of% (H (G.obj M) L)]
  simp [← NatTrans.comp_app_assoc, ← Functor.map_comp]
  simp

/-- If the base change map `β` (the mate of `α`) is an isomorphism at `M` and at `M ⊗ F L`,
and the projection map of `adj` is an isomorphism at `(M, L)`, then the projection map of
`adj'` is an isomorphism at `(N_C M, N_D L)`. -/
lemma isIso_rightAdjointProjectionMap_of_mateEquiv
    (H : ComparisonCompatible α φ φ' m_C m_D) (M : C) (L : D)
    [IsIso (((adj.rightAdjointProjectionMap φ).app M).app L)]
    [IsIso ((mateEquiv adj adj' α.hom).app M)]
    [IsIso ((mateEquiv adj adj' α.hom).app ((T_C.obj M).obj (F.obj L)))] :
    IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj M)).app (N_D.obj L)) := by
  have h := adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' H M L
  rw [← IsIso.inv_comp_eq, ← IsIso.inv_comp_eq] at h
  rw [← h]
  infer_instance

end ProjectionMap

section BaseChange

variable {R_D : D' ⥤ D} {R_C : C' ⥤ C} (adj_D : N_D ⊣ R_D) (adj_C : N_C ⊣ R_C)

/-- The base change map `β : N_D (G M) ⟶ G' (N_C M)`, the mate of an isomorphism
`α : N_D ⋙ F' ≅ F ⋙ N_C`, is an isomorphism at `M` if `N_C` and `N_D` are left adjoints,
the units of `N_C ⊣ R_C` at `M` and of `N_D ⊣ R_D` at `G M` are isomorphisms, and the counit of
`N_D ⊣ R_D` at `G' (N_C M)` is an isomorphism. Indeed `R_D β` is then, up to these units, the
iterated mate of `α`, which is its conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`),
an isomorphism. -/
lemma isIso_mateEquiv_app_of_isIso (M : C) [IsIso (adj_C.unit.app M)]
    [IsIso (adj_D.unit.app (G.obj M))] [IsIso (adj_D.counit.app (G'.obj (N_C.obj M)))] :
    IsIso ((mateEquiv adj adj' α.hom).app M) := by
  have hconj : IsIso (conjugateEquiv (adj.comp adj_C) (adj_D.comp adj') α.hom) :=
    inferInstance
  have hit := iterated_mateEquiv_conjugateEquiv adj adj' adj_D adj_C α.hom
  have hu := unit_mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom) M
  rw [← hit] at hconj
  have : IsIso ((mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom)).app (N_C.obj M)) :=
    NatIso.isIso_app_of_isIso
      (mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom)) _
  have : IsIso (R_D.map ((mateEquiv adj adj' α.hom).app M)) := by
    have : IsIso (adj_D.unit.app (G.obj M) ≫ R_D.map ((mateEquiv adj adj' α.hom).app M)) := by
      dsimp at hu
      rw [← hu]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj_D.unit.app (G.obj M)) _
  have hsrc : IsIso (adj_D.counit.app (N_D.obj (G.obj M))) := by
    have e := adj_D.left_triangle_components (G.obj M)
    rw [← IsIso.inv_eq_of_hom_inv_id e]
    infer_instance
  have h := adj_D.counit.naturality ((mateEquiv adj adj' α.hom).app M)
  dsimp at h
  have : IsIso (adj_D.counit.app (N_D.obj (G.obj M)) ≫ (mateEquiv adj adj' α.hom).app M) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj_D.counit.app (N_D.obj (G.obj M))) _

/-- The mate along `N_C ⊣ R_C` and `N_D ⊣ R_D` of the base change map, the map
`G (R_C M') ⟶ R_D (G' M')`, is an isomorphism: it is the conjugate of `α`. -/
lemma isIso_mateEquiv_mateEquiv :
    IsIso (mateEquiv adj_C adj_D (mateEquiv adj adj' α.hom)) := by
  have hconj : IsIso (conjugateEquiv (adj.comp adj_C) (adj_D.comp adj') α.hom) :=
    inferInstance
  rwa [← iterated_mateEquiv_conjugateEquiv adj adj' adj_D adj_C α.hom] at hconj

variable [Preadditive C] [Preadditive D] [HasFiniteBiproducts C]
  [G.Additive] [R_D.ReflectsIsomorphisms]

/-- A natural transformation `β : G ⋙ N_D ⟶ N_C ⋙ G'` whose mate `R_C ⋙ G ⟶ G' ⋙ R_D` along
`N_C ⊣ R_C` and `N_D ⊣ R_D` is an isomorphism is itself an isomorphism at `M` in the following
situation: `R_D` is conservative, and there are finitely many endomorphisms `e i` of `N_C M` and
`e' i` of `N_D (G M)` compatible with `β`, such that the maps `M ⟶ R_C (N_C M)` and
`G M ⟶ R_D (N_D (G M))` obtained by composing the units with `R_C (e i)` and `R_D (e' i)` exhibit
the targets as biproducts of copies of `M` and of `G M`. Indeed, on each summand, `R_D β` is then
the mate of `β`. -/
lemma isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc (β : TwoSquare G N_C N_D G')
    [IsIso (mateEquiv adj_C adj_D β)] {ι : Type} [Finite ι] (M : C)
    (e : ι → (N_C.obj M ⟶ N_C.obj M)) (e' : ι → (N_D.obj (G.obj M) ⟶ N_D.obj (G.obj M)))
    (he : ∀ i, e' i ≫ β.app M = β.app M ≫ G'.map (e i))
    [IsIso (biproduct.desc fun i ↦ adj_C.unit.app M ≫ R_C.map (e i))]
    [IsIso (biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i))] :
    IsIso (β.app M) := by
  set β' := mateEquiv adj_C adj_D β
  have hu := unit_mateEquiv adj_C adj_D β M
  dsimp at hu
  -- the comparison `⨁ G M ⟶ G (⨁ M)` is invertible, `G` being additive
  have hc : IsIso (biproduct.desc fun i ↦ G.map (biproduct.ι (fun _ : ι ↦ M) i)) := by
    have h : (biproduct.desc fun i ↦ G.map (biproduct.ι (fun _ : ι ↦ M) i)) =
        (G.mapBiproduct fun _ : ι ↦ M).inv := by
      ext i
      simp [Functor.mapBiproduct]
    rw [h]
    infer_instance
  have key : (biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i)) ≫
      R_D.map (β.app M) =
      (biproduct.desc fun i ↦ G.map (biproduct.ι (fun _ : ι ↦ M) i)) ≫
        G.map (biproduct.desc fun i ↦ adj_C.unit.app M ≫ R_C.map (e i)) ≫
          β'.app (N_C.obj M) := by
    ext i
    simp only [biproduct.ι_desc_assoc, Category.assoc, ← G.map_comp_assoc, biproduct.ι_desc]
    rw [← R_D.map_comp, he, R_D.map_comp, ← reassoc_of% hu, G.map_comp, Category.assoc]
    congr 1
    exact (β'.naturality (e i)).symm
  have : IsIso (R_D.map (β.app M)) := by
    have : IsIso ((biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i)) ≫
        R_D.map (β.app M)) := by
      have : IsIso (β'.app (N_C.obj M)) := NatIso.isIso_app_of_isIso (β' : NatTrans _ _) _
      rw [key]
      have h2 : IsIso (G.map (biproduct.desc fun i ↦ adj_C.unit.app M ≫ R_C.map (e i))) :=
        Functor.map_isIso _ _
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)
    exact IsIso.of_isIso_comp_left
      (biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i)) _
  exact isIso_of_reflects_iso _ R_D

/-- The base change map `β : N_D (G M) ⟶ G' (N_C M)`, the mate of an isomorphism
`α : N_D ⋙ F' ≅ F ⋙ N_C`, is an isomorphism at `M` in the following situation: `N_C ⊣ R_C` and
`N_D ⊣ R_D` are adjunctions with `R_D` conservative, and there are finitely many endomorphisms
`e i` of `N_C M` and `e' i` of `N_D (G M)` compatible with `β`, such that the maps
`M ⟶ R_C (N_C M)` and `G M ⟶ R_D (N_D (G M))` obtained by composing the units with `R_C (e i)`
and `R_D (e' i)` exhibit the targets as biproducts of copies of `M` and of `G M`.

This applies to extension of scalars `N` along a finite free ring map, with right adjoint the
restriction of scalars `R`, and to the multiplications `e i` by the elements of a basis: on each
summand, `R_D β` is then the iterated mate of `α`, which is invertible
(`CategoryTheory.Adjunction.isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc`). -/
lemma isIso_mateEquiv_app_of_isIso_biproductDesc {ι : Type} [Finite ι] (M : C)
    (e : ι → (N_C.obj M ⟶ N_C.obj M)) (e' : ι → (N_D.obj (G.obj M) ⟶ N_D.obj (G.obj M)))
    (he : ∀ i, e' i ≫ (mateEquiv adj adj' α.hom).app M =
      (mateEquiv adj adj' α.hom).app M ≫ G'.map (e i))
    [IsIso (biproduct.desc fun i ↦ adj_C.unit.app M ≫ R_C.map (e i))]
    [IsIso (biproduct.desc fun i ↦ adj_D.unit.app (G.obj M) ≫ R_D.map (e' i))] :
    IsIso ((mateEquiv adj adj' α.hom).app M) := by
  have := isIso_mateEquiv_mateEquiv adj adj' α adj_D adj_C
  exact isIso_app_of_isIso_mateEquiv_of_isIso_biproductDesc adj_D adj_C _ M e e' he

end BaseChange

end CategoryTheory.Adjunction
