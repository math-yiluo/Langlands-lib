/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Coherence
public import WeilConjectures.CategoryTheory.ExchangeFormalism.CompositionCoherence
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!

# The compact-support exchange map as a mate of composition isomorphisms

Let `F` be a `CategoryTheory.ExchangeFormalism`, and consider factorizations
`X ⟶[i] Z ⟶[p] Y` and `X' ⟶[i'] Z' ⟶[p'] Y'` lying over each other along `g' : X' ⟶ X`,
`h : Z' ⟶ Z` and `g : Y' ⟶ Y`. The mate of the compact-support exchange map
`F.shriekBaseChange : (p_* i_!) ⋙ g^* ⟶ g'^* ⋙ (p'_* i'_!)` under `g'^* ⊣ g'_*` and
`g^* ⊣ g_*` is the pasting of the exchange map `g'_* ⋙ i_! ⟶ i'_! ⋙ h_*` of the upper square
with the composition square `h_* ⋙ p_* ≅ (h ≫ p)_* = (p' ≫ g)_* ≅ p'_* ⋙ g_*`
(`CategoryTheory.ExchangeFormalism.mateEquiv_shriekBaseChange`). Equivalently, it is the
composite of the composition isomorphisms of the triangles of factorizations
`(X' ⟶[𝟙] X' ⟶[g'] X, X ⟶[i] Z ⟶[p] Y)` and `(X' ⟶[i'] Z' ⟶[p'] Y', Y' ⟶[𝟙] Y' ⟶[g] Y)` of
`g' ≫ (p ∘ i)` and `(p' ∘ i') ≫ g`
(`CategoryTheory.ExchangeFormalism.mateEquiv_shriekBaseChange_eq_compIso`).

-/

@[expose] public section

universe w v₁ v u

open CategoryTheory

open scoped CategoryTheory.TwoSquare

namespace CategoryTheory

section OfNatIsoRight

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- Whiskering the sides `G` and `H` of a 2-square `G ⋙ L₂ ⟶ L₁ ⋙ H` corresponds to whiskering
the sides of its mate `R₁ ⋙ G ⟶ H ⋙ R₂`, as an equation of natural transformations. -/
lemma mateEquiv_mk_whiskerRight_comp_comp_whiskerLeft (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G' : C ⥤ E} {H' : D ⥤ F} (σ : G' ⟶ G) (α : TwoSquare G L₁ L₂ H) (τ : H ⟶ H') :
    (mateEquiv adj₁ adj₂ (TwoSquare.mk G' L₁ L₂ H' (Functor.whiskerRight σ L₂ ≫ α ≫
      Functor.whiskerLeft L₁ τ))) =
      Functor.whiskerLeft R₁ σ ≫ (mateEquiv adj₁ adj₂ α) ≫ Functor.whiskerRight τ R₂ := by
  have h := (mateEquiv_whiskerTop_whiskerBottom adj₁ adj₂ α σ τ)
  simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight] using h
end OfNatIsoRight

section Conjugation

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞] [Category* 𝒟]
  {G₁ G₁' G₁'' : 𝒜 ⥤ ℬ} {F₁ F₁' : ℬ ⥤ 𝒞} {F₂ F₂' : 𝒜 ⥤ 𝒟} {G₂ G₂' G₂'' : 𝒟 ⥤ 𝒞} {H : 𝒜 ⥤ 𝒞}

/-- Conjugating a composite of 2-cells `M₁ ≫ M₂ : G₁' ⋙ F₁' ⟶ F₂' ⋙ G₂'` by isomorphisms
`a : G₁ ≅ G₁'`, `d = e⁻¹ : G₂' ⟶ G₂` (for `e : G₂ ≅ G₂'`) and morphisms `b : F₁ ⟶ F₁'`,
`c : F₂' ⟶ F₂` is the same as first replacing `G₁'` and `G₂'` by `G₁''` and `G₂''` along
isomorphisms `p : G₁' ≅ G₁''` and `q : G₂' ≅ G₂''`. -/
lemma hcomp_comp_comp_hcomp_eq (a : G₁ ≅ G₁') (p : G₁' ≅ G₁'') (b : F₁ ⟶ F₁')
    (M₁ : G₁' ⋙ F₁' ⟶ H) (M₂ : H ⟶ F₂' ⋙ G₂') (c : F₂' ⟶ F₂) (e : G₂ ≅ G₂') (q : G₂' ≅ G₂'')
    (d : G₂' ⟶ G₂) (hd : e.inv = d) :
    NatTrans.hcomp a.hom b ≫ M₁ ≫ M₂ ≫ NatTrans.hcomp c d =
      Functor.whiskerRight (a ≪≫ p).symm.inv F₁ ≫
        (Functor.whiskerLeft G₁'' b ≫
          (Functor.whiskerRight p.inv F₁' ≫ M₁ ≫ M₂ ≫ Functor.whiskerLeft F₂' q.hom) ≫
          Functor.whiskerRight c G₂'') ≫
        Functor.whiskerLeft F₂ (e ≪≫ q).inv := by
  subst hd
  ext K
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  have h₁ : F₁.map (p.hom.app K) ≫ b.app (G₁''.obj K) ≫ F₁'.map (p.inv.app K) =
      b.app (G₁'.obj K) := by
    rw [b.naturality_assoc, ← F₁'.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.comp_id]
  have h₂ : q.hom.app (F₂'.obj K) ≫ G₂''.map (c.app K) ≫ q.inv.app (F₂.obj K) ≫
      e.inv.app (F₂.obj K) = e.inv.app (F₂'.obj K) ≫ G₂.map (c.app K) := by
    rw [q.inv.naturality_assoc, Iso.hom_inv_id_app_assoc]
    exact e.inv.naturality (c.app K)
  rw [reassoc_of% h₁, h₂, ← b.naturality_assoc]

end Conjugation

namespace ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Mate

variable {X Y Z X' Y' Z' : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y) (i' : X' ⟶ Z') (p' : Z' ⟶ Y')
  [Fact (𝒪 i)] [Fact (𝒪 i')] (g' : X' ⟶ X) (h : Z' ⟶ Z) (g : Y' ⟶ Y) (wi : g' ≫ i = i' ≫ h)
  (wp : h ≫ p = p' ≫ g)

/-- The mate of the base change map of the pushforwards of a square `h ≫ p = p' ≫ g` is the
composition square `h_* ⋙ p_* ≅ (p' ≫ g)_* ≅ p'_* ⋙ g_*`. -/
lemma mateEquiv_pfBaseChange :
    (mateEquiv (F.adj h) (F.adj g) (F.pfBaseChange h p' p g wp)) =
      (F.pfComp' h p (p' ≫ g) wp).inv ≫ (F.pfComp' p' g (p' ≫ g) rfl).hom := by
  rw [pfBaseChange, iterated_mateEquiv_conjugateEquiv, pfComp'_inv, pfComp'_hom,
    conjugateEquiv_comp]
  congr 1
  simp [sqIso, pbComp']

/-- **The mate of the compact-support exchange map** under `g'^* ⊣ g'_*` and `g^* ⊣ g_*` is the
vertical pasting of the exchange map `g'_* ⋙ i_! ⟶ i'_! ⋙ h_*` of the upper square with the
composition square `h_* ⋙ p_* ≅ (p' ≫ g)_* ≅ p'_* ⋙ g_*` of the lower square. -/
lemma mateEquiv_shriekBaseChange [IsIso (F.baseChange g' i' i h wi)] :
    (mateEquiv (F.adj g') (F.adj g) (F.shriekBaseChange i p i' p' g' h g wi wp)) =
      (F.exchange g' i' i h wi ≫ᵥ TwoSquare.mk _ _ _ _
        ((F.pfComp' h p (p' ≫ g) wp).inv ≫ (F.pfComp' p' g (p' ≫ g) rfl).hom)) := by
  rw [shriekBaseChange]
  erw [mateEquiv_vcomp (F.adj g') (F.adj h) (F.adj g)]
  rw [← mateEquiv_pfBaseChange]
  rfl

end Mate

section IdentitySquares

variable [𝒪.ContainsIdentities] {X Y : 𝒞}

/-- The base change map of the square `g ≫ 𝟙 = 𝟙 ≫ g` is an isomorphism. -/
lemma isIso_baseChange_id_vert (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g) :
    IsIso (F.baseChange g (𝟙 X) (𝟙 Y) g w) := by
  rw [F.baseChange_id_vert g w]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  infer_instance

/-- The exchange map of the square `g ≫ 𝟙 = 𝟙 ≫ g` is an isomorphism. -/
lemma isIso_exchange_id_vert (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g)
    [IsIso (F.baseChange g (𝟙 X) (𝟙 Y) g w)] :
    IsIso (F.exchange g (𝟙 X) (𝟙 Y) g w) := by
  rw [F.exchange_id_vert g w]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]
  infer_instance

end IdentitySquares

section Triangles

variable [𝒪.ContainsIdentities] {X Y Z X' Y' Z' : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y) (i' : X' ⟶ Z')
  (p' : Z' ⟶ Y') [Fact (𝒪 i)] [Fact (𝒪 i')] (g' : X' ⟶ X) (h : Z' ⟶ Z) (g : Y' ⟶ Y)
  (wi : g' ≫ i = i' ≫ h) (wp : h ≫ p = p' ≫ g)

/-- The triangle of factorizations `X' ⟶[𝟙] X' ⟶[g'] X`, `X ⟶[i] Z ⟶[p] Y`,
`X' ⟶[i'] Z' ⟶[p' ≫ g] Y` of `g'` followed by `p ∘ i`, with the square `g' ≫ i = i' ≫ h`. -/
abbrev shriekBaseChangeTriangleLeft : ShriekTriangle 𝒪 X' X Y where
  Z₁ := X'
  Z₂ := Z
  W := Z'
  i₁ := 𝟙 X'
  p₁ := g'
  i₂ := i
  p₂ := p
  i := i'
  p := p' ≫ g
  q := i'
  r := h
  i_q := Category.id_comp i'
  r_p := wp
  w := wi

/-- The triangle of factorizations `X' ⟶[i'] Z' ⟶[p'] Y'`, `Y' ⟶[𝟙] Y' ⟶[g] Y`,
`X' ⟶[i'] Z' ⟶[p' ≫ g] Y` of `p' ∘ i'` followed by `g`, with the square
`p' ≫ 𝟙 = 𝟙 ≫ p'`. -/
abbrev shriekBaseChangeTriangleRight : ShriekTriangle 𝒪 X' Y' Y where
  Z₁ := Z'
  Z₂ := Y'
  W := Z'
  i₁ := i'
  p₁ := p'
  i₂ := 𝟙 Y'
  p₂ := g
  i := i'
  p := p' ≫ g
  q := 𝟙 Z'
  r := p'
  i_q := Category.comp_id i'
  r_p := rfl
  w := by rw [Category.comp_id, Category.id_comp]

/-- The composition isomorphism of `shriekBaseChangeTriangleLeft`, after `(𝟙)_! ≅ 𝟭`: the
exchange map of the square `g' ≫ i = i' ≫ h` followed by `h_* ⋙ p_* ≅ (p' ≫ g)_*`. -/
lemma compIso_shriekBaseChangeTriangleLeft_hom_app [IsIso (F.baseChange g' i' i h wi)]
    [IsIso (F.exchange g' i' i h wi)] (K : F.obj X') :
    (F.shriek i p).map ((F.pf g').map ((F.shId X').inv.app K)) ≫
        (F.compIso (shriekBaseChangeTriangleLeft i p i' p' g' h g wi wp)).hom.app K =
      (F.pf p).map ((F.exchange g' i' i h wi).app K) ≫
        (F.pfComp' h p (p' ≫ g) wp).inv.app ((F.sh i').obj K) := by
  rw [compIso_hom_app]
  dsimp only
  rw [F.shComp'_id_left_inv_app]
  dsimp only [shriek, Functor.comp_map]
  rw [← Functor.map_comp_assoc, F.exchange_naturality_assoc, ← Functor.map_comp (F.pf h),
    ← Functor.map_comp (F.sh i'),
    Iso.inv_hom_id_app]
  simp

/-- The inverse of the composition isomorphism of `shriekBaseChangeTriangleRight`, after
`(𝟙)_! ≅ 𝟭`: the isomorphism `(p' ≫ g)_* ≅ p'_* ⋙ g_*`. -/
lemma compIso_shriekBaseChangeTriangleRight_inv_app (M : F.obj X') :
    haveI := F.isIso_baseChange_id_vert p' (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g).w
    haveI := F.isIso_exchange_id_vert p' (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g).w
    (F.compIso (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g)).inv.app M ≫
        (F.pf g).map ((F.shId Y').hom.app ((F.shriek i' p').obj M)) =
      (F.pfComp' p' g (p' ≫ g) rfl).hom.app ((F.sh i').obj M) := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, compIso_hom_app]
  dsimp only
  rw [F.exchange_id_vert_app, F.shComp'_id_right_inv_app]
  simp [← Functor.map_comp, shriek]

/-- **The mate of the compact-support exchange map is a composite of composition
isomorphisms**: under `g'^* ⊣ g'_*` and `g^* ⊣ g_*`, the mate of the compact-support exchange
map of the squares `g' ≫ i = i' ≫ h` and `h ≫ p = p' ≫ g` is, up to `(𝟙)_! ≅ 𝟭`, the composite
`g'_* ⋙ (p_* i_!) ≅ (p' ≫ g)_* i'_! ≅ (p'_* i'_!) ⋙ g_*` of the composition isomorphisms of the
triangles `shriekBaseChangeTriangleLeft` and `shriekBaseChangeTriangleRight`. -/
theorem mateEquiv_shriekBaseChange_eq_compIso [IsIso (F.baseChange g' i' i h wi)]
    [IsIso (F.exchange g' i' i h wi)] :
    haveI := F.isIso_baseChange_id_vert p' (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g).w
    haveI := F.isIso_exchange_id_vert p' (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g).w
    (mateEquiv (F.adj g') (F.adj g) (F.shriekBaseChange i p i' p' g' h g wi wp)) =
      Functor.whiskerRight ((Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (F.shId X').inv (F.pf g')) (F.shriek i p) ≫
        (F.compIso (shriekBaseChangeTriangleLeft i p i' p' g' h g wi wp)).hom ≫
        (F.compIso (shriekBaseChangeTriangleRight (𝒪 := 𝒪) i' p' g)).inv ≫
        Functor.whiskerLeft (F.shriek i' p')
          (Functor.whiskerRight (F.shId Y').hom (F.pf g) ≫ (Functor.leftUnitor _).hom) := by
  rw [mateEquiv_shriekBaseChange]
  ext K
  have h₁ := F.compIso_shriekBaseChangeTriangleLeft_hom_app i p i' p' g' h g wi wp K
  have h₂ := F.compIso_shriekBaseChangeTriangleRight_inv_app i' p' g K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [Category.comp_id]
  rw [reassoc_of% h₁, h₂]
  simp [TwoSquare.vComp]
end Triangles

end ExchangeFormalism

end CategoryTheory
