/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek

/-!
# The composition isomorphism in an exchange formalism

For composable morphisms `X ⟶ Y ⟶ S` of the index category of an exchange formalism `F`, a
*triangle of factorizations* (`CategoryTheory.ExchangeFormalism.ShriekTriangle`) consists of
factorizations `X ⟶[i₁] Z₁ ⟶[p₁] Y`, `Y ⟶[i₂] Z₂ ⟶[p₂] S` and `X ⟶[i] W ⟶[p] S` (with `i₁`, `i₂`,
`i` open) and maps `q : Z₁ ⟶ W` (open) and `r : W ⟶ Z₂` with `i₁ ≫ q = i`, `r ≫ p₂ = p` and
`p₁ ≫ i₂ = q ≫ r`. When the base change map and the exchange map of the square
`p₁ ≫ i₂ = q ≫ r` are isomorphisms, it gives the composition isomorphism
`F.shriek i₁ p₁ ⋙ F.shriek i₂ p₂ ≅ F.shriek i p`
(`CategoryTheory.ExchangeFormalism.compIso`). This file proves that it is natural with respect to
morphisms of triangles (`CategoryTheory.ExchangeFormalism.compIso_naturality`) and compatible
with the compact-support exchange maps
(`CategoryTheory.ExchangeFormalism.compIso_shriekBaseChange`).

For a `AlgebraicGeometry.CompactSupportFormalism`, the composition isomorphism of a triangle of
compactifications is the one of its underlying triangle of factorizations.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

variable (𝒪) in
/-- **A triangle of factorizations** of composable morphisms `X ⟶ Y ⟶ S`: factorizations
`X ⟶[i₁] Z₁ ⟶[p₁] Y`, `Y ⟶[i₂] Z₂ ⟶[p₂] S` and `X ⟶[i] W ⟶[p] S` with `i₁`, `i₂`, `i` in `𝒪`, and
maps `q : Z₁ ⟶ W` in `𝒪` and `r : W ⟶ Z₂` with `i₁ ≫ q = i`, `r ≫ p₂ = p` and
`p₁ ≫ i₂ = q ≫ r`. -/
structure ShriekTriangle (X Y S : 𝒞) where
  /-- The middle object of the factorization of the first morphism. -/
  Z₁ : 𝒞
  /-- The middle object of the factorization of the second morphism. -/
  Z₂ : 𝒞
  /-- The middle object of the factorization of the composite. -/
  W : 𝒞
  /-- The open immersion of the factorization of the first morphism. -/
  i₁ : X ⟶ Z₁
  /-- The second map of the factorization of the first morphism. -/
  p₁ : Z₁ ⟶ Y
  /-- The open immersion of the factorization of the second morphism. -/
  i₂ : Y ⟶ Z₂
  /-- The second map of the factorization of the second morphism. -/
  p₂ : Z₂ ⟶ S
  /-- The open immersion of the factorization of the composite. -/
  i : X ⟶ W
  /-- The second map of the factorization of the composite. -/
  p : W ⟶ S
  /-- The open immersion `Z₁ ⟶ W`. -/
  q : Z₁ ⟶ W
  /-- The map `W ⟶ Z₂`. -/
  r : W ⟶ Z₂
  [fact_i₁ : Fact (𝒪 i₁)]
  [fact_i₂ : Fact (𝒪 i₂)]
  [fact_i : Fact (𝒪 i)]
  [fact_q : Fact (𝒪 q)]
  i_q : i₁ ≫ q = i
  r_p : r ≫ p₂ = p
  w : p₁ ≫ i₂ = q ≫ r

attribute [instance] ShriekTriangle.fact_i₁ ShriekTriangle.fact_i₂ ShriekTriangle.fact_i
  ShriekTriangle.fact_q

section Composition

variable {X Y S : 𝒞}

/-- **The composition isomorphism** attached to a triangle of factorizations `T`:
```
i₁_! ⋙ p₁_* ⋙ i₂_! ⋙ p₂_* ≅ i₁_! ⋙ q_! ⋙ r_* ⋙ p₂_* ≅ i_! ⋙ p_*
```
built from the exchange isomorphism of the square `p₁ ≫ i₂ = q ≫ r`. -/
noncomputable def compIso (T : ShriekTriangle 𝒪 X Y S)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)] :
    F.shriek T.i₁ T.p₁ ⋙ F.shriek T.i₂ T.p₂ ≅ F.shriek T.i T.p :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.sh T.i₁) ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)) (F.pf T.p₂) ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.shComp' T.i₁ T.q T.i T.i_q).symm _ ≪≫
    Functor.isoWhiskerLeft _ (F.pfComp' T.r T.p₂ T.p T.r_p).symm

lemma compIso_hom_app (T : ShriekTriangle 𝒪 X Y S)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)] (K : F.obj X) :
    (F.compIso T).hom.app K =
      (F.pf T.p₂).map ((F.exchange T.p₁ T.q T.i₂ T.r T.w).app ((F.sh T.i₁).obj K) ≫
        (F.pf T.r).map ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K)) ≫
      (F.pfComp' T.r T.p₂ T.p T.r_p).inv.app ((F.sh T.i).obj K) := by
  simp [compIso, shriek]


variable (𝒪) in
/-- **A morphism of triangles of factorizations** `T' ⟶ T`: refinements `rf`, `rg`, `rfg` of the
three factorizations of `T` by those of `T'`, compatible with `q` and `r`. -/
structure ShriekTriangle.Hom (T' T : ShriekTriangle 𝒪 X Y S) where
  /-- The refinement of the factorizations of the first morphism. -/
  rf : T'.Z₁ ⟶ T.Z₁
  /-- The refinement of the factorizations of the second morphism. -/
  rg : T'.Z₂ ⟶ T.Z₂
  /-- The refinement of the factorizations of the composite. -/
  rfg : T'.W ⟶ T.W
  wf : 𝟙 X ≫ T.i₁ = T'.i₁ ≫ rf
  hf : rf ≫ T.p₁ = T'.p₁
  wg : 𝟙 Y ≫ T.i₂ = T'.i₂ ≫ rg
  hg : rg ≫ T.p₂ = T'.p₂
  wfg : 𝟙 X ≫ T.i = T'.i ≫ rfg
  hfg : rfg ≫ T.p = T'.p
  q_comm : rf ≫ T.q = T'.q ≫ rfg
  p_comm : T'.r ≫ rg = rfg ≫ T.r

omit F in
/-- The big square of a morphism of triangles commutes: `p₁' ≫ i₂ = q' ≫ r' ≫ rg`. -/
lemma ShriekTriangle.Hom.big_w {T' T : ShriekTriangle 𝒪 X Y S} (φ : ShriekTriangle.Hom 𝒪 T' T) :
    T'.p₁ ≫ T.i₂ = T'.q ≫ (T'.r ≫ φ.rg) := by
  have := φ.wg
  rw [Category.id_comp] at this
  rw [this, ← Category.assoc, T'.w, Category.assoc]

/-- **Naturality of the composition isomorphism**: for a morphism of triangles `φ : T' ⟶ T`,
the comparisons along the refinements of `φ` intertwine the composition isomorphisms of `T` and
`T'`. -/
theorem compIso_naturality {T' T : ShriekTriangle 𝒪 X Y S} (φ : ShriekTriangle.Hom 𝒪 T' T)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.baseChange T'.p₁ T'.q T'.i₂ T'.r T'.w)]
    [IsIso (F.exchange T'.p₁ T'.q T'.i₂ T'.r T'.w)]
    [IsIso (F.baseChange (𝟙 X) T'.i₁ T.i₁ φ.rf φ.wf)]
    [IsIso (F.baseChange (𝟙 Y) T'.i₂ T.i₂ φ.rg φ.wg)]
    [IsIso (F.baseChange (𝟙 X) T'.i T.i φ.rfg φ.wfg)]
    [IsIso (F.baseChange φ.rf T'.q T.q φ.rfg φ.q_comm)]
    [IsIso (F.baseChange T'.p₁ T'.q T.i₂ (T'.r ≫ φ.rg) φ.big_w)] :
    (F.compIso T).hom ≫ F.refinementComparison T'.i T'.p T.i T.p φ.rfg φ.wfg φ.hfg =
      NatTrans.hcomp (F.refinementComparison T'.i₁ T'.p₁ T.i₁ T.p₁ φ.rf φ.wf φ.hf)
          (F.refinementComparison T'.i₂ T'.p₂ T.i₂ T.p₂ φ.rg φ.wg φ.hg) ≫
        (F.compIso T').hom := by
  ext K
  have hG₁ := congr_app (F.exchange_paste_horiz φ.rf T.p₁ T'.q T.q T.i₂ φ.rfg T.r
    T'.p₁ (T'.r ≫ φ.rg) φ.q_comm T.w φ.hf φ.p_comm.symm φ.big_w) ((F.sh T'.i₁).obj K)
  have hG₂ := congr_app (F.exchange_paste_horiz T'.p₁ (𝟙 Y) T'.q T'.i₂ T.i₂ T'.r
    φ.rg T'.p₁ (T'.r ≫ φ.rg) T'.w φ.wg (Category.comp_id _) rfl φ.big_w) ((F.sh T'.i₁).obj K)
  have hC := congr_app (F.exchange_paste_vert (𝟙 X) φ.rf φ.rfg T'.i₁ T.i₁ T'.q T.q
    T'.i T.i φ.wf φ.q_comm T'.i_q T.i_q φ.wfg) K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hG₁ hG₂ hC
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.hcomp_app, compIso_hom_app,
    compIso_hom_app, refinementComparison_app, refinementComparison_app,
    refinementComparison_app, hC]
  dsimp only [shriek, Functor.comp_map, Functor.comp_obj]
  have hbg : (T'.r ≫ φ.rg) ≫ T.p₂ = T'.p := by
    rw [Category.assoc, φ.hg, T'.r_p]
  have hL2 := F.pfComp'_assoc_inv_app φ.rfg T.r T.p₂ (T'.r ≫ φ.rg) T.p T'.p
    φ.p_comm.symm T.r_p hbg φ.hfg ((F.sh T'.i).obj K)
  have hR2 := F.pfComp'_assoc_inv_app T'.r φ.rg T.p₂ (T'.r ≫ φ.rg) T'.p₂ T'.p
    rfl φ.hg hbg T'.r_p ((F.sh T'.i).obj K)
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, hL2, ← Functor.map_comp_assoc, ← NatTrans.naturality_assoc,
    hR2]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  refine congrArg (· ≫ _) (congrArg (F.pf T.p₂).map ?_)
  -- the two decompositions of the exchange map of the big square
  have hG := hG₁.symm.trans hG₂
  have hG' := congrArg (fun x ↦ (F.sh T.i₂).map ((F.pfComp' φ.rf T.p₁ T'.p₁
    φ.hf).inv.app ((F.sh T'.i₁).obj K)) ≫ x) hG
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hG'
  -- naturality of the composition isomorphism of the extensions by zero
  have hSC := congrArg (F.pf T.r).map ((F.shComp' T.i₁ T.q T.i T.i_q).hom.naturality
    ((F.pfId X).inv.app K))
  -- naturality of the exchange maps
  have hεQ := (F.exchange T.p₁ T.q T.i₂ T.r T.w).naturality
    ((F.sh T.i₁).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) T'.i₁ T.i₁ φ.rf φ.wf).app K)
  have hP₁ := (F.pfComp' φ.rfg T.r (T'.r ≫ φ.rg) φ.p_comm.symm).inv.naturality
    ((F.shComp' T'.i₁ T'.q T'.i T'.i_q).inv.app K)
  have hP₂ := (F.pfComp' T'.r φ.rg (T'.r ≫ φ.rg) rfl).inv.naturality
    ((F.shComp' T'.i₁ T'.q T'.i T'.i_q).inv.app K)
  have hεB := (F.exchange (𝟙 Y) T'.i₂ T.i₂ φ.rg φ.wg).naturality
    ((F.pf T.p₁).map ((F.sh T.i₁).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) T'.i₁ T.i₁ φ.rf φ.wf).app K) ≫
      (F.pfComp' φ.rf T.p₁ T'.p₁ φ.hf).inv.app ((F.sh T'.i₁).obj K))
  have hId := congrArg (F.sh T.i₂).map ((F.pfId Y).inv.naturality
    ((F.pf T.p₁).map ((F.sh T.i₁).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) T'.i₁ T.i₁ φ.rf φ.wf).app K) ≫
      (F.pfComp' φ.rf T.p₁ T'.p₁ φ.hf).inv.app ((F.sh T'.i₁).obj K)))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Functor.id_obj,
    Functor.id_map, Category.assoc] at hSC hεQ hP₁ hP₂ hεB hId
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hSC, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hεQ, hP₁, reassoc_of% hG', hP₂, ← reassoc_of% hεB,
    ← reassoc_of% hId, ← F.pfComp'_id_right_hom_app, Functor.map_comp_assoc]

/-- **The compact-support exchange maps and the composition isomorphisms.** Let `T` be a
triangle of factorizations of `X ⟶ Y ⟶ S` and `T'` one of `X' ⟶ Y' ⟶ S'` lying over it along
`a : T'.Z₁ ⟶ T.Z₁`, `c : T'.Z₂ ⟶ T.Z₂` and `b : T'.W ⟶ T.W`, with the relevant base change maps
of the extension by zero isomorphisms. Then the exchange map of the composite is the horizontal
composite of the exchange maps, through the composition isomorphisms of `T` and `T'`. -/
theorem compIso_shriekBaseChange {X Y S X' Y' S' : 𝒞} {gX : X' ⟶ X} {gY : Y' ⟶ Y}
    {gS : S' ⟶ S} (T : ShriekTriangle 𝒪 X Y S) (T' : ShriekTriangle 𝒪 X' Y' S')
    (a : T'.Z₁ ⟶ T.Z₁) (c : T'.Z₂ ⟶ T.Z₂) (b : T'.W ⟶ T.W)
    (wfi : gX ≫ T.i₁ = T'.i₁ ≫ a) (wfp : a ≫ T.p₁ = T'.p₁ ≫ gY)
    (wgi : gY ≫ T.i₂ = T'.i₂ ≫ c) (wgp : c ≫ T.p₂ = T'.p₂ ≫ gS)
    (wfgi : gX ≫ T.i = T'.i ≫ b) (wfgp : b ≫ T.p = T'.p ≫ gS)
    (wq : a ≫ T.q = T'.q ≫ b) (hp : b ≫ T.r = T'.r ≫ c)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w)]
    [IsIso (F.baseChange T'.p₁ T'.q T'.i₂ T'.r T'.w)]
    [IsIso (F.exchange T'.p₁ T'.q T'.i₂ T'.r T'.w)]
    [IsIso (F.baseChange gX T'.i₁ T.i₁ a wfi)]
    [IsIso (F.baseChange gY T'.i₂ T.i₂ c wgi)]
    [IsIso (F.baseChange gX T'.i T.i b wfgi)]
    [IsIso (F.baseChange a T'.q T.q b wq)] :
    Functor.whiskerRight (F.compIso T).hom (F.pb gS) ≫
        (F.shriekBaseChange T.i T.p T'.i T'.p gX b gS wfgi wfgp) =
      (F.shriekBaseChange T.i₁ T.p₁ T'.i₁ T'.p₁ gX a gY wfi wfp ≫ₕ
          F.shriekBaseChange T.i₂ T.p₂ T'.i₂ T'.p₂ gY c gS wgi wgp) ≫
        Functor.whiskerLeft (F.pb gX) (F.compIso T').hom := by
  ext K
  -- the base change map of the extension by zero along `i = i₁ ≫ q`
  have hbc := congr_app (F.baseChange_paste_vert gX a b T'.i₁ T.i₁ T'.q T.q T'.i
    T.i wfi wq T'.i_q T.i_q wfgi) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc] at hbc
  have hA : (F.pb b).map ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K) ≫
      inv ((F.baseChange gX T'.i T.i b wfgi).app K) =
      inv ((F.baseChange a T'.q T.q b wq).app ((F.sh T.i₁).obj K)) ≫
        (F.sh T'.q).map (inv ((F.baseChange gX T'.i₁ T.i₁ a wfi).app K)) ≫
        (F.shComp' T'.i₁ T'.q T'.i T'.i_q).inv.app ((F.pb gX).obj K) := by
    rw [IsIso.comp_inv_eq, hbc]
    simp
  -- the cube relating the exchange maps of `T` and `T'`
  have hC := F.exchange_pfBaseChange_cube T.p₁ T.q T.i₂ T.r T'.p₁ T'.q T'.i₂ T'.r a gY b
    c T.w T'.w wfp wq wgi hp ((F.sh T.i₁).obj K)
  have hC' : inv ((F.baseChange gY T'.i₂ T.i₂ c wgi).app
        ((F.pf T.p₁).obj ((F.sh T.i₁).obj K))) ≫
      (F.sh T'.i₂).map ((F.pfBaseChange a T'.p₁ T.p₁ gY wfp).app
        ((F.sh T.i₁).obj K)) ≫
      (F.exchange T'.p₁ T'.q T'.i₂ T'.r T'.w).app
        ((F.pb a).obj ((F.sh T.i₁).obj K)) =
      (F.pb c).map ((F.exchange T.p₁ T.q T.i₂ T.r T.w).app
        ((F.sh T.i₁).obj K)) ≫
      (F.pfBaseChange b T'.r T.r c hp).app ((F.sh T.q).obj ((F.sh T.i₁).obj K)) ≫
      (F.pf T'.r).map (inv ((F.baseChange a T'.q T.q b wq).app
        ((F.sh T.i₁).obj K))) := by
    rw [← reassoc_of% hC]
    simp
  -- the base change map of the pushforwards along `p = r ≫ p₂`
  have hv := congr_app (F.pfBaseChange_paste_vert b c gS T'.r T.r T'.p₂ T.p₂ T'.p
    T.p hp wgp T'.r_p T.r_p wfgp) ((F.sh T.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at hv
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    compIso_hom_app, compIso_hom_app]
  simp only [shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Functor.associator_hom_app, Functor.associator_inv_app]
  dsimp only [shriek, Functor.comp_obj, Functor.id_obj, Functor.comp_map]
  erw [hv]
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  have hcancel : (F.pb gS).map ((F.pfComp' T.r T.p₂ T.p T.r_p).inv.app
      ((F.sh T.i).obj K)) ≫ (F.pb gS).map ((F.pfComp' T.r T.p₂ T.p T.r_p).hom.app
      ((F.sh T.i).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hn₁ := (F.pfBaseChange c T'.p₂ T.p₂ gS wgp).naturality
    ((F.exchange T.p₁ T.q T.i₂ T.r T.w).app ((F.sh T.i₁).obj K) ≫
      (F.pf T.r).map ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K))
  have hn₂ := (F.pfComp' T'.r T'.p₂ T'.p T'.r_p).inv.naturality
    (inv ((F.baseChange gX T'.i T.i b wfgi).app K))
  have hn₃ := congrArg (F.pf T'.p₂).map ((F.pfBaseChange b T'.r T.r c hp).naturality
    ((F.shComp' T.i₁ T.q T.i T.i_q).inv.app K))
  have hn₄ := congrArg (F.pf T'.p₂).map
    ((F.exchange T'.p₁ T'.q T'.i₂ T'.r T'.w).naturality
      (inv ((F.baseChange gX T'.i₁ T.i₁ a wfi).app K)))
  have hA' := congrArg (fun φ ↦ (F.pf T'.p₂).map ((F.pf T'.r).map φ)) hA
  have hC'' := congrArg (F.pf T'.p₂).map hC'
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
    at hn₁ hn₂ hn₃ hn₄ hA' hC''
  rw [reassoc_of% hcancel, reassoc_of% hn₁, ← hn₂, reassoc_of% hn₃, reassoc_of% hA',
    reassoc_of% hn₄, reassoc_of% hC'']
end Composition

end CategoryTheory.ExchangeFormalism
