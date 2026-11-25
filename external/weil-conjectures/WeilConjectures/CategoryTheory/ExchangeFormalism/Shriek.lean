/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange

/-!
# Compactly supported direct images in an exchange formalism

In a `CategoryTheory.ExchangeFormalism` `F`, a factorization `X ⟶[i] Z ⟶[p] Y` of a morphism
with `i` in the class `𝒪` of open immersions gives the compactly supported direct image
`F.shriek i p = i_! ⋙ p_*`. This file records, for such factorizations:

- the *comparison along a refinement* `r : Z ⟶ Z₁` of `X ⟶[i₁] Z₁ ⟶[p₁] Y` by `X ⟶[i] Z ⟶[p] Y`
  (`i ≫ r = i₁`, `r ≫ p₁ = p`), the map `F.shriek i₁ p₁ ⟶ F.shriek i p` built from the exchange
  map of the square of `r` (`CategoryTheory.ExchangeFormalism.refinementComparison`), with its
  identity and composition laws;
- the *compact-support exchange map* `g^* (p_* i_!) ⟶ (p'_* i'_!) g'^*` of a factorization
  `X' ⟶[i'] Z' ⟶[p'] Y'` lying over `X ⟶[i] Z ⟶[p] Y` along `h : Z' ⟶ Z`
  (`CategoryTheory.ExchangeFormalism.shriekBaseChange`), with its identity and horizontal pasting
  laws and its compatibility with the comparisons along refinements
  (`CategoryTheory.ExchangeFormalism.shriekBaseChange_refinementComparison`).

For a `AlgebraicGeometry.CompactSupportFormalism`, the constructions along compactifications
are these constructions for the underlying factorizations, the hypotheses that the relevant base
change maps of the extension by zero are isomorphisms being supplied by cartesian squares.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Shriek

variable {X Y Z : 𝒞}

/-- The compactly supported direct image `i_! ⋙ p_*` attached to a factorization
`X ⟶[i] Z ⟶[p] Y` with `i` an open immersion. -/
def shriek (i : X ⟶ Z) [Fact (𝒪 i)] (p : Z ⟶ Y) : F.obj X ⥤ F.obj Y := F.sh i ⋙ F.pf p

end Shriek

section Refinement

variable {X Y Z Z₁ Z₂ : 𝒞}

/-- **The comparison along a refinement** `r : Z ⟶ Z₁` of the factorization
`X ⟶[i₁] Z₁ ⟶[p₁] Y` by `X ⟶[i] Z ⟶[p] Y`, whose base change map of the square
`𝟙 X ≫ i₁ = i ≫ r` is an isomorphism: the map `F.shriek i₁ p₁ ⟶ F.shriek i p` given by the
exchange map `(𝟙 X)_* ⋙ i₁_! ⟶ i_! ⋙ r_*` followed by `r_* ⋙ p₁_* ≅ p_*`. -/
noncomputable def refinementComparison (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    [Fact (𝒪 i)] [Fact (𝒪 i₁)] (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r) (hp : r ≫ p₁ = p)
    [IsIso (F.baseChange (𝟙 X) i i₁ r w)] : F.shriek i₁ p₁ ⟶ F.shriek i p :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pfId X).inv (F.shriek i₁ p₁) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.exchange (𝟙 X) i i₁ r w) (F.pf p₁) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.sh i) (F.pfComp' r p₁ p hp).inv

lemma refinementComparison_app (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    [Fact (𝒪 i)] [Fact (𝒪 i₁)] (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r) (hp : r ≫ p₁ = p)
    [IsIso (F.baseChange (𝟙 X) i i₁ r w)] (K : F.obj X) :
    (F.refinementComparison i p i₁ p₁ r w hp).app K =
      (F.pf p₁).map ((F.sh i₁).map ((F.pfId X).inv.app K) ≫
          (F.exchange (𝟙 X) i i₁ r w).app K) ≫
        (F.pfComp' r p₁ p hp).inv.app ((F.sh i).obj K) := by
  simp [refinementComparison, shriek]

/-- **The identity law**: the comparison along the identity is the identity. -/
lemma refinementComparison_id [𝒪.ContainsIdentities] (i : X ⟶ Z) (p : Z ⟶ Y) [Fact (𝒪 i)]
    (w : 𝟙 X ≫ i = i ≫ 𝟙 Z) (hp : 𝟙 Z ≫ p = p)
    [IsIso (F.baseChange (𝟙 X) i i (𝟙 Z) w)] :
    F.refinementComparison i p i p (𝟙 Z) w hp = 𝟙 _ := by
  ext K
  have h₁ := congr_app (F.exchange_id_horiz i w) K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Functor.comp_obj, Functor.id_obj] at h₁
  rw [refinementComparison_app, h₁, Category.comp_id, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [F.pfComp'_id_left_inv_app, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- **The composition law**: the comparison along a composite of refinements is the composite of
the comparisons, in the opposite order. -/
lemma refinementComparison_comp (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (i₂ : X ⟶ Z₂) (p₂ : Z₂ ⟶ Y) [Fact (𝒪 i)] [Fact (𝒪 i₁)] [Fact (𝒪 i₂)] (r : Z ⟶ Z₁)
    (s : Z₁ ⟶ Z₂) (rs : Z ⟶ Z₂) (hrs : r ≫ s = rs) (wr : 𝟙 X ≫ i₁ = i ≫ r)
    (ws : 𝟙 X ≫ i₂ = i₁ ≫ s) (wrs : 𝟙 X ≫ i₂ = i ≫ rs) (hpr : r ≫ p₁ = p) (hps : s ≫ p₂ = p₁)
    (hprs : rs ≫ p₂ = p) [IsIso (F.baseChange (𝟙 X) i i₁ r wr)]
    [IsIso (F.baseChange (𝟙 X) i₁ i₂ s ws)]
    [IsIso (F.baseChange (𝟙 X) i i₂ rs wrs)] :
    F.refinementComparison i p i₂ p₂ rs wrs hprs =
      F.refinementComparison i₁ p₁ i₂ p₂ s ws hps ≫ F.refinementComparison i p i₁ p₁ r wr hpr := by
  ext K
  have hpaste := congr_app (F.exchange_paste_horiz (𝟙 X) (𝟙 X) i i₁ i₂ r s (𝟙 X)
    rs wr ws (Category.id_comp _) hrs wrs) K
  have hassoc := congr_app (F.pfComp'_assoc r s p₂ rs p₁ p hrs hps hprs) ((F.sh i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hpaste hassoc
  have hnat := congrArg (F.pf p₂).map
    ((F.exchange (𝟙 X) i₁ i₂ s ws).naturality ((F.pfId X).inv.app K))
  have hnat2 := (F.pfComp' s p₂ p₁ hps).inv.naturality
    ((F.sh i₁).map ((F.pfId X).inv.app K) ≫ (F.exchange (𝟙 X) i i₁ r wr).app K)
  have hassoc' : (F.pfComp' s p₂ p₁ hps).inv.app ((F.pf r).obj ((F.sh i).obj K)) ≫
      (F.pfComp' r p₁ p hpr).inv.app ((F.sh i).obj K) =
      (F.pf p₂).map ((F.pfComp' r s rs hrs).inv.app ((F.sh i).obj K)) ≫
        (F.pfComp' rs p₂ p hprs).inv.app ((F.sh i).obj K) := by
    rw [← cancel_epi ((F.pfComp' s p₂ p₁ hps).hom.app ((F.pf r).obj ((F.sh i).obj K))),
      ← cancel_epi ((F.pfComp' r p₁ p hpr).hom.app ((F.sh i).obj K))]
    simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [← reassoc_of% hassoc]
    simp [← Functor.map_comp_assoc]
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hnat hnat2
  rw [NatTrans.comp_app, refinementComparison_app, refinementComparison_app,
    refinementComparison_app, hpaste, F.pfComp'_id_left_hom_app]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hnat2, hassoc', reassoc_of% hnat]

/-- The base change map of the square `𝟙 X ≫ i₁ = i ≫ r` is, up to `(𝟙 X)^* ≅ 𝟭`, the exchange
morphism `CategoryTheory.Adjunction.exchangeLeft` of the composition isomorphism
`i₁^* ≅ r^* ⋙ i^*`. -/
lemma baseChange_id_eq_exchangeLeft (i : X ⟶ Z) (i₁ : X ⟶ Z₁) [Fact (𝒪 i)] [Fact (𝒪 i₁)]
    (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r) (hi : i ≫ r = i₁) :
    (F.baseChange (𝟙 X) i i₁ r w) =
      Functor.whiskerRight (F.pbId X).hom (F.sh i) ≫
        Adjunction.exchangeLeft (F.shAdj i₁) (F.shAdj i)
          (Functor.rightUnitor (F.pb i₁) ≪≫ F.pbComp' i r i₁ hi) := by
  ext K
  have hn := (F.pbId X).hom.naturality ((F.shAdj i₁).unit.app K)
  simp only [Functor.id_map] at hn
  rw [baseChange, F.sqIso_eq (𝟙 X) i i₁ r w i₁ (Category.id_comp i₁) hi]
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app,
    Functor.whiskerRight_app, Adjunction.exchangeLeft_app, Iso.trans_hom, Iso.symm_hom,
    Functor.rightUnitor_hom_app, Category.id_comp, Functor.comp_obj, Functor.id_obj,
    Functor.leftUnitor_inv_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Functor.id_map,
    F.pbComp'_id_left_inv_app, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Functor.map_comp_assoc]
  erw [hn]
  rw [Functor.map_comp_assoc]
  rfl

/-- **The comparison along a refinement, through a base change isomorphism**: if the base change
map of the square of `r` is `β : i_! ≅ i₁_! ⋙ r^*` up to `(𝟙 X)^* ≅ 𝟭`, then the comparison
along `r` is the unit of `r^* ⊣ r_*`, followed by `β⁻¹` and by `r_* ⋙ p₁_* ≅ p_*`. -/
lemma refinementComparison_eq_of_baseChange (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁)
    (p₁ : Z₁ ⟶ Y) [Fact (𝒪 i)] [Fact (𝒪 i₁)] (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r)
    (hp : r ≫ p₁ = p) [IsIso (F.baseChange (𝟙 X) i i₁ r w)]
    (β : F.sh i ≅ F.sh i₁ ⋙ F.pb r)
    (hβ : (F.baseChange (𝟙 X) i i₁ r w) =
      Functor.whiskerRight (F.pbId X).hom (F.sh i) ≫ (Functor.leftUnitor _).hom ≫ β.hom) :
    F.refinementComparison i p i₁ p₁ r w hp =
      Functor.whiskerRight (Functor.whiskerLeft (F.sh i₁) (F.adj r).unit) (F.pf p₁) ≫
        Functor.whiskerRight β.inv (F.pf r ⋙ F.pf p₁) ≫
        Functor.whiskerLeft (F.sh i) (F.pfComp' r p₁ p hp).inv := by
  have hinv : inv (F.baseChange (𝟙 X) i i₁ r w) =
      β.inv ≫ (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pbId X).inv (F.sh i) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [hβ]
    ext K
    simp [← Functor.map_comp]
  ext K
  have key : (F.sh i₁).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) i i₁ r w).app K =
      (F.adj r).unit.app ((F.sh i₁).obj K) ≫ (F.pf r).map (β.inv.app K) := by
    have hc := conjugateEquiv_counit Adjunction.id (F.adj (𝟙 X)) (F.pbId X).hom K
    rw [← pfId_inv] at hc
    simp only [exchange, mateEquiv_apply, hinv, NatTrans.comp_app]
    dsimp
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    have hc' : (F.pbId X).inv.app ((F.pf (𝟙 X)).obj K) ≫ (F.adj (𝟙 X)).counit.app K =
        (F.pfId X).hom.app K := by
      rw [← cancel_epi ((F.pfId X).inv.app K)]
      erw [(F.pbId X).inv.naturality_assoc, hc]
      simp
    simp only [← Functor.map_comp, hc']
    rw [← β.inv.naturality, Functor.map_comp, Functor.comp_map, Adjunction.unit_naturality_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [refinementComparison_app, key]
  simp

/-- The comparison along a refinement `r`, in terms of the unit of `r^* ⊣ r_*` and the inverse
of the exchange morphism `i_! ⟶ i₁_! ⋙ r^*` of the composition isomorphism
`i₁^* ≅ r^* ⋙ i^*`. -/
lemma refinementComparison_eq_exchangeLeft (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁)
    (p₁ : Z₁ ⟶ Y) [Fact (𝒪 i)] [Fact (𝒪 i₁)] (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r)
    (hp : r ≫ p₁ = p) (hi : i ≫ r = i₁) [IsIso (F.baseChange (𝟙 X) i i₁ r w)]
    [IsIso (Adjunction.exchangeLeft (F.shAdj i₁) (F.shAdj i)
      (Functor.rightUnitor (F.pb i₁) ≪≫ F.pbComp' i r i₁ hi))] :
    F.refinementComparison i p i₁ p₁ r w hp =
      Functor.whiskerRight (Functor.whiskerLeft (F.sh i₁) (F.adj r).unit) (F.pf p₁) ≫
        Functor.whiskerRight (inv (Adjunction.exchangeLeft (F.shAdj i₁) (F.shAdj i)
          (Functor.rightUnitor (F.pb i₁) ≪≫ F.pbComp' i r i₁ hi))) (F.pf r ⋙ F.pf p₁) ≫
        Functor.whiskerLeft (F.sh i) (F.pfComp' r p₁ p hp).inv := by
  rw [F.refinementComparison_eq_of_baseChange i p i₁ p₁ r w hp
    (asIso (Adjunction.exchangeLeft (F.shAdj i₁) (F.shAdj i)
      (Functor.rightUnitor (F.pb i₁) ≪≫ F.pbComp' i r i₁ hi)))
    (by rw [F.baseChange_id_eq_exchangeLeft i i₁ r w hi]; ext K; simp)]
  rfl

/-- The comparison along a refinement `r`, in terms of the unit of `r^* ⊣ r_*` and the inverse
of the base change map of the extension by zero of the square of `r`. -/
lemma refinementComparison_app_eq (i : X ⟶ Z) (p : Z ⟶ Y) (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    [Fact (𝒪 i)] [Fact (𝒪 i₁)] (r : Z ⟶ Z₁) (w : 𝟙 X ≫ i₁ = i ≫ r) (hp : r ≫ p₁ = p)
    [IsIso (F.baseChange (𝟙 X) i i₁ r w)] (K : F.obj X) :
    (F.refinementComparison i p i₁ p₁ r w hp).app K =
      (F.pf p₁).map ((F.adj r).unit.app ((F.sh i₁).obj K) ≫
        (F.pf r).map (inv ((F.baseChange (𝟙 X) i i₁ r w).app K) ≫
          (F.sh i).map ((F.pbId X).hom.app K))) ≫
        (F.pfComp' r p₁ p hp).inv.app ((F.sh i).obj K) := by
  rw [F.refinementComparison_eq_of_baseChange i p i₁ p₁ r w hp ((Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (F.pbId X).symm (F.sh i) ≪≫
    asIso (F.baseChange (𝟙 X) i i₁ r w))
    (by ext K; simp [← Functor.map_comp_assoc])]
  simp

end Refinement

section ShriekBaseChange

variable {X Y Z X' Y' Z' : 𝒞}

/-- **The compact-support exchange map** `g^* (p_* i_!) ⟶ (p'_* i'_!) g'^*`, i.e. the natural
transformation `F.shriek i p ⋙ g^* ⟶ g'^* ⋙ F.shriek i' p'`, for factorizations
`X ⟶[i] Z ⟶[p] Y` and `X' ⟶[i'] Z' ⟶[p'] Y'` and a morphism `h : Z' ⟶ Z` making both squares
```
X' --g'--> X
|i'        |i
Z' --h---> Z
|p'        |p
Y' --g---> Y
```
commute, when the base change map `g'^* ⋙ i'_! ⟶ i_! ⋙ h^*` of the extension by zero of the upper
square is an isomorphism. It is the horizontal composite of the inverse of that base change map
with the base change map `g^* p_* ⟶ p'_* h^*` of the pushforwards for the lower square
(`ExchangeFormalism.pfBaseChange`). -/
noncomputable def shriekBaseChange (i : X ⟶ Z) (p : Z ⟶ Y) (i' : X' ⟶ Z') (p' : Z' ⟶ Y')
    [Fact (𝒪 i)] [Fact (𝒪 i')] (g' : X' ⟶ X) (h : Z' ⟶ Z) (g : Y' ⟶ Y) (wi : g' ≫ i = i' ≫ h)
    (wp : h ≫ p = p' ≫ g) [IsIso (F.baseChange g' i' i h wi)] :
    TwoSquare (F.shriek i p) (F.pb g') (F.pb g) (F.shriek i' p') :=
  TwoSquare.mk _ _ _ _ (inv (F.baseChange g' i' i h wi)) ≫ₕ F.pfBaseChange h p' p g wp

lemma shriekBaseChange_app (i : X ⟶ Z) (p : Z ⟶ Y) (i' : X' ⟶ Z') (p' : Z' ⟶ Y')
    [Fact (𝒪 i)] [Fact (𝒪 i')] (g' : X' ⟶ X) (h : Z' ⟶ Z) (g : Y' ⟶ Y) (wi : g' ≫ i = i' ≫ h)
    (wp : h ≫ p = p' ≫ g) [IsIso (F.baseChange g' i' i h wi)] (K : F.obj X) :
    (F.shriekBaseChange i p i' p' g' h g wi wp).app K =
      (F.pfBaseChange h p' p g wp).app ((F.sh i).obj K) ≫
        (F.pf p').map (inv ((F.baseChange g' i' i h wi).app K)) := by
  simp [shriekBaseChange, shriek]

/-- **Horizontal pasting** of compact-support exchange maps: for two pairs of squares placed
side by side
```
X'' --a'--> X' --b'--> X
|i''        |i'        |i
Z'' --h₁--> Z' --h₂--> Z
|p''        |p'        |p
Y'' --a---> Y' --b---> Y
```
the exchange map of the outer rectangle along `h₁ ≫ h₂` is the vertical composite of the two
exchange maps, after inserting the composition isomorphisms of the pullbacks. -/
lemma shriekBaseChange_paste_horiz {X'' Y'' Z'' : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y) (i' : X' ⟶ Z')
    (p' : Z' ⟶ Y') (i'' : X'' ⟶ Z'') (p'' : Z'' ⟶ Y'') [Fact (𝒪 i)] [Fact (𝒪 i')]
    [Fact (𝒪 i'')] (a' : X'' ⟶ X') (b' : X' ⟶ X) (h₁ : Z'' ⟶ Z') (h₂ : Z' ⟶ Z) (a : Y'' ⟶ Y')
    (b : Y' ⟶ Y) (wi₁ : a' ≫ i' = i'' ≫ h₁) (wp₁ : h₁ ≫ p' = p'' ≫ a) (wi₂ : b' ≫ i = i' ≫ h₂)
    (wp₂ : h₂ ≫ p = p' ≫ b) (wi : (a' ≫ b') ≫ i = i'' ≫ (h₁ ≫ h₂))
    (wp : (h₁ ≫ h₂) ≫ p = p'' ≫ (a ≫ b)) [IsIso (F.baseChange a' i'' i' h₁ wi₁)]
    [IsIso (F.baseChange b' i' i h₂ wi₂)]
    [IsIso (F.baseChange (a' ≫ b') i'' i (h₁ ≫ h₂) wi)] :
    F.shriekBaseChange i p i'' p'' (a' ≫ b') (h₁ ≫ h₂) (a ≫ b) wi wp =
      ((F.shriekBaseChange i p i' p' b' h₂ b wi₂ wp₂ ≫ᵥ
        F.shriekBaseChange i' p' i'' p'' a' h₁ a wi₁ wp₁).whiskerLeft
          (F.pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight (F.pbComp' a b (a ≫ b) rfl).hom := by
  have hA : inv (F.baseChange (a' ≫ b') i'' i (h₁ ≫ h₂) wi) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (inv (F.baseChange b' i' i h₂ wi₂)))
        (TwoSquare.mk _ _ _ _ (inv (F.baseChange a' i'' i' h₁ wi₁)))).whiskerLeft
          (F.pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight
            (F.pbComp' h₁ h₂ (h₁ ≫ h₂) rfl).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_paste_horiz a' b' i'' i' i h₁ h₂ (a' ≫ b') (h₁ ≫ h₂) wi₁ wi₂ rfl
      rfl wi]
    ext M
    simp [← Functor.map_comp]
  have hP := F.pfBaseChange_paste_horiz h₁ h₂ p'' p' p a b (h₁ ≫ h₂) (a ≫ b) wp₁ wp₂
    rfl rfl wp
  ext K
  simp only [shriekBaseChange, hA, hP, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc, shriek]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (F.pfBaseChange h₁ p'' p' a wp₁).naturality
    ((inv (F.baseChange b' i' i h₂ wi₂)).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [TwoSquare.mk]
  rw [← reassoc_of% hn]

/-- **Compatibility with refinements**: the compact-support exchange maps attached to two
factorizations `X ⟶[i] Z ⟶[p] Y`, `X ⟶[i₁] Z₁ ⟶[p₁] Y` (and `X' ⟶[i'] Z' ⟶[p'] Y'`,
`X' ⟶[i₁'] Z₁' ⟶[p₁'] Y'`) are intertwined by the comparisons along refinements `r : Z ⟶ Z₁` and
`r' : Z' ⟶ Z₁'` compatible with the maps `hc : Z' ⟶ Z` and `hd : Z₁' ⟶ Z₁`. -/
lemma shriekBaseChange_refinementComparison {Z₁ Z₁' : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y)
    (i₁ : X ⟶ Z₁) (p₁ : Z₁ ⟶ Y) (i' : X' ⟶ Z') (p' : Z' ⟶ Y') (i₁' : X' ⟶ Z₁')
    (p₁' : Z₁' ⟶ Y') [Fact (𝒪 i)] [Fact (𝒪 i₁)] [Fact (𝒪 i')] [Fact (𝒪 i₁')] (g' : X' ⟶ X)
    (g : Y' ⟶ Y) (r : Z ⟶ Z₁) (wr : 𝟙 X ≫ i₁ = i ≫ r) (hpr : r ≫ p₁ = p) (r' : Z' ⟶ Z₁')
    (wr' : 𝟙 X' ≫ i₁' = i' ≫ r') (hpr' : r' ≫ p₁' = p') (hc : Z' ⟶ Z)
    (wci : g' ≫ i = i' ≫ hc) (wcp : hc ≫ p = p' ≫ g) (hd : Z₁' ⟶ Z₁)
    (wdi : g' ≫ i₁ = i₁' ≫ hd) (wdp : hd ≫ p₁ = p₁' ≫ g) (hcomm : hc ≫ r = r' ≫ hd)
    [IsIso (F.baseChange (𝟙 X) i i₁ r wr)]
    [IsIso (F.baseChange (𝟙 X') i' i₁' r' wr')]
    [IsIso (F.baseChange g' i' i hc wci)]
    [IsIso (F.baseChange g' i₁' i₁ hd wdi)] :
    Functor.whiskerRight (F.refinementComparison i p i₁ p₁ r wr hpr) (F.pb g) ≫
        (F.shriekBaseChange i p i' p' g' hc g wci wcp) =
      (F.shriekBaseChange i₁ p₁ i₁' p₁' g' hd g wdi wdp) ≫
        Functor.whiskerLeft (F.pb g') (F.refinementComparison i' p' i₁' p₁' r' wr' hpr') := by
  have hir : i ≫ r = i₁ := by rw [← wr, Category.id_comp]
  have hw : g' ≫ i₁ = i' ≫ (hc ≫ r) := by rw [← hir, reassoc_of% wci]
  -- the two decompositions of the base change map of the square `g' ≫ i₁ = i' ≫ (hc ≫ r)`
  have hcube : ∀ K : F.obj X,
      (F.baseChange g' i' i hc wci).app K ≫
        (F.pb hc).map ((F.sh i).map ((F.pbId X).inv.app K) ≫
          (F.baseChange (𝟙 X) i i₁ r wr).app K) ≫
        (F.sqIso hc r' r hd hcomm).hom.app ((F.sh i₁).obj K) =
      (F.sh i').map ((F.pbId X').inv.app ((F.pb g').obj K)) ≫
        (F.baseChange (𝟙 X') i' i₁' r' wr').app ((F.pb g').obj K) ≫
        (F.pb r').map ((F.baseChange g' i₁' i₁ hd wdi).app K) := by
    intro K
    have h₁ := congr_app (F.baseChange_paste_horiz g' (𝟙 X) i' i i₁ hc r g'
      (hc ≫ r) wci wr (Category.comp_id g') rfl hw) K
    have h₂ := congr_app (F.baseChange_paste_horiz (𝟙 X') g' i' i₁' i₁ r' hd g'
      (hc ≫ r) wr' wdi (Category.id_comp g') hcomm.symm hw) K
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Functor.comp_obj] at h₁ h₂
    rw [F.pbComp'_id_right_hom_app] at h₁
    rw [F.pbComp'_id_left_hom_app] at h₂
    have hn := (F.baseChange g' i' i hc wci).naturality ((F.pbId X).inv.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [F.sqIso_eq hc r' r hd hcomm (hc ≫ r) rfl hcomm.symm]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hn, ← reassoc_of% h₁, h₂]
    simp
  -- the same identity for the inverses, transposed along `r'^* ⊣ r'_*`
  have hcore : ∀ K : F.obj X,
      (F.pb hd).map ((F.adj r).unit.app ((F.sh i₁).obj K) ≫
        (F.pf r).map (inv ((F.baseChange (𝟙 X) i i₁ r wr).app K) ≫
          (F.sh i).map ((F.pbId X).hom.app K))) ≫
        (F.pfBaseChange hc r' r hd hcomm).app ((F.sh i).obj K) ≫
        (F.pf r').map (inv ((F.baseChange g' i' i hc wci).app K)) =
      inv ((F.baseChange g' i₁' i₁ hd wdi).app K) ≫
        (F.adj r').unit.app ((F.sh i₁').obj ((F.pb g').obj K)) ≫
        (F.pf r').map (inv ((F.baseChange (𝟙 X') i' i₁' r' wr').app
          ((F.pb g').obj K)) ≫ (F.sh i').map ((F.pbId X').hom.app ((F.pb g').obj K))) := by
    intro K
    have hinv := (IsIso.inv_eq_inv (f := _) (g := _)).mpr (hcube K)
    simp only [IsIso.inv_comp, Category.assoc, ← Functor.map_inv, NatIso.inv_inv_app,
      NatIso.inv_hom_app] at hinv
    -- the transpose of the base change map of the pushforwards along `r'^* ⊣ r'_*`
    have hm : ∀ {A : F.obj Z₁} {B : F.obj Z} (z : (F.pb r).obj A ⟶ B),
        (F.pb r').map ((F.pb hd).map ((F.adj r).unit.app A ≫ (F.pf r).map z) ≫
          (F.pfBaseChange hc r' r hd hcomm).app B) ≫
          (F.adj r').counit.app ((F.pb hc).obj B) =
        (F.sqIso hc r' r hd hcomm).inv.app A ≫ (F.pb hc).map z := by
      intro A B z
      have h₁ := mateEquiv_counit (F.adj r) (F.adj r')
        (TwoSquare.mk _ _ _ _ (F.sqIso hc r' r hd hcomm).inv) B
      have h₂ := (F.sqIso hc r' r hd hcomm).inv.naturality
        ((F.adj r).unit.app A ≫ (F.pf r).map z)
      simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
      rw [Functor.map_comp, Category.assoc]
      erw [h₁, reassoc_of% h₂]
      rw [← Functor.map_comp]
      simp
    apply ((F.adj r').homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    have hm' := hm (A := (F.sh i₁).obj K) (B := (F.sh i).obj K)
      (inv ((F.baseChange (𝟙 X) i i₁ r wr).app K) ≫
        (F.sh i).map ((F.pbId X).hom.app K))
    simp only [Functor.map_comp, Category.assoc] at hm' hinv
    simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
    rw [reassoc_of% hm', hinv]
    congr 1
    erw [(F.adj r').counit_naturality_assoc,
      (F.adj r').left_triangle_components_assoc]
  ext K
  have hv := congr_app (F.pfBaseChange_paste_vert hc hd g r' r p₁' p₁ p' p hcomm
    wdp hpr' hpr wcp) ((F.sh i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj] at hv
  have hn := (F.pfBaseChange hd p₁' p₁ g wdp).naturality
    ((F.adj r).unit.app ((F.sh i₁).obj K) ≫
      (F.pf r).map (inv ((F.baseChange (𝟙 X) i i₁ r wr).app K) ≫
        (F.sh i).map ((F.pbId X).hom.app K)))
  have hn₂ := (F.pfComp' r' p₁' p' hpr').inv.naturality
    (inv ((F.baseChange g' i' i hc wci).app K))
  have hcore' := congrArg (F.pf p₁').map (hcore K)
  have hcancel : (F.pb g).map ((F.pfComp' r p₁ p hpr).inv.app ((F.sh i).obj K)) ≫
      (F.pb g).map ((F.pfComp' r p₁ p hpr).hom.app ((F.sh i).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.map_comp,
    Category.assoc] at hn hn₂ hcore' hv
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    refinementComparison_app_eq, refinementComparison_app_eq]
  simp only [shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  dsimp only [shriek, Functor.comp_obj, Functor.id_obj]
  erw [hv]
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  rw [reassoc_of% hcancel, reassoc_of% hn, ← hn₂, reassoc_of% hcore']

/-- The compact-support exchange map of factorizations with identities as open immersions is
the base change map of the pushforwards, through `(𝟙)_! ≅ 𝟭`. -/
lemma shriekBaseChange_id_left_app [𝒪.ContainsIdentities] (p : X ⟶ Y) (p' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) (wi : g' ≫ 𝟙 X = 𝟙 X' ≫ g') (wp : g' ≫ p = p' ≫ g)
    [IsIso (F.baseChange g' (𝟙 X') (𝟙 X) g' wi)] (K : F.obj X) :
    (F.shriekBaseChange (𝟙 X) p (𝟙 X') p' g' g' g wi wp).app K ≫
        (F.pf p').map ((F.shId X').hom.app ((F.pb g').obj K)) =
      (F.pb g).map ((F.pf p).map ((F.shId X).hom.app K)) ≫
        (F.pfBaseChange g' p' p g wp).app K := by
  have hb := congr_app (F.baseChange_id_vert g' wi) K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Functor.comp_obj, Functor.id_obj] at hb
  have hinv : inv ((F.baseChange g' (𝟙 X') (𝟙 X) g' wi).app K) =
      (F.pb g').map ((F.shId X).hom.app K) ≫ (F.shId X').inv.app ((F.pb g').obj K) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hb]
    simp [← Functor.map_comp_assoc]
  rw [shriekBaseChange_app, hinv]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp (F.pf p'), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact ((F.pfBaseChange g' p' p g wp).naturality ((F.shId X).hom.app K)).symm

/-- The compact-support exchange map of factorizations with identities as open immersions is
the base change map of the pushforwards, through `(𝟙)_! ≅ 𝟭`. -/
lemma shriekBaseChange_id_left [𝒪.ContainsIdentities] (p : X ⟶ Y) (p' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) (wi : g' ≫ 𝟙 X = 𝟙 X' ≫ g') (wp : g' ≫ p = p' ≫ g)
    [IsIso (F.baseChange g' (𝟙 X') (𝟙 X) g' wi)] :
    (F.shriekBaseChange (𝟙 X) p (𝟙 X') p' g' g' g wi wp) ≫
        Functor.whiskerLeft (F.pb g') (Functor.whiskerRight (F.shId X').hom (F.pf p') ≫
          (Functor.leftUnitor _).hom) =
      Functor.whiskerRight (Functor.whiskerRight (F.shId X).hom (F.pf p) ≫
          (Functor.leftUnitor _).hom) (F.pb g) ≫ (F.pfBaseChange g' p' p g wp) := by
  ext K
  have := F.shriekBaseChange_id_left_app p p' g' g wi wp K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.map_comp] at this ⊢
  erw [Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact this
end ShriekBaseChange

end CategoryTheory.ExchangeFormalism
