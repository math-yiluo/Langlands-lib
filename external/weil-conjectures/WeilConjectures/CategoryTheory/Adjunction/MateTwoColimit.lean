/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates commute with filtered 2-colimits

Let `c₁ : CategoryCocone C₁ D₁` and `c₂ : CategoryCocone C₂ D₂` be filtered 2-colimits of
directed systems of categories (`CategoryTheory.CategoryCocone.IsFilteredTwoColimit`), and let
`G i ⊣ R i` (`G i : C₁ i ⥤ C₂ i`) be adjunctions at the finite stages and `GΩ ⊣ RΩ`
(`GΩ : D₁ ⥤ D₂`) an adjunction on the vertices. Suppose the left adjoints are compatible with
the cocones, through isomorphisms `α i : G i ⋙ c₂.Φ i ≅ c₁.Φ i ⋙ GΩ` and
`αT h : G i ⋙ c₂.T h ≅ c₁.T h ⋙ G j`, satisfying a cocycle condition relating `α i`, `α j`,
`αT h` and the structure isomorphisms of the cocones. The squares are
```
  C₁ i --G i--> C₂ i        C₁ i --G i--> C₂ i
   |             |            |             |
  c₁.Φ i       c₂.Φ i       c₁.T h        c₂.T h
   v             v            v             v
   D₁  --GΩ-->   D₂         C₁ j --G j--> C₂ j
```

The main result, `CategoryTheory.CategoryCocone.isIso_mateEquiv_of_isFilteredTwoColimit`, says
that if the mates `R i ⋙ c₁.T h ⟶ c₂.T h ⋙ R j` of the transition squares `αT h` are
isomorphisms, then so are the mates `R i ⋙ c₁.Φ i ⟶ c₂.Φ i ⋙ RΩ` of the squares `α i`: the right
adjoints commute with passage to the 2-colimit as soon as they commute with the transitions.

## Proof sketch

Write `β i` for the mate of `α i` and `m h` for the mate of `αT h`.
* `iso_hom_app_comp_mateEquiv_app`: by the cocycle condition, `β i` agrees, up to the structure
  isomorphisms of the cocones, with `c₁.Φ j` applied to `m h`, followed by `β j`.
* `exists_comp_mateEquiv_app_eq`: every morphism `d ⟶ RΩ ((c₂.Φ i) k)` factors through
  `β i`; reduce to `d = (c₁.Φ j) x`, transpose along `GΩ ⊣ RΩ`, descend the transpose to a
  finite stage with `c₂.HomSurj`, transpose back along `G l ⊣ R l` and correct by `(m h)⁻¹`.
* `map_eq_map_of_map_comp_mateEquiv_eq`: `β l` is "injective" on morphisms coming from the
  stage `l`, using `c₂.HomInj` and the invertibility of the `m h`.
* The section `s` of `β i` obtained from the first point is a two-sided inverse: `β i ≫ s` comes
  from a finite stage by `c₁.HomSurj`, and the second point shows it is the identity.
-/


public section

namespace CategoryTheory.CategoryCocone

open _root_.CategoryTheory.Functor

variable {I : Type*} [Preorder I]
  {C₁ C₂ : I → Type*} [∀ i, Category (C₁ i)] [∀ i, Category (C₂ i)]
  {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  {c₁ : CategoryCocone C₁ D₁} {c₂ : CategoryCocone C₂ D₂}
  {G : ∀ i, C₁ i ⥤ C₂ i} {R : ∀ i, C₂ i ⥤ C₁ i} (adj : ∀ i, G i ⊣ R i)
  {GΩ : D₁ ⥤ D₂} {RΩ : D₂ ⥤ D₁} (adjΩ : GΩ ⊣ RΩ)
  (α : ∀ i, G i ⋙ c₂.Φ i ≅ c₁.Φ i ⋙ GΩ)
  (αT : ∀ ⦃i j⦄ (h : i ≤ j), G i ⋙ c₂.T h ≅ c₁.T h ⋙ G j)

/-- `mateEquiv_counit` for a 2-square given by a natural transformation, stated with
`TwoSquare.natTrans` so that both sides are well typed as natural transformations. -/
@[reassoc]
lemma _root_.CategoryTheory.map_mateEquiv_mk_natTrans_app_comp_counit {A B C' D' : Type*}
    [Category A] [Category B] [Category C'] [Category D'] {G' : A ⥤ C'} {H : B ⥤ D'}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C' ⥤ D'} {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : G' ⋙ L₂ ⟶ L₁ ⋙ H) (d : B) :
    L₂.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e)).app d) ≫
        adj₂.counit.app (H.obj d) =
      e.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) :=
  mateEquiv_counit adj₁ adj₂ _ d

/-- The cocycle condition, solved for `GΩ.map (c₁.iso h).hom ≫ (α i).inv`. -/
@[reassoc]
lemma map_iso_hom_app_comp_inv_app
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    {i j : I} (h : i ≤ j) (X : C₁ i) :
    GΩ.map ((c₁.iso h).hom.app X) ≫ (α i).inv.app X =
      (α j).inv.app ((c₁.T h).obj X) ≫ (c₂.Φ j).map ((αT h).inv.app X) ≫
        (c₂.iso h).hom.app ((G i).obj X) := by
  rw [← Iso.app_inv, Iso.comp_inv_eq, Iso.app_hom, hcocycle h X]
  simp only [Category.assoc, Functor.comp_obj, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- The mate of `α i`, transported along the structure isomorphism `c₁.iso h`, factors as the
image under `c₁.Φ j` of the mate of `αT h`, followed by the mate of `α j` and the structure
isomorphism `c₂.iso h`. -/
lemma iso_hom_app_comp_mateEquiv_app
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    {i j : I} (h : i ≤ j) (k : C₂ i) :
    (c₁.iso h).hom.app ((R i).obj k) ≫
        (mateEquiv (adj i) adjΩ (TwoSquare.mk _ _ _ _ (α i).inv)).app k =
      (c₁.Φ j).map ((mateEquiv (adj i) (adj j)
          (TwoSquare.mk _ _ _ _ (αT h).inv)).app k) ≫
        (mateEquiv (adj j) adjΩ (TwoSquare.mk _ _ _ _ (α j).inv)).app
          ((c₂.T h).obj k) ≫
        RΩ.map ((c₂.iso h).hom.app k) := by
  apply (adjΩ.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [map_mateEquiv_mk_natTrans_app_comp_counit, Adjunction.counit_naturality,
    map_mateEquiv_mk_natTrans_app_comp_counit_assoc,
    map_iso_hom_app_comp_inv_app_assoc α αT hcocycle, ← Functor.comp_map (c₁.Φ j) GΩ]
  erw [(α j).inv.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp_assoc,
    map_mateEquiv_mk_natTrans_app_comp_counit]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg _ (congrArg _ ((c₂.iso h).hom.naturality _).symm)

/-- The adjoint transpose of `G'.map v ≫ mate.app d` along the target adjunction. -/
lemma _root_.CategoryTheory.homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app
    {A B C' D' : Type*}
    [Category A] [Category B] [Category C'] [Category D'] {G' : A ⥤ C'} {H : B ⥤ D'}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C' ⥤ D'} {R₂ : D' ⥤ C'} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : G' ⋙ L₂ ⟶ L₁ ⋙ H) {X : A} {d : B} (v : X ⟶ R₁.obj d) :
    (adj₂.homEquiv _ _).symm
        (G'.map v ≫ (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e)).app d) =
      e.app X ≫ H.map ((adj₁.homEquiv _ _).symm v) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    map_mateEquiv_mk_natTrans_app_comp_counit, ← Functor.comp_map]
  erw [e.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp, Adjunction.homEquiv_counit]

/-- Two morphisms `v₁ v₂ : X ⟶ (R l).obj z` at the stage `l` whose images under `c₁.Φ l` become
equal after composing with the mate of `α l` already have equal images under `c₁.Φ l`, provided
`c₂` satisfies (Hom) injectivity and the transition mates are isomorphisms. -/
lemma map_eq_map_of_map_comp_mateEquiv_eq (hc₂ : c₂.HomInj)
    (hT : ∀ ⦃i j⦄ (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (αT h).inv)))
    {l : I} {X : C₁ l} {z : C₂ l} (v₁ v₂ : X ⟶ (R l).obj z)
    (hv : (c₁.Φ l).map v₁ ≫
        (mateEquiv (adj l) adjΩ (TwoSquare.mk _ _ _ _ (α l).inv)).app z =
      (c₁.Φ l).map v₂ ≫
        (mateEquiv (adj l) adjΩ (TwoSquare.mk _ _ _ _ (α l).inv)).app z) :
    (c₁.Φ l).map v₁ = (c₁.Φ l).map v₂ := by
  have hv' := congrArg (adjΩ.homEquiv _ _).symm hv
  rw [homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app,
    homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app, cancel_epi] at hv'
  obtain ⟨l', h, hl'⟩ := hc₂ l _ _ _ _ hv'
  have := hT h
  have hT₁ : (c₁.T h).map v₁ = (c₁.T h).map v₂ := by
    rw [← cancel_mono ((mateEquiv (adj l) (adj l')
      (TwoSquare.mk _ _ _ _ (αT h).inv)).app z)]
    apply ((adj l').homEquiv _ _).symm.injective
    rw [homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app,
      homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app, hl']
  rw [← cancel_epi ((c₁.iso h).hom.app X), ← (c₁.iso h).hom.naturality,
    ← (c₁.iso h).hom.naturality, Functor.comp_map, Functor.comp_map, hT₁]

/-- Every morphism `(c₁.Φ j).obj x ⟶ RΩ.obj ((c₂.Φ j).obj y)` factors through the mate of `α j`,
provided `c₂` satisfies (Hom) surjectivity and the transition mates are isomorphisms. -/
lemma exists_comp_mateEquiv_app_eq_of_stage
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    (hc₂ : c₂.HomSurj)
    (hT : ∀ ⦃i j⦄ (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (αT h).inv)))
    {j : I} (x : C₁ j) (y : C₂ j) (f : (c₁.Φ j).obj x ⟶ RΩ.obj ((c₂.Φ j).obj y)) :
    ∃ f₀ : (c₁.Φ j).obj x ⟶ (c₁.Φ j).obj ((R j).obj y),
      f₀ ≫ (mateEquiv (adj j) adjΩ (TwoSquare.mk _ _ _ _ (α j).inv)).app y = f := by
  obtain ⟨l, h, h', u, hu⟩ :=
    hc₂ j j ((G j).obj x) y ((α j).hom.app x ≫ (adjΩ.homEquiv _ _).symm f)
  have := hT h
  refine ⟨(c₁.iso h).inv.app x ≫
    (c₁.Φ l).map ((adj l).homEquiv _ _ ((αT h).inv.app x ≫ u)) ≫
    inv ((c₁.Φ l).map ((mateEquiv (adj j) (adj l)
      (TwoSquare.mk _ _ _ _ (αT h).inv)).app y)) ≫
    (c₁.iso h).hom.app ((R j).obj y), (adjΩ.homEquiv _ _).symm.injective ?_⟩
  rw [Category.assoc, Category.assoc, Category.assoc,
    iso_hom_app_comp_mateEquiv_app adj adjΩ α αT hcocycle, IsIso.inv_hom_id_assoc,
    ← Category.assoc, ← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Category.assoc, Adjunction.homEquiv_naturality_left_symm]
  erw [homEquiv_symm_map_comp_mateEquiv_mk_natTrans_app]
  rw [Equiv.symm_apply_apply,
    ← Iso.inv_hom_id_app_assoc (α j) x ((adjΩ.homEquiv _ _).symm f), hu,
    ← cancel_epi (GΩ.map ((c₁.iso h).hom.app x)),
    map_iso_hom_app_comp_inv_app_assoc α αT hcocycle]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

/-- Every morphism `d ⟶ RΩ.obj ((c₂.Φ i).obj k)` factors through the mate of `α i`. -/
lemma exists_comp_mateEquiv_app_eq [IsDirected I (· ≤ ·)]
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    (hc₁ : c₁.EssSurjObj) (hc₂ : c₂.HomSurj)
    (hT : ∀ ⦃i j⦄ (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (αT h).inv)))
    {i : I} (k : C₂ i) {d : D₁} (f : d ⟶ RΩ.obj ((c₂.Φ i).obj k)) :
    ∃ f₀ : d ⟶ (c₁.Φ i).obj ((R i).obj k),
      f₀ ≫ (mateEquiv (adj i) adjΩ (TwoSquare.mk _ _ _ _ (α i).inv)).app k = f := by
  obtain ⟨j₀, x₀, ⟨e⟩⟩ := hc₁ d
  obtain ⟨j, hij, hj₀⟩ := directed_of (· ≤ ·) i j₀
  obtain ⟨f₀, hf₀⟩ := exists_comp_mateEquiv_app_eq_of_stage adj adjΩ α αT hcocycle hc₂ hT
    ((c₁.T hj₀).obj x₀) ((c₂.T hij).obj k)
    ((c₁.iso hj₀).hom.app x₀ ≫ e.hom ≫ f ≫ RΩ.map ((c₂.iso hij).inv.app k))
  have := hT hij
  refine ⟨e.inv ≫ (c₁.iso hj₀).inv.app x₀ ≫ f₀ ≫ inv ((c₁.Φ j).map ((mateEquiv (adj i) (adj j)
    (TwoSquare.mk _ _ _ _ (αT hij).inv)).app k)) ≫ (c₁.iso hij).hom.app ((R i).obj k), ?_⟩
  simp only [Category.assoc]
  rw [iso_hom_app_comp_mateEquiv_app adj adjΩ α αT hcocycle, IsIso.inv_hom_id_assoc,
    reassoc_of% hf₀]
  simp [← Functor.map_comp]

/-- The components of the mate of `α i` are isomorphisms. -/
lemma isIso_mateEquiv_app_of_isFilteredTwoColimit [IsDirected I (· ≤ ·)]
    (hc₁ : c₁.IsFilteredTwoColimit) (hc₂ : c₂.IsFilteredTwoColimit)
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    (hT : ∀ ⦃i j⦄ (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (αT h).inv)))
    {i : I} (k : C₂ i) :
    IsIso ((mateEquiv (adj i) adjΩ (TwoSquare.mk _ _ _ _ (α i).inv)).app k) := by
  obtain ⟨s, hs⟩ := exists_comp_mateEquiv_app_eq adj adjΩ α αT hcocycle hc₁.essSurjObj
    hc₂.homSurj hT k (𝟙 _)
  obtain ⟨l, h, h', w, hw⟩ := hc₁.homSurj i i _ _
    ((mateEquiv (adj i) adjΩ (TwoSquare.mk _ _ _ _ (α i).inv)).app k ≫ s)
  have := hT h
  have hm : (c₁.Φ l).map (w ≫ (mateEquiv (adj i) (adj l)
        (TwoSquare.mk _ _ _ _ (αT h).inv)).app k) =
      (c₁.Φ l).map ((mateEquiv (adj i) (adj l)
        (TwoSquare.mk _ _ _ _ (αT h).inv)).app k) := by
    apply map_eq_map_of_map_comp_mateEquiv_eq adj adjΩ α αT hc₂.homInj hT
    rw [← cancel_epi ((c₁.iso h).inv.app _), ← cancel_mono (RΩ.map ((c₂.iso h).hom.app k))]
    simp only [Category.assoc, Functor.map_comp]
    rw [← iso_hom_app_comp_mateEquiv_app adj adjΩ α αT hcocycle h, ← reassoc_of% hw, hs]
    simp
  have hw₁ : (c₁.Φ l).map w = 𝟙 _ := by
    rw [← cancel_mono ((c₁.Φ l).map ((mateEquiv (adj i) (adj l)
      (TwoSquare.mk _ _ _ _ (αT h).inv)).app k)), ← Functor.map_comp, hm,
      Category.id_comp]
  refine ⟨⟨s, ?_, hs⟩⟩
  rw [hw, hw₁]
  simp

/-- **Mates commute with filtered 2-colimits.** If the right adjoints `R i` commute with the
transition functors, in the sense that the mates of the squares `αT h` are isomorphisms, then
the mate `R i ⋙ c₁.Φ i ⟶ c₂.Φ i ⋙ RΩ` of the square `α i` is an isomorphism. -/
theorem isIso_mateEquiv_of_isFilteredTwoColimit [IsDirected I (· ≤ ·)]
    (hc₁ : c₁.IsFilteredTwoColimit) (hc₂ : c₂.IsFilteredTwoColimit)
    (hcocycle : ∀ ⦃i j⦄ (h : i ≤ j) (X : C₁ i),
      (α i).hom.app X = (c₂.iso h).inv.app ((G i).obj X) ≫ (c₂.Φ j).map ((αT h).hom.app X) ≫
        (α j).hom.app ((c₁.T h).obj X) ≫ GΩ.map ((c₁.iso h).hom.app X))
    (hT : ∀ ⦃i j⦄ (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (αT h).inv)))
    (i : I) :
    IsIso (mateEquiv (adj i) adjΩ (TwoSquare.mk _ _ _ _ (α i).inv)) := by
  have (k : C₂ i) := isIso_mateEquiv_app_of_isFilteredTwoColimit adj adjΩ α αT hc₁ hc₂
    hcocycle hT k
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.CategoryCocone

