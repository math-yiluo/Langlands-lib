import Langlands.CategoryTheory.Sites.PseudofunctorParallelIsomorphisms
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Gluing along commuting squares for category-valued pseudofunctors -/

universe v v' u u' v₂ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Bicategory Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

namespace Langlands.CategoryTheory.PseudofunctorSquareGluing

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

lemma toLoc_comp {X Y Z : C} {x : Y ⟶ X} {g : Z ⟶ Y} {gx : Z ⟶ X} (h : g ≫ x = gx) :
    x.op.toLoc ≫ g.op.toLoc = gx.op.toLoc := by
  subst h
  rfl

section Coherence

variable {F}

/-- Associativity of the composition comparisons, in the form used to conjugate
morphisms between pulled-back objects. -/
@[reassoc]
lemma mapComp'_hom_app_map_inv_app {W X Y Z : C} (a : X ⟶ W) (j : Y ⟶ X) (i : Z ⟶ Y)
    (a₁ : Y ⟶ W) (c : Z ⟶ X) (d : Z ⟶ W) (h₁ : j ≫ a = a₁) (hc : i ≫ j = c)
    (hd : i ≫ a₁ = d) (M : F.obj (.mk (op W))) :
    (F.mapComp' j.op.toLoc i.op.toLoc c.op.toLoc (toLoc_comp hc)).hom.toNatTrans.app
        ((F.map a.op.toLoc).toFunctor.obj M) ≫
      (F.map i.op.toLoc).toFunctor.map
        ((F.mapComp' a.op.toLoc j.op.toLoc a₁.op.toLoc (toLoc_comp h₁)).inv.toNatTrans.app M) =
    (F.mapComp' a.op.toLoc c.op.toLoc d.op.toLoc
        (toLoc_comp (by rw [← hd, ← h₁, ← hc, Category.assoc]))).inv.toNatTrans.app M ≫
      (F.mapComp' a₁.op.toLoc i.op.toLoc d.op.toLoc (toLoc_comp hd)).hom.toNatTrans.app M := by
  have h := F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app a.op.toLoc j.op.toLoc i.op.toLoc
    a₁.op.toLoc c.op.toLoc d.op.toLoc (toLoc_comp h₁) (toLoc_comp hc) (toLoc_comp hd) M
  rw [← cancel_epi ((F.mapComp' a₁.op.toLoc i.op.toLoc d.op.toLoc
    (toLoc_comp hd)).inv.toNatTrans.app M ≫ (F.mapComp' a.op.toLoc c.op.toLoc d.op.toLoc
        (toLoc_comp (by rw [← hd, ← h₁, ← hc, Category.assoc]))).hom.toNatTrans.app M)]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [Cat.Hom.inv_hom_id_toNatTrans_app_assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app]
  rw [← Functor.map_comp, Cat.Hom.hom_inv_id_toNatTrans_app]
  exact (F.map i.op.toLoc).toFunctor.map_id _

/-- The inverse form of `mapComp'_hom_app_map_inv_app`. -/
@[reassoc]
lemma map_hom_app_mapComp'_inv_app {W X Y Z : C} (a : X ⟶ W) (j : Y ⟶ X) (i : Z ⟶ Y)
    (a₁ : Y ⟶ W) (c : Z ⟶ X) (d : Z ⟶ W) (h₁ : j ≫ a = a₁) (hc : i ≫ j = c)
    (hd : i ≫ a₁ = d) (M : F.obj (.mk (op W))) :
    (F.map i.op.toLoc).toFunctor.map
        ((F.mapComp' a.op.toLoc j.op.toLoc a₁.op.toLoc (toLoc_comp h₁)).hom.toNatTrans.app M) ≫
      (F.mapComp' j.op.toLoc i.op.toLoc c.op.toLoc (toLoc_comp hc)).inv.toNatTrans.app
        ((F.map a.op.toLoc).toFunctor.obj M) =
    (F.mapComp' a₁.op.toLoc i.op.toLoc d.op.toLoc (toLoc_comp hd)).inv.toNatTrans.app M ≫
      (F.mapComp' a.op.toLoc c.op.toLoc d.op.toLoc
        (toLoc_comp (by rw [← hd, ← h₁, ← hc, Category.assoc]))).hom.toNatTrans.app M :=
  (F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app a.op.toLoc j.op.toLoc i.op.toLoc
    a₁.op.toLoc c.op.toLoc d.op.toLoc (toLoc_comp h₁) (toLoc_comp hc) (toLoc_comp hd) M).symm

/-- Conjugating a morphism by composition comparisons commutes with `pullHom`. -/
lemma pullHom_conj {V V' X Y Z : C} {M : F.obj (.mk (op V))} {M' : F.obj (.mk (op V'))}
    (a : X ⟶ V) (a' : X ⟶ V') (j : Y ⟶ X) (i : Z ⟶ Y) (a₁ : Y ⟶ V) (a₁' : Y ⟶ V')
    (c : Z ⟶ X) (d : Z ⟶ V) (d' : Z ⟶ V')
    (h₁ : j ≫ a = a₁) (h₁' : j ≫ a' = a₁') (hc : i ≫ j = c) (hd : i ≫ a₁ = d)
    (hd' : i ≫ a₁' = d')
    (φ : (F.map a₁.op.toLoc).toFunctor.obj M ⟶ (F.map a₁'.op.toLoc).toFunctor.obj M') :
    pullHom (M₁ := (F.map a.op.toLoc).toFunctor.obj M)
      (M₂ := (F.map a'.op.toLoc).toFunctor.obj M') (f₁ := j) (f₂ := j)
      ((F.mapComp' a.op.toLoc j.op.toLoc a₁.op.toLoc (toLoc_comp h₁)).inv.toNatTrans.app M ≫
        φ ≫ (F.mapComp' a'.op.toLoc j.op.toLoc a₁'.op.toLoc
          (toLoc_comp h₁')).hom.toNatTrans.app M') i c c hc hc =
      (F.mapComp' a.op.toLoc c.op.toLoc d.op.toLoc
          (toLoc_comp (by rw [← hd, ← h₁, ← hc, Category.assoc]))).inv.toNatTrans.app M ≫
        pullHom φ i d d' hd hd' ≫
        (F.mapComp' a'.op.toLoc c.op.toLoc d'.op.toLoc
          (toLoc_comp (by rw [← hd', ← h₁', ← hc, Category.assoc]))).hom.toNatTrans.app M' := by
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [mapComp'_hom_app_map_inv_app_assoc a j i a₁ c d h₁ hc hd M,
    map_hom_app_mapComp'_inv_app a' j i a₁' c d' h₁' hc hd' M']

/-- A morphism between pulled-back objects is determined by its `pullHom` along a map. -/
lemma map_eq_iff_pullHom_eq {V V' X Y : C} {M : F.obj (.mk (op V))} {M' : F.obj (.mk (op V'))}
    (a : X ⟶ V) (a' : X ⟶ V') (j : Y ⟶ X) (a₁ : Y ⟶ V) (a₁' : Y ⟶ V')
    (h₁ : j ≫ a = a₁) (h₁' : j ≫ a' = a₁')
    (φ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map a'.op.toLoc).toFunctor.obj M')
    (φ₁ : (F.map a₁.op.toLoc).toFunctor.obj M ⟶ (F.map a₁'.op.toLoc).toFunctor.obj M') :
    (F.map j.op.toLoc).toFunctor.map φ =
        (F.mapComp' a.op.toLoc j.op.toLoc a₁.op.toLoc (toLoc_comp h₁)).inv.toNatTrans.app M ≫
          φ₁ ≫ (F.mapComp' a'.op.toLoc j.op.toLoc a₁'.op.toLoc
            (toLoc_comp h₁')).hom.toNatTrans.app M' ↔
      pullHom φ j a₁ a₁' h₁ h₁' = φ₁ := by
  rw [map_eq_pullHom φ j a₁ a₁' h₁ h₁']
  constructor
  · intro h
    simpa using
      congrArg (fun t ↦ (F.mapComp' a.op.toLoc j.op.toLoc a₁.op.toLoc
        (toLoc_comp h₁)).hom.toNatTrans.app M ≫ t ≫ (F.mapComp' a'.op.toLoc j.op.toLoc
          a₁'.op.toLoc (toLoc_comp h₁')).inv.toNatTrans.app M') h
  · intro h
    rw [h]

end Coherence

section Square

variable {X₀ X₁ X₂ X : C} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X} {j₂ : X₂ ⟶ X}

/-- The canonical isomorphism between the two restrictions of an object over the total
corner of a commuting square to its initial corner. -/
def squareIso (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Z : F.obj (.mk (op X))) :
    (F.map i₁.op.toLoc).toFunctor.obj ((F.map j₁.op.toLoc).toFunctor.obj Z) ≅
      (F.map i₂.op.toLoc).toFunctor.obj ((F.map j₂.op.toLoc).toFunctor.obj Z) :=
  ((Cat.Hom.toNatIso (F.mapComp' j₁.op.toLoc i₁.op.toLoc (i₁ ≫ j₁).op.toLoc
    (toLoc_comp rfl))).app Z).symm ≪≫
    (Cat.Hom.toNatIso (F.mapComp' j₂.op.toLoc i₂.op.toLoc (i₁ ≫ j₁).op.toLoc
      (toLoc_comp w.symm))).app Z

/-- `squareIso` may be computed through any name for the diagonal of the square. -/
lemma squareIso_eq (w : i₁ ≫ j₁ = i₂ ≫ j₂) (c : X₀ ⟶ X) (h₁ : i₁ ≫ j₁ = c)
    (h₂ : i₂ ≫ j₂ = c) (Z : F.obj (.mk (op X))) :
    squareIso F w Z =
      ((Cat.Hom.toNatIso (F.mapComp' j₁.op.toLoc i₁.op.toLoc c.op.toLoc
        (toLoc_comp h₁))).app Z).symm ≪≫
        (Cat.Hom.toNatIso (F.mapComp' j₂.op.toLoc i₂.op.toLoc c.op.toLoc
          (toLoc_comp h₂))).app Z := by
  subst h₁
  rfl

/-- Objects glue along the square: every object on each of the two middle corners,
together with an isomorphism of their restrictions to the initial corner, comes from an
object on the total corner, compatibly with the given isomorphism. -/
def IsSquareEffective (w : i₁ ≫ j₁ = i₂ ≫ j₂) : Prop :=
  ∀ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂)))
    (e : (F.map i₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map i₂.op.toLoc).toFunctor.obj M₂),
    ∃ (Z : F.obj (.mk (op X))) (e₁ : (F.map j₁.op.toLoc).toFunctor.obj Z ≅ M₁)
      (e₂ : (F.map j₂.op.toLoc).toFunctor.obj Z ≅ M₂),
      squareIso F w Z ≪≫ (F.map i₂.op.toLoc).toFunctor.mapIso e₂ =
        (F.map i₁.op.toLoc).toFunctor.mapIso e₁ ≪≫ e

/-- Morphisms glue uniquely along the square: two morphisms on the middle corners whose
restrictions to the initial corner agree through `squareIso` come from exactly one
morphism on the total corner. -/
def IsSquareHomGluing (w : i₁ ≫ j₁ = i₂ ≫ j₂) : Prop :=
  ∀ (Z Z' : F.obj (.mk (op X)))
    (φ₁ : (F.map j₁.op.toLoc).toFunctor.obj Z ⟶ (F.map j₁.op.toLoc).toFunctor.obj Z')
    (φ₂ : (F.map j₂.op.toLoc).toFunctor.obj Z ⟶ (F.map j₂.op.toLoc).toFunctor.obj Z'),
    (F.map i₁.op.toLoc).toFunctor.map φ₁ ≫ (squareIso F w Z').hom =
        (squareIso F w Z).hom ≫ (F.map i₂.op.toLoc).toFunctor.map φ₂ →
      ∃! φ : Z ⟶ Z', (F.map j₁.op.toLoc).toFunctor.map φ = φ₁ ∧
        (F.map j₂.op.toLoc).toFunctor.map φ = φ₂

variable {F}

/-- The compatibility condition of two morphisms on a square, in terms of `pullHom`. -/
lemma squareIso_comm_iff (w : i₁ ≫ j₁ = i₂ ≫ j₂) {Z Z' : F.obj (.mk (op X))}
    (φ₁ : (F.map j₁.op.toLoc).toFunctor.obj Z ⟶ (F.map j₁.op.toLoc).toFunctor.obj Z')
    (φ₂ : (F.map j₂.op.toLoc).toFunctor.obj Z ⟶ (F.map j₂.op.toLoc).toFunctor.obj Z') :
    (F.map i₁.op.toLoc).toFunctor.map φ₁ ≫ (squareIso F w Z').hom =
        (squareIso F w Z).hom ≫ (F.map i₂.op.toLoc).toFunctor.map φ₂ ↔
      pullHom φ₁ i₁ (i₁ ≫ j₁) (i₁ ≫ j₁) rfl rfl =
        pullHom φ₂ i₂ (i₁ ≫ j₁) (i₁ ≫ j₁) w.symm w.symm := by
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, pullHom]
  constructor
  · intro h
    simp only [Category.assoc] at h
    rw [← cancel_mono ((F.mapComp' j₂.op.toLoc i₂.op.toLoc (i₁ ≫ j₁).op.toLoc
      (toLoc_comp w.symm)).hom.toNatTrans.app Z')]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
    rw [h]
    simp
  · intro h
    rw [← cancel_epi ((F.mapComp' j₁.op.toLoc i₁.op.toLoc (i₁ ≫ j₁).op.toLoc
      (toLoc_comp rfl)).hom.toNatTrans.app Z)]
    simp only [Category.assoc]
    rw [reassoc_of% h]
    simp

/-- Unique gluing of morphisms between pullbacks of objects along maps from the total
corner of the square. -/
lemma IsSquareHomGluing.existsUnique_pullHom {w : i₁ ≫ j₁ = i₂ ≫ j₂}
    (hG : IsSquareHomGluing F w) {V V' : C}
    (M : F.obj (.mk (op V))) (M' : F.obj (.mk (op V'))) (a : X ⟶ V) (a' : X ⟶ V')
    (a₁ : X₁ ⟶ V) (a₁' : X₁ ⟶ V') (a₂ : X₂ ⟶ V) (a₂' : X₂ ⟶ V') (d : X₀ ⟶ V) (d' : X₀ ⟶ V')
    (h₁ : j₁ ≫ a = a₁) (h₁' : j₁ ≫ a' = a₁') (h₂ : j₂ ≫ a = a₂) (h₂' : j₂ ≫ a' = a₂')
    (hd₁ : i₁ ≫ a₁ = d) (hd₁' : i₁ ≫ a₁' = d') (hd₂ : i₂ ≫ a₂ = d) (hd₂' : i₂ ≫ a₂' = d')
    (φ₁ : (F.map a₁.op.toLoc).toFunctor.obj M ⟶ (F.map a₁'.op.toLoc).toFunctor.obj M')
    (φ₂ : (F.map a₂.op.toLoc).toFunctor.obj M ⟶ (F.map a₂'.op.toLoc).toFunctor.obj M')
    (h : pullHom φ₁ i₁ d d' hd₁ hd₁' = pullHom φ₂ i₂ d d' hd₂ hd₂') :
    ∃! φ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map a'.op.toLoc).toFunctor.obj M',
      pullHom φ j₁ a₁ a₁' h₁ h₁' = φ₁ ∧ pullHom φ j₂ a₂ a₂' h₂ h₂' = φ₂ := by
  have hc : (i₁ ≫ j₁) ≫ a = d := by rw [Category.assoc, h₁, hd₁]
  have hc' : (i₁ ≫ j₁) ≫ a' = d' := by rw [Category.assoc, h₁', hd₁']
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, hφ⟩ := hG _ _
    ((F.mapComp' a.op.toLoc j₁.op.toLoc a₁.op.toLoc (toLoc_comp h₁)).inv.toNatTrans.app M ≫
      φ₁ ≫ (F.mapComp' a'.op.toLoc j₁.op.toLoc a₁'.op.toLoc
        (toLoc_comp h₁')).hom.toNatTrans.app M')
    ((F.mapComp' a.op.toLoc j₂.op.toLoc a₂.op.toLoc (toLoc_comp h₂)).inv.toNatTrans.app M ≫
      φ₂ ≫ (F.mapComp' a'.op.toLoc j₂.op.toLoc a₂'.op.toLoc
        (toLoc_comp h₂')).hom.toNatTrans.app M') (by
      rw [squareIso_comm_iff, pullHom_conj a a' j₁ i₁ a₁ a₁' (i₁ ≫ j₁) d d' h₁ h₁' rfl hd₁ hd₁',
        pullHom_conj a a' j₂ i₂ a₂ a₂' (i₁ ≫ j₁) d d' h₂ h₂' w.symm hd₂ hd₂', h])
  refine ⟨φ, ⟨(map_eq_iff_pullHom_eq a a' j₁ a₁ a₁' h₁ h₁' φ φ₁).mp hφ₁,
    (map_eq_iff_pullHom_eq a a' j₂ a₂ a₂' h₂ h₂' φ φ₂).mp hφ₂⟩, ?_⟩
  rintro ψ ⟨hψ₁, hψ₂⟩
  exact hφ ψ ⟨(map_eq_iff_pullHom_eq a a' j₁ a₁ a₁' h₁ h₁' ψ φ₁).mpr hψ₁,
    (map_eq_iff_pullHom_eq a a' j₂ a₂ a₂' h₂ h₂' ψ φ₂).mpr hψ₂⟩

/-- Effectivity data on a square, rewritten with `pullIso` when both glued objects are
themselves pullbacks. -/
lemma pullIso_symm_trans_pullIso_of_effective (w : i₁ ≫ j₁ = i₂ ≫ j₂)
    {V₁ V₂ : C} {N₁ : F.obj (.mk (op V₁))} {N₂ : F.obj (.mk (op V₂))}
    (f₁ : X₁ ⟶ V₁) (f₂ : X₂ ⟶ V₂) (d₁ : X₀ ⟶ V₁) (d₂ : X₀ ⟶ V₂)
    (hd₁ : i₁ ≫ f₁ = d₁) (hd₂ : i₂ ≫ f₂ = d₂) (Z : F.obj (.mk (op X)))
    (e₁ : (F.map j₁.op.toLoc).toFunctor.obj Z ≅ (F.map f₁.op.toLoc).toFunctor.obj N₁)
    (e₂ : (F.map j₂.op.toLoc).toFunctor.obj Z ≅ (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (e : (F.map i₁.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj N₁) ≅
      (F.map i₂.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj N₂))
    (he : squareIso F w Z ≪≫ (F.map i₂.op.toLoc).toFunctor.mapIso e₂ =
      (F.map i₁.op.toLoc).toFunctor.mapIso e₁ ≪≫ e) :
    (Cat.Hom.toNatIso (F.mapComp' f₁.op.toLoc i₁.op.toLoc d₁.op.toLoc
        (toLoc_comp hd₁))).app N₁ ≪≫ e ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc i₂.op.toLoc d₂.op.toLoc
        (toLoc_comp hd₂))).app N₂).symm =
      (pullIso e₁ i₁ (i₁ ≫ j₁) d₁ rfl hd₁).symm ≪≫ pullIso e₂ i₂ (i₁ ≫ j₁) d₂ w.symm hd₂ := by
  have he' : e.hom = (F.map i₁.op.toLoc).toFunctor.map e₁.inv ≫ (squareIso F w Z).hom ≫
      (F.map i₂.op.toLoc).toFunctor.map e₂.hom := by
    have := congrArg Iso.hom he
    simp only [Iso.trans_hom, Functor.mapIso_hom] at this
    rw [this, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom,
    Cat.Hom.toNatIso_inv, he', squareIso, pullIso, Iso.trans_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc, Iso.symm_inv]

end Square

section Composition

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (P : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{w₁, w₂})

set_option backward.isDefEq.respectTransparency false in
/-- The composition comparisons of a pseudofunctor precomposed with a functor are those of
the pseudofunctor at the images. -/
lemma comp_mapComp' {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf) :
    (G.op.toPseudofunctor.comp P).mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (toLoc_comp h) =
      P.mapComp' (G.map f).op.toLoc (G.map g).op.toLoc (G.map gf).op.toLoc
        (toLoc_comp (by rw [← h, G.map_comp])) := by
  subst h
  simp only [Pseudofunctor.mapComp', Pseudofunctor.comp_mapComp]
  ext
  simp [PrelaxFunctor.map₂_eqToHom, Functor.toPseudofunctor_mapComp, Quiver.Hom.toLoc]
  erw [Category.id_comp]
  rfl

/-- The overlap isomorphism of a pseudofunctor precomposed with a functor is that of the
pseudofunctor on the image square. -/
lemma squareIso_comp {X₀ X₁ X₂ X : C} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ X}
    {j₂ : X₂ ⟶ X} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Z : P.obj (.mk (op (G.obj X)))) :
    squareIso (G.op.toPseudofunctor.comp P) w Z =
      squareIso P (by rw [← G.map_comp, ← G.map_comp, w] :
        G.map i₁ ≫ G.map j₁ = G.map i₂ ≫ G.map j₂) Z := by
  rw [squareIso_eq P _ (G.map (i₁ ≫ j₁)) (G.map_comp _ _).symm
    (by rw [← G.map_comp, w])]
  apply Iso.ext
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Cat.Hom.toNatIso_inv, Cat.Hom.toNatIso_hom]
  rw [comp_mapComp' G P j₁ i₁ (i₁ ≫ j₁) rfl, comp_mapComp' G P j₂ i₂ (i₁ ≫ j₁) w.symm]
  rfl

end Composition

section Points

variable {F} {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- `pullHom` preserves composition. -/
lemma pullHom_comp' {X₁ X₂ X₃ Y : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {M₃ : F.obj (.mk (op X₃))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

/-- `pullHom` sends identities to identities. -/
lemma pullHom_id' {X₁ Y : C} {M₁ : F.obj (.mk (op X₁))} {f₁ : Y ⟶ X₁}
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

/-- `pullIso` commutes with inverses. -/
lemma pullIso_symm {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {Y : C}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullIso e g gf₁ gf₂ hgf₁ hgf₂).symm = pullIso e.symm g gf₂ gf₁ hgf₂ hgf₁ := by
  apply Iso.ext
  simp [pullIso]

/-- Restriction of a point, with a prescribed name for its new base map. -/
lemma restrict_eq {Z Z' : Over T} (q : Z' ⟶ Z) (x : Points F ξ η Z) (a : Z'.left ⟶ U)
    (h : q.left ≫ x.1 = a) :
    restrict F ξ η q x = ⟨a, pullIso x.2 q.left a Z'.hom h q.w⟩ := by
  subst h
  rfl

/-- Points with the same base map are equal when their isomorphisms are. -/
lemma mk_eq_mk_iff {Z : Over T} (a : Z.left ⟶ U)
    (e e' : (F.map a.op.toLoc).toFunctor.obj ξ ≅ (F.map Z.hom.op.toLoc).toFunctor.obj η) :
    (⟨a, e⟩ : Points F ξ η Z) = ⟨a, e'⟩ ↔ e = e' := by
  simp

/-- Points glue along a square on which morphisms glue uniquely, once their base maps
glue. -/
theorem exists_glued_point {X₀ X₁ X₂ : C} {i₁ : X₀ ⟶ X₁} {i₂ : X₀ ⟶ X₂} {j₁ : X₁ ⟶ T}
    {j₂ : X₂ ⟶ T} {w : i₁ ≫ j₁ = i₂ ≫ j₂} (hG : IsSquareHomGluing F w)
    (c : X₀ ⟶ T) (hc₁ : i₁ ≫ j₁ = c) (hc₂ : i₂ ≫ j₂ = c)
    (x₁ : Points F ξ η (Over.mk j₁)) (x₂ : Points F ξ η (Over.mk j₂))
    (h : restrict F ξ η (Over.homMk i₁ hc₁ : Over.mk c ⟶ Over.mk j₁) x₁ =
      restrict F ξ η (Over.homMk i₂ hc₂ : Over.mk c ⟶ Over.mk j₂) x₂)
    (g : T ⟶ U) (hg₁ : j₁ ≫ g = x₁.1) (hg₂ : j₂ ≫ g = x₂.1) :
    ∃ z : Points F ξ η (Over.mk (𝟙 T)), z.1 = g ∧
      restrict F ξ η (Over.homMk j₁ (Category.comp_id _) : Over.mk j₁ ⟶ Over.mk (𝟙 T)) z =
        x₁ ∧
      restrict F ξ η (Over.homMk j₂ (Category.comp_id _) : Over.mk j₂ ⟶ Over.mk (𝟙 T)) z =
        x₂ := by
  rcases x₁ with ⟨a₁, e₁⟩
  rcases x₂ with ⟨a₂, e₂⟩
  dsimp only at hg₁ hg₂
  subst hg₁ hg₂
  have hd₁ : i₁ ≫ j₁ ≫ g = c ≫ g := by rw [← Category.assoc, hc₁]
  have hd₂ : i₂ ≫ j₂ ≫ g = c ≫ g := by rw [← Category.assoc, hc₂]
  rw [restrict_eq _ _ _ _ (c ≫ g) hd₁, restrict_eq _ _ _ _ (c ≫ g) hd₂, mk_eq_mk_iff] at h
  have hP : pullIso e₁ i₁ (c ≫ g) c hd₁ hc₁ = pullIso e₂ i₂ (c ≫ g) c hd₂ hc₂ := h
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := hG.existsUnique_pullHom ξ η g (𝟙 T) (j₁ ≫ g) j₁ (j₂ ≫ g) j₂
    (c ≫ g) c rfl (Category.comp_id _) rfl (Category.comp_id _) hd₁ hc₁ hd₂ hc₂ e₁.hom e₂.hom
    (by rw [← pullIso_hom, ← pullIso_hom, hP])
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, -⟩ := hG.existsUnique_pullHom η ξ (𝟙 T) g j₁ (j₁ ≫ g) j₂ (j₂ ≫ g)
    c (c ≫ g) (Category.comp_id _) rfl (Category.comp_id _) rfl hc₁ hd₁ hc₂ hd₂ e₁.inv e₂.inv
    (by
      have := congrArg (fun e ↦ e.symm.hom) hP
      simpa only [pullIso_symm, pullIso_hom, Iso.symm_hom] using this)
  have hid : ∀ (V : C) (M : F.obj (.mk (op V))) (a : T ⟶ V)
      (θ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map a.op.toLoc).toFunctor.obj M)
      (a₁ : X₁ ⟶ V) (a₂ : X₂ ⟶ V) (h₁ : j₁ ≫ a = a₁) (h₂ : j₂ ≫ a = a₂),
      pullHom θ j₁ a₁ a₁ h₁ h₁ = 𝟙 _ → pullHom θ j₂ a₂ a₂ h₂ h₂ = 𝟙 _ → θ = 𝟙 _ := by
    intro V M a θ a₁ a₂ h₁ h₂ hθ₁ hθ₂
    have e₁' : i₁ ≫ a₁ = c ≫ a := by rw [← h₁, ← Category.assoc, hc₁]
    have e₂' : i₂ ≫ a₂ = c ≫ a := by rw [← h₂, ← Category.assoc, hc₂]
    obtain ⟨θ₀, -, hθ₀⟩ := hG.existsUnique_pullHom M M a a a₁ a₁ a₂ a₂ (c ≫ a) (c ≫ a)
      h₁ h₁ h₂ h₂ e₁' e₁' e₂' e₂' (𝟙 _) (𝟙 _) (by rw [pullHom_id', pullHom_id'])
    rw [hθ₀ θ ⟨hθ₁, hθ₂⟩, hθ₀ (𝟙 _) ⟨pullHom_id' _ _ _, pullHom_id' _ _ _⟩]
  have hφψ : φ ≫ ψ = 𝟙 _ := hid U ξ g _ (j₁ ≫ g) (j₂ ≫ g) rfl rfl
    (by rw [pullHom_comp' φ ψ j₁ (j₁ ≫ g) j₁ (j₁ ≫ g) rfl (Category.comp_id _) rfl, hφ₁, hψ₁,
      Iso.hom_inv_id])
    (by rw [pullHom_comp' φ ψ j₂ (j₂ ≫ g) j₂ (j₂ ≫ g) rfl (Category.comp_id _) rfl, hφ₂, hψ₂,
      Iso.hom_inv_id])
  have hψφ : ψ ≫ φ = 𝟙 _ := hid T η (𝟙 T) _ j₁ j₂ (Category.comp_id _) (Category.comp_id _)
    (by rw [pullHom_comp' ψ φ j₁ j₁ (j₁ ≫ g) j₁ (Category.comp_id _) rfl
      (Category.comp_id _), hψ₁, hφ₁, Iso.inv_hom_id])
    (by rw [pullHom_comp' ψ φ j₂ j₂ (j₂ ≫ g) j₂ (Category.comp_id _) rfl
      (Category.comp_id _), hψ₂, hφ₂, Iso.inv_hom_id])
  refine ⟨⟨g, ⟨φ, ψ, hφψ, hψφ⟩⟩, rfl, ?_, ?_⟩
  · rw [restrict_eq _ _ _ _ (j₁ ≫ g) rfl, mk_eq_mk_iff]
    apply Iso.ext
    exact hφ₁
  · rw [restrict_eq _ _ _ _ (j₂ ≫ g) rfl, mk_eq_mk_iff]
    apply Iso.ext
    exact hφ₂

/-- The lifting step of the proof of Stacks Lemma 90.13.2 (Tag 06IU), for actual points.

Let `y` be a point of `ξ` with values in `N` over `i : B ⟶ A` whose base map extends along
`i` to some `u : A ⟶ U`. Suppose objects glue along the square `(i, i, j₁, j₂)` with total
corner `P`, morphisms glue along the square `(rA, rD, j₁, jD)` with the same total corner,
maps to `U` glue along the second square, and points over `rD` with residue map `p` lift
along `rD`. Then `y` lifts to a point over the identity of `A`. -/
theorem exists_lift_of_square_gluing {K A B D P : C} (p : K ⟶ U) (i : B ⟶ A) (rA : K ⟶ A)
    (rB : K ⟶ B) (hr : rB ≫ i = rA) (rD : K ⟶ D) (j₁ j₂ : A ⟶ P) (jD : D ⟶ P)
    (w₁ : i ≫ j₁ = i ≫ j₂) (w₂ : rA ≫ j₁ = rD ≫ jD)
    (hE : IsSquareEffective F w₁) (hG : IsSquareHomGluing F w₂)
    (hU : ∀ (g₁ : A ⟶ U) (g₂ : D ⟶ U), rA ≫ g₁ = rD ≫ g₂ →
      ∃ g : P ⟶ U, j₁ ≫ g = g₁ ∧ jD ≫ g = g₂)
    (hT : ∀ (Z : F.obj (.mk (op P))) (y : Points F ξ Z (Over.mk (rD ≫ jD))), y.1 = p →
      ∃ x : Points F ξ Z (Over.mk jD),
        restrict F ξ Z (Over.homMk rD rfl : Over.mk (rD ≫ jD) ⟶ Over.mk jD) x = y)
    (N : F.obj (.mk (op A))) (y : Points F ξ N (Over.mk i)) (hy : rB ≫ y.1 = p)
    (u : A ⟶ U) (hu : i ≫ u = y.1) :
    ∃ x : Points F ξ N (Over.mk (𝟙 A)),
      restrict F ξ N (Over.homMk i (Category.comp_id _) : Over.mk i ⟶ Over.mk (𝟙 A)) x = y := by
  rcases y with ⟨y₁, ey⟩
  dsimp only at hy hu
  subst hu
  let e : (F.map i.op.toLoc).toFunctor.obj ((F.map u.op.toLoc).toFunctor.obj ξ) ≅
      (F.map i.op.toLoc).toFunctor.obj ((F.map (𝟙 A).op.toLoc).toFunctor.obj N) :=
    ((Cat.Hom.toNatIso (F.mapComp' u.op.toLoc i.op.toLoc (i ≫ u).op.toLoc
      (toLoc_comp rfl))).app ξ).symm ≪≫ ey ≪≫
      (Cat.Hom.toNatIso (F.mapComp' (𝟙 A).op.toLoc i.op.toLoc i.op.toLoc
        (toLoc_comp (Category.comp_id i)))).app N
  obtain ⟨Z, e₁, e₂, he⟩ := hE _ _ e
  have hey := pullIso_symm_trans_pullIso_of_effective w₁ u (𝟙 A) (i ≫ u) i rfl
    (Category.comp_id i) Z e₁ e₂ e he
  have hey' : ey = (pullIso e₁ i (i ≫ j₁) (i ≫ u) rfl rfl).symm ≪≫
      pullIso e₂ i (i ≫ j₁) i w₁.symm (Category.comp_id i) := by
    rw [← hey]
    apply Iso.ext
    simp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom,
      Cat.Hom.toNatIso_inv, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
      Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    simp
  have hp : rA ≫ u = p := by rw [← hr, Category.assoc]; exact hy
  obtain ⟨wpt, hw⟩ := hT Z (restrict F ξ Z (Over.homMk rA w₂ : Over.mk (rD ≫ jD) ⟶
    Over.mk j₁) ⟨u, e₁.symm⟩) hp
  have hw₁ : rD ≫ wpt.1 = rA ≫ u := congrArg Sigma.fst hw
  obtain ⟨g, hg₁, hg₂⟩ := hU u wpt.1 hw₁.symm
  obtain ⟨⟨z₁, z₂⟩, hz, hz₁, -⟩ :=
    exists_glued_point ξ Z hG (rD ≫ jD) w₂ rfl ⟨u, e₁.symm⟩ wpt hw.symm g hg₁ hg₂
  dsimp only at hz
  subst hz hg₁
  change (⟨j₁ ≫ z₁, pullIso z₂ j₁ (j₁ ≫ z₁) j₁ rfl (Category.comp_id _)⟩ :
    Points F ξ Z (Over.mk j₁)) = ⟨j₁ ≫ z₁, e₁.symm⟩ at hz₁
  rw [mk_eq_mk_iff] at hz₁
  have hiu : i ≫ j₂ ≫ z₁ = i ≫ j₁ ≫ z₁ := by rw [← Category.assoc, ← w₁, Category.assoc]
  refine ⟨⟨j₂ ≫ z₁, pullIso z₂ j₂ (j₂ ≫ z₁) j₂ rfl (Category.comp_id _) ≪≫ e₂⟩, ?_⟩
  refine (restrict_eq ξ N (Over.homMk i (Category.comp_id _) : Over.mk i ⟶ Over.mk (𝟙 A))
    ⟨j₂ ≫ z₁, pullIso z₂ j₂ (j₂ ≫ z₁) j₂ rfl (Category.comp_id _) ≪≫ e₂⟩
    (i ≫ j₁ ≫ z₁) hiu).trans ?_
  have L : pullIso (pullIso z₂ j₂ (j₂ ≫ z₁) j₂ rfl (Category.comp_id _)) i (i ≫ j₁ ≫ z₁)
      (i ≫ j₁) hiu w₁.symm =
      pullIso z₂ (i ≫ j₁) (i ≫ j₁ ≫ z₁) (i ≫ j₁) (Category.assoc _ _ _)
        (Category.comp_id _) := by
    rw [pullIso_pullIso z₂ j₂ (j₂ ≫ z₁) j₂ i (i ≫ j₁ ≫ z₁) (i ≫ j₁) rfl (Category.comp_id _)
      hiu w₁.symm]
    exact pullIso_congr _ _ _ w₁.symm _ _ _ _ _ _
  have R : (pullIso e₁ i (i ≫ j₁) (i ≫ j₁ ≫ z₁) rfl rfl).symm =
      pullIso z₂ (i ≫ j₁) (i ≫ j₁ ≫ z₁) (i ≫ j₁) (Category.assoc _ _ _)
        (Category.comp_id _) := by
    rw [pullIso_symm, ← hz₁, pullIso_pullIso z₂ j₁ (j₁ ≫ z₁) j₁ i (i ≫ j₁ ≫ z₁) (i ≫ j₁) rfl
      (Category.comp_id _) rfl rfl]
  rw [mk_eq_mk_iff]
  change pullIso (pullIso z₂ j₂ (j₂ ≫ z₁) j₂ rfl (Category.comp_id _) ≪≫ e₂) i (i ≫ j₁ ≫ z₁) i
    hiu (Category.comp_id i) = ey
  rw [hey', pullIso_trans _ _ i (i ≫ j₁ ≫ z₁) (i ≫ j₁) i hiu w₁.symm
    (Category.comp_id i), L, R]

end Points

end Langlands.CategoryTheory.PseudofunctorSquareGluing
