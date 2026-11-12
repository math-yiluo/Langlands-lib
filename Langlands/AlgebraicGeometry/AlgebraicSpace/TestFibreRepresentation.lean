import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Represented base changes through fibres over a test scheme -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace TestFibre

section Points

variable {S : Scheme.{u}}

/-- A morphism of schemes over `S`, as a point of the represented presheaf. -/
def pt {T T' : Over S} (c : T ⟶ T') : ((schemeYoneda S).obj T').obj (op T) :=
  ULift.up c

lemma pt_injective {T T' : Over S} : Function.Injective (pt : (T ⟶ T') → _) :=
  fun _ _ h => congrArg ULift.down h

lemma exists_pt {T T' : Over S} (x : ((schemeYoneda S).obj T').obj (op T)) :
    ∃ c : T ⟶ T', x = pt c :=
  ⟨x.down, rfl⟩

lemma app_pt {F : Presheaf S} {T T' : Over S} (α : (schemeYoneda S).obj T' ⟶ F)
    (c : T ⟶ T') : α.app (op T) (pt c) = F.map c.op (uliftYonedaEquiv α) :=
  schemeYoneda_app_up α c

lemma map_pt {T T' T'' : Over S} (k : T ⟶ T') (c : T' ⟶ T'') :
    ((schemeYoneda S).obj T'').map k.op (pt c) = pt (k ≫ c) :=
  rfl

lemma yoneda_map_pt {T T' T'' : Over S} (h : T' ⟶ T'') (c : T ⟶ T') :
    ((schemeYoneda S).map h).app (op T) (pt c) = pt (c ≫ h) :=
  rfl

end Points

variable {S : Scheme.{u}} {V : Over S}

/-- The structure morphism of a scheme over `V.left`, as a morphism over `S` to `V`. -/
abbrev toTest (T : Over V.left) : (Over.map V.hom).obj T ⟶ V :=
  Over.homMk T.hom

@[reassoc (attr := simp)]
lemma map_toTest {T T' : Over V.left} (k : T ⟶ T') :
    (Over.map V.hom).map k ≫ toTest T' = toTest T := by
  ext
  simp

variable {F G : Presheaf S} (f : F ⟶ G) (g : (schemeYoneda S).obj V ⟶ G)

/-- The fibre of `f` over `g`, as a presheaf on schemes over `V.left`: the sections of `F`
whose image under `f` is the restriction of `g` along the structure morphism. -/
def presheaf : Presheaf V.left where
  obj T := {x : F.obj (op ((Over.map V.hom).obj T.unop)) //
    f.app _ x = g.app _ (pt (toTest T.unop))}
  map {T T'} k := TypeCat.ofHom fun x => ⟨F.map ((Over.map V.hom).map k.unop).op x.1, by
    rw [NatTrans.naturality_apply, x.2, ← NatTrans.naturality_apply, map_pt, map_toTest]⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change F.map ((Over.map V.hom).map (𝟙 T.unop)).op x.1 = x.1
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id_apply]
  map_comp {T T' T''} k k' := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change F.map ((Over.map V.hom).map (k'.unop ≫ k.unop)).op x.1 =
      F.map ((Over.map V.hom).map k'.unop).op (F.map ((Over.map V.hom).map k.unop).op x.1)
    rw [CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp_apply]

@[simp]
lemma presheaf_map_val {T T' : (Over V.left)ᵒᵖ} (k : T ⟶ T') (x : (presheaf f g).obj T) :
    ((presheaf f g).map k x).1 = F.map ((Over.map V.hom).map k.unop).op x.1 :=
  rfl

variable {f g} (W : Over V.left) (e : (schemeYoneda V.left).obj W ≅ presheaf f g)

/-- The universal section of `F` over the representing scheme, viewed over `S`. -/
def fst : (schemeYoneda S).obj ((Over.map V.hom).obj W) ⟶ F :=
  uliftYonedaEquiv.symm (e.hom.app (op W) (pt (𝟙 W))).1

/-- For a scheme `T` over `S` and a factorization through `V`, the same scheme over
`V.left`. -/
abbrev over {T : Over S} (b : T ⟶ V) : Over V.left := Over.mk b.left

/-- The identification of `T` with its factorization through `V`, viewed back over `S`. -/
def overIso {T : Over S} (b : T ⟶ V) : T ≅ (Over.map V.hom).obj (over b) :=
  Over.isoMk (Iso.refl _) (by simp [Over.w b])

@[reassoc (attr := simp)]
lemma overIso_hom_toTest {T : Over S} (b : T ⟶ V) :
    (overIso b).hom ≫ toTest (over b) = b := by
  ext
  simp [overIso]

lemma fst_app_map {T : Over V.left} (d : T ⟶ W) :
    (fst W e).app (op ((Over.map V.hom).obj T)) (pt ((Over.map V.hom).map d)) =
      (e.hom.app (op T) (pt d)).1 := by
  rw [app_pt]
  simp only [fst, Equiv.apply_symm_apply]
  have h := e.hom.naturality_apply d.op (pt (𝟙 W))
  rw [map_pt, Category.comp_id] at h
  rw [h]
  rfl

/-- A representation of the fibre presheaf over `V.left` gives a representation of the
base change of `f` along `g` over `S`, with projection the structure morphism. -/
theorem isPullback :
    IsPullback (fst W e) ((schemeYoneda S).map (toTest W)) f g := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  obtain ⟨T⟩ := T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    obtain ⟨c, rfl⟩ := exists_pt x
    change f.app _ ((fst W e).app _ (pt c)) =
      g.app _ (((schemeYoneda S).map (toTest W)).app _ (pt c))
    rw [yoneda_map_pt, app_pt (fst W e) c, NatTrans.naturality_apply]
    simp only [fst, Equiv.apply_symm_apply]
    rw [(e.hom.app (op W) (pt (𝟙 W))).2, ← NatTrans.naturality_apply, map_pt]
  · rintro x₁ x₂ ⟨h₁, h₂⟩
    obtain ⟨c₁, rfl⟩ := exists_pt x₁
    obtain ⟨c₂, rfl⟩ := exists_pt x₂
    rw [yoneda_map_pt, yoneda_map_pt] at h₂
    have e₂ : c₁ ≫ toTest W = c₂ ≫ toTest W := pt_injective h₂
    let b := c₁ ≫ toTest W
    let d₁ : over b ⟶ W := Over.homMk c₁.left rfl
    let d₂ : over b ⟶ W := Over.homMk c₂.left (by
      have := congrArg CommaMorphism.left e₂
      simpa [b] using this.symm)
    have hc₁ : (overIso b).hom ≫ (Over.map V.hom).map d₁ = c₁ := by
      ext
      change 𝟙 _ ≫ c₁.left = c₁.left
      exact Category.id_comp _
    have hc₂ : (overIso b).hom ≫ (Over.map V.hom).map d₂ = c₂ := by
      ext
      change 𝟙 _ ≫ c₂.left = c₂.left
      exact Category.id_comp _
    have k₁ : (fst W e).app _ (pt c₁) = F.map (overIso b).hom.op
        ((fst W e).app _ (pt ((Over.map V.hom).map d₁))) := by
      rw [← NatTrans.naturality_apply, map_pt, hc₁]
    have k₂ : (fst W e).app _ (pt c₂) = F.map (overIso b).hom.op
        ((fst W e).app _ (pt ((Over.map V.hom).map d₂))) := by
      rw [← NatTrans.naturality_apply, map_pt, hc₂]
    have hval : (fst W e).app _ (pt ((Over.map V.hom).map d₁)) =
        (fst W e).app _ (pt ((Over.map V.hom).map d₂)) := by
      have h₁' : F.map (overIso b).hom.op
          ((fst W e).app _ (pt ((Over.map V.hom).map d₁))) =
          F.map (overIso b).hom.op
          ((fst W e).app _ (pt ((Over.map V.hom).map d₂))) := by
        rw [← k₁, ← k₂]
        exact h₁
      exact (ConcreteCategory.bijective_of_isIso (F.map (overIso b).hom.op)).injective h₁'
    rw [fst_app_map, fst_app_map] at hval
    have hd : d₁ = d₂ := pt_injective
      ((ConcreteCategory.bijective_of_isIso (e.hom.app (op (over b)))).injective
        (Subtype.ext hval))
    rw [← hc₁, ← hc₂, hd]
  · intro x b' hx
    obtain ⟨b, rfl⟩ := exists_pt b'
    let y : (presheaf f g).obj (op (over b)) := ⟨F.map (overIso b).inv.op x, by
      rw [NatTrans.naturality_apply, hx, ← NatTrans.naturality_apply, map_pt]
      exact congrArg (g.app _)
        (congrArg pt ((Iso.inv_comp_eq _).2 (overIso_hom_toTest b).symm))⟩
    let d : over b ⟶ W := (e.inv.app (op (over b)) y).down
    refine ⟨pt ((overIso b).hom ≫ (Over.map V.hom).map d), ?_, ?_⟩
    · rw [← map_pt, NatTrans.naturality_apply, fst_app_map]
      have hy : e.hom.app (op (over b)) (pt d) = y :=
        e.inv_hom_id_app_apply _ y
      rw [hy]
      change F.map (overIso b).hom.op (F.map (overIso b).inv.op x) = x
      rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
        CategoryTheory.Functor.map_id_apply]
    · rw [yoneda_map_pt, Category.assoc, map_toTest, overIso_hom_toTest]

/-- The projection of the represented base change is the structure morphism over `V.left`. -/
lemma toTest_left : (toTest W).left = W.hom :=
  rfl

end TestFibre

end Langlands.AlgebraicGeometry.AlgebraicSpace
