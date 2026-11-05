import Langlands.Shimura.EquivariantFormsHecke
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Group actions on colimits over compact open levels -/

noncomputable section

universe u v w t uΓ uX

set_option autoImplicit false

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- Compact open levels, remembering only the inclusion order of their subgroups. -/
def Ordered (G : Type v) [Group G] [TopologicalSpace G] : Type v := CompactOpenLevel G

instance : Preorder (Ordered G) :=
  Preorder.lift (fun K : CompactOpenLevel G => K.subgroup)

/-- Inclusions of levels, as forgetful arrows of the transporter category of levels. -/
def inclusionFunctor : Ordered G ⥤ CompactOpenLevel G where
  obj K := K
  map h := inclusion (leOfHom h)
  map_id _ := rfl
  map_comp _ _ := Arrow.ext (mul_one 1).symm

/-- The arrow `K ⟶ K` given by an element `k ∈ K`. -/
def selfArrow (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup) : K ⟶ K :=
  ⟨k, fun _ hx => K.subgroup.mul_mem (K.subgroup.mul_mem (K.subgroup.inv_mem hk) hx) hk⟩

@[simp] theorem selfArrow_element (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup) :
    (selfArrow K k hk).element = k := rfl

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- The intersection of two compact open levels. -/
def inf (K L : CompactOpenLevel G) : CompactOpenLevel G where
  openSubgroup := K.openSubgroup ⊓ L.openSubgroup
  isCompact := K.isCompact.inter_right L.openSubgroup.isClosed

instance : IsDirected (Ordered G) (· ≥ ·) :=
  ⟨fun K L => ⟨inf K L, fun _ hx => hx.1, fun _ hx => hx.2⟩⟩

instance [Nonempty (CompactOpenLevel G)] : IsCofiltered (Ordered G) :=
  haveI : Nonempty (Ordered G) := ‹Nonempty (CompactOpenLevel G)›
  isCofiltered_of_directed_ge_nonempty _

/-- The conjugate level `g K g⁻¹`. -/
def conjLevel (g : G) (K : CompactOpenLevel G) : CompactOpenLevel G where
  openSubgroup := K.openSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
    (by change Continuous (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹); fun_prop)
  isCompact := by
    have h : (fun y : G => g * y * g⁻¹) '' (K.openSubgroup : Set G) =
        (MulAut.conj g⁻¹).toMonoidHom ⁻¹' (K.openSubgroup : Set G) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
      · intro hx
        exact ⟨g⁻¹ * x * g, hx, by group⟩
    have hc := K.isCompact.image (f := fun y : G => g * y * g⁻¹) (by fun_prop)
    rw [h] at hc
    exact hc

theorem mem_conjLevel {g x : G} {K : CompactOpenLevel G} :
    x ∈ (conjLevel g K).subgroup ↔ g⁻¹ * x * g ∈ K.subgroup := by
  change (MulAut.conj g⁻¹) x ∈ K.subgroup ↔ _
  rw [MulAut.conj_apply, inv_inv]

/-- Right translation by `g`, from the conjugate level `g K g⁻¹` to `K`. -/
def conjArrow (g : G) (K : CompactOpenLevel G) : conjLevel g K ⟶ K :=
  ⟨g, fun _ hk => mem_conjLevel.1 hk⟩

@[simp] theorem conjArrow_element (g : G) (K : CompactOpenLevel G) :
    (conjArrow g K).element = g := rfl

theorem le_conjLevel {K L : CompactOpenLevel G} (a : K ⟶ L) :
    K.subgroup ≤ (conjLevel a.element L).subgroup :=
  fun k hk => mem_conjLevel.2 (a.respects k hk)

theorem conjLevel_mono (g : G) {K L : CompactOpenLevel G} (h : K.subgroup ≤ L.subgroup) :
    (conjLevel g K).subgroup ≤ (conjLevel g L).subgroup :=
  fun _ hx => mem_conjLevel.2 (h (mem_conjLevel.1 hx))

/-- Every level arrow is an inclusion followed by a conjugation arrow. -/
theorem eq_inclusion_comp_conjArrow {K L : CompactOpenLevel G} (a : K ⟶ L) :
    a = inclusion (le_conjLevel a) ≫ conjArrow a.element L :=
  Arrow.ext (one_mul _).symm

theorem conjArrow_comp_inclusion (g : G) {K L : CompactOpenLevel G}
    (h : K.subgroup ≤ L.subgroup) :
    conjArrow g K ≫ inclusion h = inclusion (conjLevel_mono g h) ≫ conjArrow g L :=
  Arrow.ext ((mul_one g).trans (one_mul g).symm)

end TopologicalGroup

end CompactOpenLevel

namespace LevelColimit

open CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] {C : Type u} [Category.{w} C]

/-- A presheaf on levels restricted to inclusions of levels. -/
abbrev diagram (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) : (Ordered G)ᵒᵖ ⥤ C :=
  (inclusionFunctor (G := G)).op ⋙ F

/-- Each `k ∈ K` acts as the identity on level `K`. -/
def IsLevelTrivial (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) : Prop :=
  ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
    F.map (selfArrow K k hk).op = 𝟙 (F.obj (op K))

variable (G C) in
/-- Level-trivial presheaves on levels, as a property of objects. -/
def levelTrivialProperty : ObjectProperty ((CompactOpenLevel G)ᵒᵖ ⥤ C) :=
  fun F => IsLevelTrivial F

/-- A presheaf pulled back from a covariant functor on levels is level-trivial when
each `k ∈ K` acts as the identity on level `K` of that functor. -/
theorem isLevelTrivial_op_comp {D : Type*} [Category D] (T : CompactOpenLevel G ⥤ D)
    (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
      T.map (selfArrow K k hk) = 𝟙 (T.obj K))
    (E : Dᵒᵖ ⥤ C) : IsLevelTrivial (T.op ⋙ E) := by
  intro K k hk
  change E.map (T.map (selfArrow K k hk)).op = 𝟙 _
  rw [hT K k hk, op_id, E.map_id]

theorem diagram_map (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) {K L : (Ordered G)ᵒᵖ} (h : K ⟶ L) :
    (diagram F).map h = F.map (inclusion (leOfHom h.unop)).op := rfl

variable [HasColimitsOfShape (Ordered G)ᵒᵖ C] (F : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- The inclusion of level `K` into the colimit over shrinking levels. -/
def ι (K : CompactOpenLevel G) : F.obj (op K) ⟶ colimit (diagram F) :=
  colimit.ι (diagram F) (op K)

@[reassoc (attr := simp)]
theorem map_inclusion_ι {K L : CompactOpenLevel G} (h : K.subgroup ≤ L.subgroup) :
    F.map (inclusion h).op ≫ ι F K = ι F L :=
  colimit.w (diagram F)
    (homOfLE (X := Ordered G) (x := K) (y := L) h).op

theorem hom_ext {Y : C} {f f' : colimit (diagram F) ⟶ Y}
    (h : ∀ K : CompactOpenLevel G, ι F K ≫ f = ι F K ≫ f') : f = f' :=
  colimit.hom_ext fun K => h K.unop

section Translate

variable [IsTopologicalGroup G]

theorem translate_leg_naturality (g : G) {K L : CompactOpenLevel G}
    (h : K.subgroup ≤ L.subgroup) :
    F.map (inclusion h).op ≫ F.map (conjArrow g K).op ≫ ι F (conjLevel g K) =
      F.map (conjArrow g L).op ≫ ι F (conjLevel g L) := by
  rw [← Category.assoc, ← F.map_comp, ← op_comp, conjArrow_comp_inclusion, op_comp,
    F.map_comp, Category.assoc, map_inclusion_ι]

/-- The cocone whose level-`K` leg is translation by `g` into level `g K g⁻¹`. -/
def translateCocone (g : G) : Cocone (diagram F) where
  pt := colimit (diagram F)
  ι :=
    { app := fun K => F.map (conjArrow g K.unop).op ≫ ι F (conjLevel g K.unop)
      naturality := fun _ _ h =>
        (translate_leg_naturality F g (leOfHom h.unop)).trans (Category.comp_id _).symm }

/-- The action of `g` on the colimit over levels. -/
def translate (g : G) : colimit (diagram F) ⟶ colimit (diagram F) :=
  colimit.desc (diagram F) (translateCocone F g)

@[reassoc]
theorem ι_translate (g : G) (K : CompactOpenLevel G) :
    ι F K ≫ translate F g = F.map (conjArrow g K).op ≫ ι F (conjLevel g K) :=
  colimit.ι_desc (translateCocone F g) (op K)

/-- Every level arrow `a : K ⟶ L` is compatible with translation by its element. -/
@[reassoc]
theorem map_ι {K L : CompactOpenLevel G} (a : K ⟶ L) :
    F.map a.op ≫ ι F K = ι F L ≫ translate F a.element := by
  conv_lhs => rw [eq_inclusion_comp_conjArrow a]
  rw [op_comp, F.map_comp, Category.assoc, map_inclusion_ι, ι_translate]

theorem translate_one : translate F 1 = 𝟙 _ :=
  hom_ext F fun K => by
    have h := map_ι F (𝟙 K)
    rw [id_element, op_id, F.map_id, Category.id_comp] at h
    rw [← h, Category.comp_id]

theorem translate_mul (g h : G) : translate F (g * h) = translate F h ≫ translate F g :=
  hom_ext F fun L => by
    have e := map_ι F (conjArrow g (conjLevel h L) ≫ conjArrow h L)
    rw [comp_element, conjArrow_element, conjArrow_element] at e
    rw [← e, ι_translate_assoc, ι_translate, op_comp, F.map_comp, Category.assoc]

/-- The colimit over levels, with `g` acting through the conjugate levels `g K g⁻¹`. -/
def action : Action C G where
  V := colimit (diagram F)
  ρ :=
    { toFun := translate F
      map_one' := translate_one F
      map_mul' := fun g h => translate_mul F g h }

@[simp] theorem action_V : (action F).V = colimit (diagram F) := rfl

@[simp] theorem action_ρ (g : G) : (action F).ρ g = translate F g := rfl

theorem ι_translate_of_mem (hF : IsLevelTrivial F) {K : CompactOpenLevel G} {k : G}
    (hk : k ∈ K.subgroup) : ι F K ≫ translate F k = ι F K := by
  have h := map_ι F (selfArrow K k hk)
  rw [hF K k hk, Category.id_comp, selfArrow_element] at h
  exact h.symm

end Translate

section Map

variable {F} {F' F'' : (CompactOpenLevel G)ᵒᵖ ⥤ C}

/-- The map of colimits over levels induced by a natural transformation. -/
def map (α : F ⟶ F') : colimit (diagram F) ⟶ colimit (diagram F') :=
  colimMap (Functor.whiskerLeft (inclusionFunctor (G := G)).op α)

@[reassoc (attr := simp)]
theorem ι_map (α : F ⟶ F') (K : CompactOpenLevel G) :
    ι F K ≫ map α = α.app (op K) ≫ ι F' K :=
  ι_colimMap _ _

theorem map_id : map (𝟙 F) = 𝟙 _ :=
  hom_ext F fun K => by simp

theorem map_comp (α : F ⟶ F') (β : F' ⟶ F'') : map (α ≫ β) = map α ≫ map β :=
  hom_ext F fun K => by simp

variable [IsTopologicalGroup G]

@[reassoc]
theorem translate_map (α : F ⟶ F') (g : G) :
    translate F g ≫ map α = map α ≫ translate F' g :=
  hom_ext F fun K => by
    rw [ι_translate_assoc, ι_map, ι_map_assoc, ι_translate, α.naturality_assoc]

end Map

variable [IsTopologicalGroup G]

variable (G C) in
/-- Colimits over levels as a functor to objects with an action of `G`. -/
def functor : ((CompactOpenLevel G)ᵒᵖ ⥤ C) ⥤ Action C G where
  obj F := action F
  map α := ⟨map α, fun g => translate_map α g⟩
  map_id F := Action.Hom.ext (map_id (F := F))
  map_comp α β := Action.Hom.ext (map_comp α β)

@[simp] theorem functor_obj (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    (functor G C).obj F = action F := rfl

@[simp] theorem functor_map_hom {F F' : (CompactOpenLevel G)ᵒᵖ ⥤ C} (α : F ⟶ F') :
    ((functor G C).map α).hom = map α := rfl

variable (G C) in
/-- The underlying object of the colimit action is the ordinary colimit over inclusions. -/
def functorCompForgetIso :
    functor G C ⋙ Action.forget C G ≅
      (Functor.whiskeringLeft _ _ C).obj (inclusionFunctor (G := G)).op ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

section Smooth

variable {R : Type t} [CommRing R] [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]

/-- The colimit over levels of a level-trivial presheaf of modules is smooth: the image of
level `K` is fixed by the open subgroup `K`. -/
theorem isSmooth_action (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) : IsSmooth ((Rep.ActionToRep R G).obj (action F)).ρ := by
  let S : Submodule R (action F).V :=
    smoothVectors ((Rep.ActionToRep R G).obj (action F)).ρ
  have hι : ∀ (K : CompactOpenLevel G) (x : F.obj (op K)), (ι F K).hom x ∈ S := by
    intro K x
    refine ⟨K.openSubgroup, ?_⟩
    intro g
    change (translate F (g : G)).hom ((ι F K).hom x) = (ι F K).hom x
    exact congrArg (fun f => ModuleCat.Hom.hom f x) (ι_translate_of_mem F hF g.property)
  have h0 : (ModuleCat.ofHom S.mkQ :
      (action F).V ⟶ ModuleCat.of R ((action F).V ⧸ S)) = 0 := by
    apply hom_ext F
    intro K
    rw [Limits.comp_zero]
    ext x
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hι K x)
  have hS : S = ⊤ := by
    rw [← Submodule.ker_mkQ S]
    have h1 : S.mkQ = 0 := congrArg ModuleCat.Hom.hom h0
    rw [h1, LinearMap.ker_zero]
  have hv : ∀ x : (action F).V, x ∈ S := fun x => hS ▸ Submodule.mem_top
  exact hv

/-- Vectors coming from level `K` are fixed by `K`. -/
theorem translate_ι_apply_of_mem (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) {K : CompactOpenLevel G} {k : G} (hk : k ∈ K.subgroup)
    (x : F.obj (op K)) : (translate F k).hom ((ι F K).hom x) = (ι F K).hom x :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_translate_of_mem F hF hk)

/-- The action of `g` on a vector coming from level `K`: it comes from the conjugate level
`g K g⁻¹`, through the transition map of the arrow `g K g⁻¹ ⟶ K` with element `g`. -/
theorem translate_ι_apply (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (g : G)
    (K : CompactOpenLevel G) (x : F.obj (op K)) :
    (translate F g).hom ((ι F K).hom x) =
      (ι F (conjLevel g K)).hom ((F.map (conjArrow g K).op).hom x) :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_translate F g K)

/-- Since the levels are directed under intersection, every vector of the colimit comes from
a single level, provided some compact open level exists. -/
theorem exists_ι_apply [Nonempty (CompactOpenLevel G)]
    (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (x : (colimit (diagram F) : ModuleCat.{w} R)) :
    ∃ (K : CompactOpenLevel G) (y : F.obj (op K)), (ι F K).hom y = x := by
  let S : Submodule R (colimit (diagram F) : ModuleCat.{w} R) :=
    { carrier := {x | ∃ (K : CompactOpenLevel G) (y : F.obj (op K)), (ι F K).hom y = x}
      add_mem' := by
        rintro _ _ ⟨K, y, rfl⟩ ⟨L, z, rfl⟩
        have hK : (inf K L).subgroup ≤ K.subgroup := fun _ hx => hx.1
        have hL : (inf K L).subgroup ≤ L.subgroup := fun _ hx => hx.2
        refine ⟨inf K L, (F.map (inclusion hK).op).hom y + (F.map (inclusion hL).op).hom z, ?_⟩
        rw [map_add, ← map_inclusion_ι F hK, ← map_inclusion_ι F hL]
        rfl
      zero_mem' := by
        obtain ⟨K⟩ := ‹Nonempty (CompactOpenLevel G)›
        exact ⟨K, 0, map_zero _⟩
      smul_mem' := by
        rintro r _ ⟨K, y, rfl⟩
        exact ⟨K, r • y, map_smul _ r y⟩ }
  have h0 : (ModuleCat.ofHom S.mkQ :
      (colimit (diagram F) : ModuleCat.{w} R) ⟶
        ModuleCat.of R ((colimit (diagram F) : ModuleCat.{w} R) ⧸ S)) = 0 := by
    apply hom_ext F
    intro K
    rw [Limits.comp_zero]
    ext y
    exact (Submodule.Quotient.mk_eq_zero S).mpr ⟨K, y, rfl⟩
  have hS : S = ⊤ := by
    rw [← Submodule.ker_mkQ S]
    have h1 : S.mkQ = 0 := congrArg ModuleCat.Hom.hom h0
    rw [h1, LinearMap.ker_zero]
  have hx : x ∈ S := hS ▸ Submodule.mem_top
  exact hx

/-- The smooth representation on the colimit over levels of a level-trivial presheaf. -/
def smoothRep (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F) :
    SmoothRep.{t, v, w} R G :=
  ⟨(Rep.ActionToRep R G).obj (action F), isSmooth_action F hF⟩

variable (G R) in
/-- Colimits over levels of level-trivial presheaves of modules, as smooth representations. -/
def smoothFunctor :
    (levelTrivialProperty G (ModuleCat.{w} R)).FullSubcategory ⥤ SmoothRep.{t, v, w} R G :=
  (smoothRepProperty R G).lift
    ((levelTrivialProperty G (ModuleCat.{w} R)).ι ⋙ functor G (ModuleCat.{w} R) ⋙
      Rep.ActionToRep R G)
    (fun F => isSmooth_action F.obj F.property)

@[simp] theorem smoothFunctor_obj_obj
    (F : (levelTrivialProperty G (ModuleCat.{w} R)).FullSubcategory) :
    ((smoothFunctor G R).obj F).obj = (Rep.ActionToRep R G).obj (action F.obj) := rfl

theorem smoothRep_ρ_ι_apply (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) (g : G) (K : CompactOpenLevel G) (x : F.obj (op K)) :
    (smoothRep F hF).obj.ρ g ((ι F K).hom x) =
      (ι F (conjLevel g K)).hom ((F.map (conjArrow g K).op).hom x) :=
  translate_ι_apply F g K x

end Smooth

end LevelColimit

/-! ## Specializations -/

namespace LevelSpace

open CompactOpenLevel LevelColimit

variable {Γ : Type uΓ} {G : Type v} {X : Type uX} [Group Γ] [Group G] [MulAction Γ X]
  (ι : Γ →* G)

theorem translate_self (K : Subgroup G) (k : G) (hk : k ∈ K)
    (hg : ∀ x ∈ K, k⁻¹ * x * k ∈ K) (q : LevelSpace (X := X) ι K) :
    translate k hg q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk K (x.1, x.2 * k) = mk K x
    rw [mk_eq_mk]
    exact ⟨1, k⁻¹, K.inv_mem hk, by simp, by simp [mul_assoc]⟩

variable [TopologicalSpace X] [TopologicalSpace G] [ContinuousMul G]

theorem tower_map_selfArrow (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup) :
    (tower (X := X) (ι := ι)).map (selfArrow K k hk) = 𝟙 _ := by
  ext q
  exact translate_self ι K.subgroup k hk (selfArrow K k hk).respects q

/-- Any presheaf on the level spaces gives a level-trivial presheaf on levels. -/
theorem isLevelTrivial_tower {C : Type u} [Category.{w} C] (E : TopCat.{max v uX}ᵒᵖ ⥤ C) :
    IsLevelTrivial ((tower (X := X) (ι := ι)).op ⋙ E) :=
  isLevelTrivial_op_comp _ (tower_map_selfArrow ι) E

end LevelSpace

namespace EquivariantForms

open CompactOpenLevel LevelColimit

variable {R : Type t} [CommRing R] {Γ : Type uΓ} {G : Type v} [Group Γ] [Group G]
  [TopologicalSpace G] (ι : Γ →* G) {V : Type w} [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- The presheaf of forms of all levels is level-trivial. -/
theorem isLevelTrivial_levelPresheaf : IsLevelTrivial (levelPresheaf R ι ρ) := by
  intro K k hk
  ext f
  refine Subtype.ext (funext fun x => ?_)
  change ρ k (f.1 (x * k)) = f.1 x
  rw [f.2.2 x ⟨k, hk⟩]
  change ρ k (ρ k⁻¹ (f.1 x)) = f.1 x
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (R) [IsTopologicalGroup G]

include ι ρ in
/-- The smooth representation of `G` on forms of all levels: the colimit over shrinking
compact open levels `K` of the forms of level `K`, where `g` sends a form `f` of level `K` to
the form `x ↦ ρ g (f (x * g))` of level `g K g⁻¹`. -/
def levelColimitRep : SmoothRep.{t, v, max v w} R G :=
  LevelColimit.smoothRep (G := G) (R := R) (levelPresheaf R ι ρ)
    (isLevelTrivial_levelPresheaf ι ρ)

theorem levelColimitRep_ρ_ι_apply (g : G) (K : CompactOpenLevel G)
    (f : forms ι K.subgroup (ρ.comp K.subgroup.subtype)) :
    (levelColimitRep R ι ρ).obj.ρ g ((LevelColimit.ι (levelPresheaf R ι ρ) K).hom f) =
      (LevelColimit.ι (levelPresheaf R ι ρ) (conjLevel g K)).hom
        (levelTransport R ι ρ (conjArrow g K) f) :=
  smoothRep_ρ_ι_apply (G := G) (R := R) (levelPresheaf R ι ρ) (isLevelTrivial_levelPresheaf ι ρ)
    g K f

end EquivariantForms

end Langlands.Shimura
