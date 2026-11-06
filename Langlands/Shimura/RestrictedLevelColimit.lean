import Langlands.Shimura.LevelColimit
import Mathlib.CategoryTheory.Filtered.Final

/-! # Group actions on colimits over levels satisfying a property -/

noncomputable section

universe u v w t

set_option autoImplicit false

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] (P : ObjectProperty (CompactOpenLevel G))

/-- The compact open levels satisfying `P`, remembering only the inclusion order of their
subgroups. -/
abbrev RestrictedOrdered : Type v := {K : Ordered G // P K}

/-- Inclusions of levels satisfying `P`, as arrows of the full transporter subcategory of
levels satisfying `P`. -/
def restrictedInclusion : RestrictedOrdered P ⥤ P.FullSubcategory where
  obj K := ⟨K.val, K.property⟩
  map h := ObjectProperty.homMk (inclusion (leOfHom h))
  map_id _ := P.hom_ext rfl
  map_comp _ _ := P.hom_ext (Arrow.ext (mul_one 1).symm)

/-- Forget that the ordered levels satisfy `P`. -/
def restrictedForget : RestrictedOrdered P ⥤ Ordered G where
  obj K := K.val
  map h := homOfLE (leOfHom h)

/-- Both routes from ordered levels satisfying `P` to all levels are the inclusion arrows. -/
theorem restrictedInclusion_comp_ι :
    restrictedInclusion P ⋙ P.ι = restrictedForget P ⋙ inclusionFunctor := rfl

/-- `P` holds for every level contained in a level satisfying `P`. -/
class IsDownwardClosed : Prop where
  of_le : ∀ {K L : CompactOpenLevel G}, K.subgroup ≤ L.subgroup → P L → P K

/-- The inclusion arrow between levels satisfying `P`. -/
abbrev restrictedHom {K L : P.FullSubcategory} (h : K.obj.subgroup ≤ L.obj.subgroup) : K ⟶ L :=
  ObjectProperty.homMk (inclusion h)

/-- The arrow `K ⟶ K` given by an element `k ∈ K`, for a level satisfying `P`. -/
abbrev restrictedSelfArrow (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup) : K ⟶ K :=
  ObjectProperty.homMk (selfArrow K.obj k hk)

section TopologicalGroup

variable [IsTopologicalGroup G]

/-- `P` is stable under conjugation `K ↦ g K g⁻¹`. -/
class IsConjStable : Prop where
  conjLevel : ∀ (g : G) {K : CompactOpenLevel G}, P K → P (conjLevel g K)

/-- The intersection of a level satisfying `P` with any level. -/
def restrictedInf [IsDownwardClosed P] (K : RestrictedOrdered P) (V : CompactOpenLevel G) :
    RestrictedOrdered P :=
  ⟨inf K.val V, IsDownwardClosed.of_le (fun _ hx => hx.1) K.property⟩

instance [IsDownwardClosed P] : IsDirected (RestrictedOrdered P) (· ≥ ·) :=
  ⟨fun K L => ⟨restrictedInf P K L.val, fun _ hx => hx.1, fun _ hx => hx.2⟩⟩

instance [Nonempty P.FullSubcategory] : Nonempty (RestrictedOrdered P) :=
  let ⟨K⟩ := ‹Nonempty P.FullSubcategory›
  ⟨⟨K.obj, K.property⟩⟩

instance [IsDownwardClosed P] [Nonempty P.FullSubcategory] : IsCofiltered (RestrictedOrdered P) :=
  isCofiltered_of_directed_ge_nonempty _

/-- Every level contains a level satisfying `P`, if `P` is downward closed and holds for some
level. -/
theorem exists_restrictedOrdered_le [IsDownwardClosed P] [Nonempty P.FullSubcategory]
    (V : CompactOpenLevel G) : ∃ K : RestrictedOrdered P, K.val.subgroup ≤ V.subgroup := by
  obtain ⟨K⟩ := (inferInstance : Nonempty (RestrictedOrdered P))
  exact ⟨restrictedInf P K V, fun _ hx => hx.2⟩

/-- If `P` is downward closed and holds for some level, the ordered levels satisfying `P` are
initial among all ordered levels; hence colimits over shrinking levels may be computed over
levels satisfying `P`. -/
instance restrictedForget_initial [IsDownwardClosed P] [Nonempty P.FullSubcategory] :
    (restrictedForget P).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro V
    obtain ⟨K, hK⟩ := exists_restrictedOrdered_le P V
    exact ⟨K, ⟨homOfLE hK⟩⟩
  · intro _ K _ _
    exact ⟨K, 𝟙 K, Subsingleton.elim _ _⟩

variable [IsConjStable P]

/-- The conjugate level `g K g⁻¹` of a level satisfying `P`. -/
def restrictedConj (g : G) (K : P.FullSubcategory) : P.FullSubcategory :=
  ⟨conjLevel g K.obj, IsConjStable.conjLevel g K.property⟩

@[simp] theorem restrictedConj_obj (g : G) (K : P.FullSubcategory) :
    (restrictedConj P g K).obj = conjLevel g K.obj := rfl

/-- Right translation by `g`, from the conjugate level `g K g⁻¹` to `K`. -/
def restrictedConjArrow (g : G) (K : P.FullSubcategory) : restrictedConj P g K ⟶ K :=
  ObjectProperty.homMk (conjArrow g K.obj)

@[simp] theorem restrictedConjArrow_hom (g : G) (K : P.FullSubcategory) :
    (restrictedConjArrow P g K).hom = conjArrow g K.obj := rfl

/-- Every arrow between levels satisfying `P` is an inclusion followed by a conjugation
arrow. -/
theorem eq_restrictedHom_comp_restrictedConjArrow {K L : P.FullSubcategory} (a : K ⟶ L) :
    a = restrictedHom P (K := K) (L := restrictedConj P a.hom.element L)
        (le_conjLevel a.hom) ≫ restrictedConjArrow P a.hom.element L :=
  P.hom_ext (eq_inclusion_comp_conjArrow a.hom)

theorem restrictedConjArrow_comp_restrictedHom (g : G) {K L : P.FullSubcategory}
    (h : K.obj.subgroup ≤ L.obj.subgroup) :
    restrictedConjArrow P g K ≫ restrictedHom P h =
      restrictedHom P (K := restrictedConj P g K) (L := restrictedConj P g L)
        (conjLevel_mono g h) ≫ restrictedConjArrow P g L :=
  P.hom_ext (conjArrow_comp_inclusion g h)

end TopologicalGroup

end CompactOpenLevel

namespace RestrictedLevelColimit

open CompactOpenLevel

variable {G : Type v} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}
  {C : Type u} [Category.{w} C]

/-- A presheaf on levels satisfying `P`, restricted to inclusions of levels. -/
abbrev diagram (F : P.FullSubcategoryᵒᵖ ⥤ C) : (RestrictedOrdered P)ᵒᵖ ⥤ C :=
  (restrictedInclusion P).op ⋙ F

/-- Each `k ∈ K` acts as the identity on level `K`. -/
def IsLevelTrivial (F : P.FullSubcategoryᵒᵖ ⥤ C) : Prop :=
  ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
    F.map (restrictedSelfArrow P K k hk).op = 𝟙 (F.obj (op K))

variable (P C) in
/-- Level-trivial presheaves on levels satisfying `P`, as a property of objects. -/
def levelTrivialProperty : ObjectProperty (P.FullSubcategoryᵒᵖ ⥤ C) :=
  fun F => IsLevelTrivial F

/-- A presheaf pulled back from a covariant functor on levels satisfying `P` is level-trivial
when each `k ∈ K` acts as the identity on level `K` of that functor. -/
theorem isLevelTrivial_op_comp {D : Type*} [Category D] (T : P.FullSubcategory ⥤ D)
    (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
      T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
    (E : Dᵒᵖ ⥤ C) : IsLevelTrivial (T.op ⋙ E) := by
  intro K k hk
  change E.map (T.map (restrictedSelfArrow P K k hk)).op = 𝟙 _
  rw [hT K k hk, op_id, E.map_id]

/-- The restriction of a level-trivial presheaf on all levels is level-trivial. -/
theorem isLevelTrivial_restrict {F : (CompactOpenLevel G)ᵒᵖ ⥤ C}
    (hF : LevelColimit.IsLevelTrivial F) : IsLevelTrivial (P.ι.op ⋙ F) :=
  fun K k hk => hF K.obj k hk

theorem diagram_map (F : P.FullSubcategoryᵒᵖ ⥤ C) {K L : (RestrictedOrdered P)ᵒᵖ} (h : K ⟶ L) :
    (diagram F).map h =
      F.map (restrictedHom P (K := ⟨L.unop.val, L.unop.property⟩)
        (L := ⟨K.unop.val, K.unop.property⟩) (leOfHom h.unop)).op := rfl

variable [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ C] (F : P.FullSubcategoryᵒᵖ ⥤ C)

/-- The inclusion of level `K` into the colimit over shrinking levels satisfying `P`. -/
def ι (K : P.FullSubcategory) : F.obj (op K) ⟶ colimit (diagram F) :=
  colimit.ι (diagram F) (op ⟨K.obj, K.property⟩)

@[reassoc (attr := simp)]
theorem map_restrictedHom_ι {K L : P.FullSubcategory} (h : K.obj.subgroup ≤ L.obj.subgroup) :
    F.map (restrictedHom P h).op ≫ ι F K = ι F L :=
  colimit.w (diagram F)
    (homOfLE (X := RestrictedOrdered P) (x := ⟨K.obj, K.property⟩)
      (y := ⟨L.obj, L.property⟩) h).op

theorem hom_ext {Y : C} {f f' : colimit (diagram F) ⟶ Y}
    (h : ∀ K : P.FullSubcategory, ι F K ≫ f = ι F K ≫ f') : f = f' :=
  colimit.hom_ext fun K => h ⟨K.unop.val, K.unop.property⟩

section Translate

variable [IsTopologicalGroup G] [IsConjStable P]

theorem translate_leg_naturality (g : G) {K L : P.FullSubcategory}
    (h : K.obj.subgroup ≤ L.obj.subgroup) :
    F.map (restrictedHom P h).op ≫ F.map (restrictedConjArrow P g K).op ≫
        ι F (restrictedConj P g K) =
      F.map (restrictedConjArrow P g L).op ≫ ι F (restrictedConj P g L) := by
  rw [← Category.assoc, ← F.map_comp, ← op_comp, restrictedConjArrow_comp_restrictedHom, op_comp,
    F.map_comp, Category.assoc]
  exact congrArg (F.map (restrictedConjArrow P g L).op ≫ ·)
    (map_restrictedHom_ι F (K := restrictedConj P g K) (L := restrictedConj P g L)
      (conjLevel_mono g h))

/-- The cocone whose level-`K` leg is translation by `g` into level `g K g⁻¹`. -/
def translateCocone (g : G) : Cocone (diagram F) where
  pt := colimit (diagram F)
  ι :=
    { app := fun K => F.map (restrictedConjArrow P g ⟨K.unop.val, K.unop.property⟩).op ≫
        ι F (restrictedConj P g ⟨K.unop.val, K.unop.property⟩)
      naturality := fun _ _ h =>
        (translate_leg_naturality F g (leOfHom h.unop)).trans (Category.comp_id _).symm }

/-- The action of `g` on the colimit over levels satisfying `P`. -/
def translate (g : G) : colimit (diagram F) ⟶ colimit (diagram F) :=
  colimit.desc (diagram F) (translateCocone F g)

@[reassoc]
theorem ι_translate (g : G) (K : P.FullSubcategory) :
    ι F K ≫ translate F g = F.map (restrictedConjArrow P g K).op ≫ ι F (restrictedConj P g K) :=
  colimit.ι_desc (translateCocone F g) (op ⟨K.obj, K.property⟩)

/-- Every arrow `a : K ⟶ L` between levels satisfying `P` is compatible with translation by
its element. -/
@[reassoc]
theorem map_ι {K L : P.FullSubcategory} (a : K ⟶ L) :
    F.map a.op ≫ ι F K = ι F L ≫ translate F a.hom.element := by
  conv_lhs => rw [eq_restrictedHom_comp_restrictedConjArrow P a]
  rw [op_comp, F.map_comp, Category.assoc, ι_translate]
  exact congrArg (F.map (restrictedConjArrow P a.hom.element L).op ≫ ·)
    (map_restrictedHom_ι F (K := K) (L := restrictedConj P a.hom.element L) (le_conjLevel a.hom))

theorem translate_one : translate F 1 = 𝟙 _ :=
  hom_ext F fun K => by
    have h := map_ι F (𝟙 K)
    rw [show (𝟙 K : K ⟶ K).hom.element = 1 from rfl, op_id, F.map_id, Category.id_comp] at h
    rw [← h, Category.comp_id]

theorem translate_mul (g h : G) : translate F (g * h) = translate F h ≫ translate F g :=
  hom_ext F fun L => by
    have e := map_ι F (restrictedConjArrow P g (restrictedConj P h L) ≫ restrictedConjArrow P h L)
    rw [show (restrictedConjArrow P g (restrictedConj P h L) ≫
        restrictedConjArrow P h L).hom.element = g * h from rfl] at e
    rw [← e, ι_translate_assoc, ι_translate, op_comp, F.map_comp, Category.assoc]

/-- The colimit over levels satisfying `P`, with `g` acting through the conjugate levels
`g K g⁻¹`. -/
def action : Action C G where
  V := colimit (diagram F)
  ρ :=
    { toFun := translate F
      map_one' := translate_one F
      map_mul' := fun g h => translate_mul F g h }

@[simp] theorem action_V : (action F).V = colimit (diagram F) := rfl

@[simp] theorem action_ρ (g : G) : (action F).ρ g = translate F g := rfl

theorem ι_translate_of_mem (hF : IsLevelTrivial F) {K : P.FullSubcategory} {k : G}
    (hk : k ∈ K.obj.subgroup) : ι F K ≫ translate F k = ι F K := by
  have h := map_ι F (restrictedSelfArrow P K k hk)
  rw [hF K k hk, Category.id_comp] at h
  exact h.symm

end Translate

section Map

variable {F} {F' F'' : P.FullSubcategoryᵒᵖ ⥤ C}

/-- The map of colimits over levels satisfying `P` induced by a natural transformation. -/
def map (α : F ⟶ F') : colimit (diagram F) ⟶ colimit (diagram F') :=
  colimMap (Functor.whiskerLeft (restrictedInclusion P).op α)

@[reassoc (attr := simp)]
theorem ι_map (α : F ⟶ F') (K : P.FullSubcategory) :
    ι F K ≫ map α = α.app (op K) ≫ ι F' K :=
  ι_colimMap _ _

theorem map_id : map (𝟙 F) = 𝟙 _ :=
  hom_ext F fun K => by simp

theorem map_comp (α : F ⟶ F') (β : F' ⟶ F'') : map (α ≫ β) = map α ≫ map β :=
  hom_ext F fun K => by simp

variable [IsTopologicalGroup G] [IsConjStable P]

@[reassoc]
theorem translate_map (α : F ⟶ F') (g : G) :
    translate F g ≫ map α = map α ≫ translate F' g :=
  hom_ext F fun K => by
    rw [ι_translate_assoc, ι_map, ι_map_assoc, ι_translate, α.naturality_assoc]

end Map

section Functor

variable [IsTopologicalGroup G] [IsConjStable P]

variable (P C) in
/-- Colimits over levels satisfying `P` as a functor to objects with an action of `G`. -/
def functor : (P.FullSubcategoryᵒᵖ ⥤ C) ⥤ Action C G where
  obj F := action F
  map α := ⟨map α, fun g => translate_map α g⟩
  map_id F := Action.Hom.ext (map_id (F := F))
  map_comp α β := Action.Hom.ext (map_comp α β)

@[simp] theorem functor_obj (F : P.FullSubcategoryᵒᵖ ⥤ C) : (functor P C).obj F = action F := rfl

@[simp] theorem functor_map_hom {F F' : P.FullSubcategoryᵒᵖ ⥤ C} (α : F ⟶ F') :
    ((functor P C).map α).hom = map α := rfl

variable (P C) in
/-- The underlying object of the colimit action is the ordinary colimit over inclusions. -/
def functorCompForgetIso :
    functor P C ⋙ Action.forget C G ≅
      (Functor.whiskeringLeft _ _ C).obj (restrictedInclusion P).op ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

section Smooth

variable {R : Type t} [CommRing R] [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]

/-- The colimit over levels satisfying `P` of a level-trivial presheaf of modules is smooth:
the image of level `K` is fixed by the open subgroup `K`. -/
theorem isSmooth_action (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) : IsSmooth ((Rep.ActionToRep R G).obj (action F)).ρ := by
  let S : Submodule R (action F).V :=
    smoothVectors ((Rep.ActionToRep R G).obj (action F)).ρ
  have hι : ∀ (K : P.FullSubcategory) (x : F.obj (op K)), (ι F K).hom x ∈ S := by
    intro K x
    refine ⟨K.obj.openSubgroup, ?_⟩
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
theorem translate_ι_apply_of_mem (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) {K : P.FullSubcategory} {k : G} (hk : k ∈ K.obj.subgroup)
    (x : F.obj (op K)) : (translate F k).hom ((ι F K).hom x) = (ι F K).hom x :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_translate_of_mem F hF hk)

/-- The action of `g` on a vector coming from level `K`: it comes from the conjugate level
`g K g⁻¹`, through the transition map of the arrow `g K g⁻¹ ⟶ K` with element `g`. -/
theorem translate_ι_apply (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R) (g : G)
    (K : P.FullSubcategory) (x : F.obj (op K)) :
    (translate F g).hom ((ι F K).hom x) =
      (ι F (restrictedConj P g K)).hom ((F.map (restrictedConjArrow P g K).op).hom x) :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_translate F g K)

omit [IsConjStable P] in
/-- If `P` is downward closed and holds for some level, every vector of the colimit comes from
a single level satisfying `P`. -/
theorem exists_ι_apply [IsDownwardClosed P] [Nonempty P.FullSubcategory]
    (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R)
    (x : (colimit (diagram F) : ModuleCat.{w} R)) :
    ∃ (K : P.FullSubcategory) (y : F.obj (op K)), (ι F K).hom y = x := by
  let S : Submodule R (colimit (diagram F) : ModuleCat.{w} R) :=
    { carrier := {x | ∃ (K : P.FullSubcategory) (y : F.obj (op K)), (ι F K).hom y = x}
      add_mem' := by
        rintro _ _ ⟨K, y, rfl⟩ ⟨L, z, rfl⟩
        let M : P.FullSubcategory := ⟨inf K.obj L.obj,
          IsDownwardClosed.of_le (fun _ hx => hx.1) K.property⟩
        have hK : M.obj.subgroup ≤ K.obj.subgroup := fun _ hx => hx.1
        have hL : M.obj.subgroup ≤ L.obj.subgroup := fun _ hx => hx.2
        refine ⟨M, (F.map (restrictedHom P hK).op).hom y +
          (F.map (restrictedHom P hL).op).hom z, ?_⟩
        rw [map_add, ← map_restrictedHom_ι F hK, ← map_restrictedHom_ι F hL]
        rfl
      zero_mem' := by
        obtain ⟨K⟩ := ‹Nonempty P.FullSubcategory›
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

/-- The smooth representation on the colimit over levels satisfying `P` of a level-trivial
presheaf. -/
def smoothRep (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F) :
    SmoothRep.{t, v, w} R G :=
  ⟨(Rep.ActionToRep R G).obj (action F), isSmooth_action F hF⟩

variable (P R) in
/-- Colimits over levels satisfying `P` of level-trivial presheaves of modules, as smooth
representations. -/
def smoothFunctor :
    (levelTrivialProperty P (ModuleCat.{w} R)).FullSubcategory ⥤ SmoothRep.{t, v, w} R G :=
  (smoothRepProperty R G).lift
    ((levelTrivialProperty P (ModuleCat.{w} R)).ι ⋙ functor P (ModuleCat.{w} R) ⋙
      Rep.ActionToRep R G)
    (fun F => isSmooth_action F.obj F.property)

@[simp] theorem smoothFunctor_obj_obj
    (F : (levelTrivialProperty P (ModuleCat.{w} R)).FullSubcategory) :
    ((smoothFunctor P R).obj F).obj = (Rep.ActionToRep R G).obj (action F.obj) := rfl

theorem smoothRep_ρ_ι_apply (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) (g : G) (K : P.FullSubcategory) (x : F.obj (op K)) :
    (smoothRep F hF).obj.ρ g ((ι F K).hom x) =
      (ι F (restrictedConj P g K)).hom ((F.map (restrictedConjArrow P g K).op).hom x) :=
  translate_ι_apply F g K x

end Smooth

end Functor

/-! ## Comparison with colimits over all levels -/

section Comparison

variable [IsTopologicalGroup G] [IsDownwardClosed P] [Nonempty P.FullSubcategory]
  [HasColimitsOfShape (Ordered G)ᵒᵖ C] (F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- For `P` downward closed and holding for some level, the colimit over levels satisfying `P`
of the restriction of a presheaf on all levels is its colimit over all levels. -/
def colimitRestrictIso :
    colimit (diagram (P.ι.op ⋙ F₀)) ≅ colimit (LevelColimit.diagram F₀) :=
  Functor.Final.colimitIso (restrictedForget P).op (LevelColimit.diagram F₀)

@[reassoc (attr := simp)]
theorem ι_colimitRestrictIso_hom (K : P.FullSubcategory) :
    ι (P.ι.op ⋙ F₀) K ≫ (colimitRestrictIso (P := P) F₀).hom = LevelColimit.ι F₀ K.obj :=
  Functor.Final.ι_colimitIso_hom (restrictedForget P).op (LevelColimit.diagram F₀)
    (op ⟨K.obj, K.property⟩)

@[reassoc (attr := simp)]
theorem ι_colimitRestrictIso_inv (K : P.FullSubcategory) :
    LevelColimit.ι F₀ K.obj ≫ (colimitRestrictIso (P := P) F₀).inv = ι (P.ι.op ⋙ F₀) K :=
  Functor.Final.ι_colimitIso_inv (restrictedForget P).op (LevelColimit.diagram F₀)
    (op ⟨K.obj, K.property⟩)

/-- The comparison of colimits is natural in the presheaf on all levels. -/
@[reassoc]
theorem map_colimitRestrictIso_hom {F₀ F₀' : (CompactOpenLevel G)ᵒᵖ ⥤ C} (α : F₀ ⟶ F₀') :
    map (Functor.whiskerLeft P.ι.op α) ≫ (colimitRestrictIso (P := P) F₀').hom =
      (colimitRestrictIso (P := P) F₀).hom ≫ LevelColimit.map α :=
  hom_ext _ fun K => by
    rw [ι_map_assoc, ι_colimitRestrictIso_hom, ι_colimitRestrictIso_hom_assoc,
      LevelColimit.ι_map]
    rfl

variable [IsConjStable P]

/-- The comparison of colimits is compatible with the actions of `G`. -/
@[reassoc]
theorem translate_colimitRestrictIso_hom (g : G) :
    translate (P.ι.op ⋙ F₀) g ≫ (colimitRestrictIso (P := P) F₀).hom =
      (colimitRestrictIso (P := P) F₀).hom ≫ LevelColimit.translate F₀ g :=
  hom_ext _ fun K => by
    rw [ι_translate_assoc, ι_colimitRestrictIso_hom, ι_colimitRestrictIso_hom_assoc,
      LevelColimit.ι_translate]
    rfl

/-- For `P` conjugation stable, downward closed and holding for some level, the colimit action
over levels satisfying `P` of a restricted presheaf is the colimit action over all levels. -/
def actionRestrictIso : action (P.ι.op ⋙ F₀) ≅ LevelColimit.action F₀ :=
  Action.mkIso (colimitRestrictIso F₀) (translate_colimitRestrictIso_hom F₀)

@[simp] theorem actionRestrictIso_hom_hom :
    (actionRestrictIso (P := P) F₀).hom.hom = (colimitRestrictIso F₀).hom := rfl

variable (P C) in
/-- The comparison of colimit actions, natural in the presheaf on all levels. -/
def functorRestrictIso :
    (Functor.whiskeringLeft _ _ C).obj P.ι.op ⋙ functor P C ≅ LevelColimit.functor G C :=
  NatIso.ofComponents (fun F₀ => actionRestrictIso F₀) (fun α =>
    Action.Hom.ext (map_colimitRestrictIso_hom α))

section Smooth

variable {R : Type t} [CommRing R] [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]

/-- For a level-trivial presheaf of modules on all levels, the smooth representation over
levels satisfying `P` of its restriction is the smooth representation over all levels. -/
def smoothRepRestrictIso (F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF₀ : LevelColimit.IsLevelTrivial F₀) :
    smoothRep (P.ι.op ⋙ F₀) (isLevelTrivial_restrict hF₀) ≅
      LevelColimit.smoothRep (G := G) (R := R) F₀ hF₀ :=
  ObjectProperty.isoMk _ ((Rep.ActionToRep R G).mapIso (actionRestrictIso F₀))

theorem smoothRepRestrictIso_hom_ι_apply (F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF₀ : LevelColimit.IsLevelTrivial F₀) (K : P.FullSubcategory) (x : F₀.obj (op K.obj)) :
    (smoothRepRestrictIso (P := P) F₀ hF₀).hom.hom.hom ((ι (P.ι.op ⋙ F₀) K).hom x) =
      (LevelColimit.ι F₀ K.obj).hom x :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_colimitRestrictIso_hom F₀ K)

end Smooth

end Comparison

end RestrictedLevelColimit

end Langlands.Shimura
