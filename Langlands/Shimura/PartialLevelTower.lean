import Langlands.Shimura.LevelColimit

/-! # Level functors over group homomorphisms and partial level towers -/

noncomputable section

universe u v v' w t

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

section Over

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]

/-- A functor of level categories lying over a group homomorphism `φ`: an arrow with element
`h` goes to an arrow with element `φ h`, and `φ` maps each level into its image level. -/
structure FunctorOver (φ : H →* G) where
  /-- The underlying functor of level categories. -/
  functor : CompactOpenLevel H ⥤ CompactOpenLevel G
  map_element {K L : CompactOpenLevel H} (a : K ⟶ L) : (functor.map a).element = φ a.element
  map_mem (K : CompactOpenLevel H) {k : H} (hk : k ∈ K.subgroup) :
    φ k ∈ (functor.obj K).subgroup

namespace FunctorOver

variable {φ : H →* G} (Φ : FunctorOver φ)

theorem le_of_le {K L : CompactOpenLevel H} (h : K.subgroup ≤ L.subgroup) :
    (Φ.functor.obj K).subgroup ≤ (Φ.functor.obj L).subgroup := fun x hx => by
  have e := (Φ.functor.map (inclusion h)).respects x hx
  rwa [Φ.map_element, show (inclusion h).element = 1 from rfl, map_one, inv_one, one_mul,
    mul_one] at e

theorem map_inclusion {K L : CompactOpenLevel H} (h : K.subgroup ≤ L.subgroup) :
    Φ.functor.map (inclusion h) = inclusion (Φ.le_of_le h) :=
  Arrow.ext ((Φ.map_element _).trans (map_one φ))

theorem map_selfArrow (K : CompactOpenLevel H) (k : H) (hk : k ∈ K.subgroup) :
    Φ.functor.map (selfArrow K k hk) = selfArrow _ (φ k) (Φ.map_mem K hk) :=
  Arrow.ext (Φ.map_element _)

/-- The induced functor of ordered levels. -/
def ordered : Ordered H ⥤ Ordered G where
  obj K := (Φ.functor.obj K : CompactOpenLevel G)
  map h := homOfLE (Φ.le_of_le (leOfHom h))

/-- The identity functor of levels, over the identity homomorphism. -/
def id (E : Type t) [Group E] [TopologicalSpace E] : FunctorOver (MonoidHom.id E) where
  functor := 𝟭 _
  map_element _ := rfl
  map_mem _ _ hk := hk

/-- The composite of functors of levels over the composite homomorphism. -/
def comp {E : Type t} [Group E] [TopologicalSpace E] {ψ : G →* E} (Ψ : FunctorOver ψ) :
    FunctorOver (ψ.comp φ) where
  functor := Φ.functor ⋙ Ψ.functor
  map_element a := (Ψ.map_element _).trans (congrArg ψ (Φ.map_element a))
  map_mem K _ hk := Ψ.map_mem _ (Φ.map_mem K hk)

@[simp] theorem comp_functor {E : Type t} [Group E] [TopologicalSpace E] {ψ : G →* E}
    (Ψ : FunctorOver ψ) : (Φ.comp Ψ).functor = Φ.functor ⋙ Ψ.functor := rfl

end FunctorOver

end Over

section Prod

variable {H : Type v} {H' : Type v'} [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H']

/-- The product `K × K'` of compact open levels, a compact open level of `H × H'`. -/
def prod (K : CompactOpenLevel H) (K' : CompactOpenLevel H') : CompactOpenLevel (H × H') where
  openSubgroup := K.openSubgroup.prod K'.openSubgroup
  isCompact := by
    rw [OpenSubgroup.coe_prod]
    exact K.isCompact.prod K'.isCompact

theorem mem_prod {K : CompactOpenLevel H} {K' : CompactOpenLevel H'} {x : H × H'} :
    x ∈ (prod K K').subgroup ↔ x.1 ∈ K.subgroup ∧ x.2 ∈ K'.subgroup :=
  Iff.rfl

theorem prod_mono {K L : CompactOpenLevel H} {K' L' : CompactOpenLevel H'}
    (h : K.subgroup ≤ L.subgroup) (h' : K'.subgroup ≤ L'.subgroup) :
    (prod K K').subgroup ≤ (prod L L').subgroup :=
  fun _ hx => ⟨h hx.1, h' hx.2⟩

/-- The product of two level arrows, with element the pair of their elements. -/
def prodArrow {K L : CompactOpenLevel H} {K' L' : CompactOpenLevel H'} (a : K ⟶ L)
    (a' : K' ⟶ L') : prod K K' ⟶ prod L L' :=
  ⟨(a.element, a'.element), fun x hx => ⟨a.respects x.1 hx.1, a'.respects x.2 hx.2⟩⟩

@[simp] theorem prodArrow_element {K L : CompactOpenLevel H} {K' L' : CompactOpenLevel H'}
    (a : K ⟶ L) (a' : K' ⟶ L') : (prodArrow a a').element = (a.element, a'.element) := rfl

theorem prodArrow_id (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    prodArrow (𝟙 K) (𝟙 K') = 𝟙 (prod K K') :=
  Arrow.ext rfl

theorem prodArrow_comp {K L M : CompactOpenLevel H} {K' L' M' : CompactOpenLevel H'}
    (a : K ⟶ L) (b : L ⟶ M) (a' : K' ⟶ L') (b' : L' ⟶ M') :
    prodArrow (a ≫ b) (a' ≫ b') = prodArrow a a' ≫ prodArrow b b' :=
  Arrow.ext rfl

variable (H H') in
/-- Products of levels, as a functor of two variables. -/
def prodFunctor : CompactOpenLevel H ⥤ CompactOpenLevel H' ⥤ CompactOpenLevel (H × H') where
  obj K :=
    { obj := prod K
      map := fun a' => prodArrow (𝟙 K) a'
      map_id := fun K' => prodArrow_id K K'
      map_comp := fun a' b' => by
        rw [← prodArrow_comp, Category.comp_id] }
  map a :=
    { app := fun K' => prodArrow a (𝟙 K')
      naturality := fun _ _ a' => by
        dsimp only
        rw [← prodArrow_comp, ← prodArrow_comp, Category.id_comp, Category.comp_id,
          Category.id_comp, Category.comp_id] }
  map_id K := by
    ext K'
    exact prodArrow_id K K'
  map_comp a b := by
    ext K'
    change prodArrow (a ≫ b) (𝟙 K') = prodArrow a (𝟙 K') ≫ prodArrow b (𝟙 K')
    rw [← prodArrow_comp, Category.comp_id]

@[simp] theorem prodFunctor_obj_obj (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    ((prodFunctor H H').obj K).obj K' = prod K K' := rfl

@[simp] theorem prodFunctor_obj_map (K : CompactOpenLevel H) {K' L' : CompactOpenLevel H'}
    (a' : K' ⟶ L') : ((prodFunctor H H').obj K).map a' = prodArrow (𝟙 K) a' := rfl

@[simp] theorem prodFunctor_map_app {K L : CompactOpenLevel H} (a : K ⟶ L)
    (K' : CompactOpenLevel H') : ((prodFunctor H H').map a).app K' = prodArrow a (𝟙 K') := rfl

/-- The levels `K₀ × K'` with the first factor fixed, over the inclusion `H' → H × H'` of the
second factor. -/
def withLeft (K₀ : CompactOpenLevel H) : FunctorOver (MonoidHom.inr H H') where
  functor := (prodFunctor H H').obj K₀
  map_element _ := rfl
  map_mem _ _ hk := ⟨K₀.subgroup.one_mem, hk⟩

/-- The levels `K × K₀'` with the second factor fixed, over the inclusion `H → H × H'` of the
first factor. -/
def withRight (K₀' : CompactOpenLevel H') : FunctorOver (MonoidHom.inl H H') where
  functor := (prodFunctor H H').flip.obj K₀'
  map_element _ := rfl
  map_mem _ _ hk := ⟨hk, K₀'.subgroup.one_mem⟩

@[simp] theorem withLeft_functor (K₀ : CompactOpenLevel H) :
    (withLeft (H' := H') K₀).functor = (prodFunctor H H').obj K₀ := rfl

@[simp] theorem withRight_functor (K₀' : CompactOpenLevel H') :
    (withRight (H := H) K₀').functor = (prodFunctor H H').flip.obj K₀' := rfl

end Prod

end CompactOpenLevel

namespace LevelColimit

open CompactOpenLevel

section Reindex

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {C : Type u} [Category.{w} C] {φ : H →* G} (Φ : FunctorOver φ)

/-- The presheaf on the levels of `H` obtained from a presheaf on the levels of `G` by
restriction along `Φ`. -/
abbrev reindex (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) : (CompactOpenLevel H)ᵒᵖ ⥤ C :=
  Φ.functor.op ⋙ F

variable (C) in
/-- Restriction along `Φ`, as a functor of presheaves on levels. -/
abbrev reindexFunctor :
    ((CompactOpenLevel G)ᵒᵖ ⥤ C) ⥤ ((CompactOpenLevel H)ᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj Φ.functor.op

theorem isLevelTrivial_reindex {F : (CompactOpenLevel G)ᵒᵖ ⥤ C} (hF : IsLevelTrivial F) :
    IsLevelTrivial (reindex Φ F) := by
  intro K k hk
  change F.map (Φ.functor.map (selfArrow K k hk)).op = 𝟙 _
  rw [Φ.map_selfArrow]
  exact hF _ _ _

variable [HasColimitsOfShape (Ordered H)ᵒᵖ C] [HasColimitsOfShape (Ordered G)ᵒᵖ C]
  (F : (CompactOpenLevel G)ᵒᵖ ⥤ C)

omit [HasColimitsOfShape (Ordered H)ᵒᵖ C] in
theorem map_reindex_inclusion_ι {K L : CompactOpenLevel H} (h : K.subgroup ≤ L.subgroup) :
    F.map (Φ.functor.map (inclusion h)).op ≫ ι F (Φ.functor.obj K) = ι F (Φ.functor.obj L) := by
  rw [Φ.map_inclusion, map_inclusion_ι]

/-- The cocone on the reindexed diagram whose level-`K` leg is the inclusion of level `Φ K`
into the colimit of `F`. -/
def reindexCocone : Cocone (diagram (reindex Φ F)) where
  pt := colimit (diagram F)
  ι :=
    { app := fun K => ι F (Φ.functor.obj K.unop)
      naturality := fun _ _ h =>
        (map_reindex_inclusion_ι Φ F (leOfHom h.unop)).trans (Category.comp_id _).symm }

/-- The comparison map from the colimit of the reindexed presheaf to the colimit of `F`. -/
def reindexComparison : colimit (diagram (reindex Φ F)) ⟶ colimit (diagram F) :=
  colimit.desc _ (reindexCocone Φ F)

@[reassoc (attr := simp)]
theorem ι_reindexComparison (K : CompactOpenLevel H) :
    ι (reindex Φ F) K ≫ reindexComparison Φ F = ι F (Φ.functor.obj K) :=
  colimit.ι_desc (reindexCocone Φ F) (op K)

variable {F} in
@[reassoc]
theorem map_reindexComparison {F' : (CompactOpenLevel G)ᵒᵖ ⥤ C} (α : F ⟶ F') :
    map (Functor.whiskerLeft Φ.functor.op α) ≫ reindexComparison Φ F' =
      reindexComparison Φ F ≫ map α :=
  hom_ext _ fun K => by
    rw [ι_map_assoc, ι_reindexComparison, ι_reindexComparison_assoc, ι_map]
    rfl

section Translate

variable [IsTopologicalGroup H] [IsTopologicalGroup G]

/-- The comparison map intertwines translation by `h` with translation by `φ h`. -/
@[reassoc]
theorem translate_reindexComparison (h : H) :
    translate (reindex Φ F) h ≫ reindexComparison Φ F =
      reindexComparison Φ F ≫ translate F (φ h) :=
  hom_ext (reindex Φ F) fun K => by
    have e := map_ι F (Φ.functor.map (conjArrow h K))
    rw [Φ.map_element, conjArrow_element] at e
    rw [ι_translate_assoc, ι_reindexComparison, ι_reindexComparison_assoc]
    exact e

/-- The comparison map as a morphism of objects with an action of `H`, where `H` acts on the
colimit of `F` through `φ`. -/
def reindexComparisonHom : action (reindex Φ F) ⟶ (Action.res C φ).obj (action F) where
  hom := reindexComparison Φ F
  comm h := translate_reindexComparison Φ F h

@[simp] theorem reindexComparisonHom_hom :
    (reindexComparisonHom Φ F).hom = reindexComparison Φ F := rfl

variable (C) in
/-- The comparison maps, natural in the presheaf on the levels of `G`. -/
def reindexComparisonNatTrans :
    reindexFunctor C Φ ⋙ functor H C ⟶ functor G C ⋙ Action.res C φ where
  app F := reindexComparisonHom Φ F
  naturality _ _ α := Action.Hom.ext (map_reindexComparison Φ α)

@[simp] theorem reindexComparisonNatTrans_app :
    (reindexComparisonNatTrans C Φ).app F = reindexComparisonHom Φ F := rfl

end Translate

section Smooth

variable [IsTopologicalGroup H] [IsTopologicalGroup G] {R : Type t} [CommRing R]
  [HasColimitsOfShape (Ordered H)ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]

omit [IsTopologicalGroup H] [IsTopologicalGroup G] in
theorem reindexComparison_ι_apply (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (K : CompactOpenLevel H) (x : F.obj (op (Φ.functor.obj K))) :
    (reindexComparison Φ F).hom ((ι (reindex Φ F) K).hom x) = (ι F (Φ.functor.obj K)).hom x :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_reindexComparison Φ F K)

/-- An element `g` lying in every level `Φ K` fixes the image of the comparison map. -/
theorem translate_reindexComparison_apply_of_mem [Nonempty (CompactOpenLevel H)]
    (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F) {g : G}
    (hg : ∀ K : CompactOpenLevel H, g ∈ (Φ.functor.obj K).subgroup)
    (x : (colimit (diagram (reindex Φ F)) : ModuleCat.{w} R)) :
    (translate F g).hom ((reindexComparison Φ F).hom x) = (reindexComparison Φ F).hom x := by
  obtain ⟨K, y, rfl⟩ := exists_ι_apply (reindex Φ F) x
  rw [reindexComparison_ι_apply]
  exact translate_ι_apply_of_mem F hF (hg K) y

end Smooth

end Reindex

section Partial

variable {H : Type v} {H' : Type v'} [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] {C : Type u} [Category.{w} C]

/-- The partial tower `K' ↦ F (K₀ × K')` of a presheaf on the levels of `H × H'`, with the
first factor `K₀` of the level fixed. -/
abbrev partialTower (K₀ : CompactOpenLevel H) (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C) :
    (CompactOpenLevel H')ᵒᵖ ⥤ C :=
  reindex (withLeft K₀) F

/-- The partial towers as a presheaf on the levels of `H`, with values presheaves on the levels
of `H'`: an arrow `a : K₀ ⟶ K₁` acts through the arrows `K₀ × K' ⟶ K₁ × K'` with element
`(a.element, 1)`. -/
def partialTowerFunctor (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C) :
    (CompactOpenLevel H)ᵒᵖ ⥤ (CompactOpenLevel H')ᵒᵖ ⥤ C :=
  (prodFunctor H H').op ⋙ Functor.opHom _ _ ⋙ (Functor.whiskeringRight _ _ C).obj F

@[simp] theorem partialTowerFunctor_obj (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)
    (K₀ : CompactOpenLevel H) : (partialTowerFunctor F).obj (op K₀) = partialTower K₀ F := rfl

theorem partialTowerFunctor_map_app (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)
    {K₀ K₁ : CompactOpenLevel H} (a : K₀ ⟶ K₁) (K' : CompactOpenLevel H') :
    ((partialTowerFunctor F).map a.op).app (op K') = F.map (prodArrow a (𝟙 K')).op := rfl

/-- The transition `partialTower K₁ F ⟶ partialTower K₀ F` along `a : K₀ ⟶ K₁`, the map of
`partialTowerFunctor F` at `a`. -/
def partialTowerMap (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C) {K₀ K₁ : CompactOpenLevel H}
    (a : K₀ ⟶ K₁) : partialTower K₁ F ⟶ partialTower K₀ F :=
  (partialTowerFunctor F).map a.op

theorem partialTowerMap_app (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)
    {K₀ K₁ : CompactOpenLevel H} (a : K₀ ⟶ K₁) (K' : CompactOpenLevel H') :
    (partialTowerMap F a).app (op K') = F.map (prodArrow a (𝟙 K')).op := rfl

theorem isLevelTrivial_partialTower (K₀ : CompactOpenLevel H)
    {F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C} (hF : IsLevelTrivial F) :
    IsLevelTrivial (partialTower K₀ F) :=
  isLevelTrivial_reindex _ hF

theorem isLevelTrivial_partialTowerFunctor {F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C}
    (hF : IsLevelTrivial F) : IsLevelTrivial (partialTowerFunctor F) := by
  intro K₀ k hk
  ext K'
  rw [partialTowerFunctor_map_app, NatTrans.id_app]
  exact hF (prod K₀ K'.unop) (k, 1) ⟨hk, K'.unop.subgroup.one_mem⟩

section Colimit

variable [HasColimitsOfShape (Ordered H')ᵒᵖ C]

/-- The colimits of the partial towers, as a presheaf on the levels of `H` with values objects
with an action of `H'`. -/
def partialColimitFunctor (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C) [IsTopologicalGroup H'] :
    (CompactOpenLevel H)ᵒᵖ ⥤ Action C H' :=
  partialTowerFunctor F ⋙ functor H' C

@[simp] theorem partialColimitFunctor_obj (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)
    [IsTopologicalGroup H'] (K₀ : CompactOpenLevel H) :
    (partialColimitFunctor F).obj (op K₀) = action (partialTower K₀ F) := rfl

theorem isLevelTrivial_partialColimitFunctor [IsTopologicalGroup H']
    {F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C} (hF : IsLevelTrivial F) :
    IsLevelTrivial (partialColimitFunctor F) := by
  intro K₀ k hk
  change (functor H' C).map ((partialTowerFunctor F).map (selfArrow K₀ k hk).op) = _
  rw [isLevelTrivial_partialTowerFunctor hF K₀ k hk, CategoryTheory.Functor.map_id]
  rfl

variable [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C] [IsTopologicalGroup H]
  [IsTopologicalGroup H'] (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)

/-- The comparison from the colimit of the partial tower at `K₀` to the colimit over all levels
of `H × H'`, equivariant for `H' → H × H'`. -/
abbrev partialComparisonHom (K₀ : CompactOpenLevel H) :
    action (partialTower K₀ F) ⟶ (Action.res C (MonoidHom.inr H H')).obj (action F) :=
  reindexComparisonHom (withLeft K₀) F

/-- The transition of partial colimits along `a : K₀ ⟶ K₁`, followed by the comparison at `K₀`,
is the comparison at `K₁` followed by translation by `(a.element, 1)`. -/
@[reassoc]
theorem partialColimitFunctor_map_comparison {K₀ K₁ : CompactOpenLevel H} (a : K₀ ⟶ K₁) :
    ((partialColimitFunctor F).map a.op).hom ≫ reindexComparison (withLeft K₀) F =
      reindexComparison (withLeft K₁) F ≫ translate F (a.element, 1) :=
  hom_ext (partialTower K₁ F) fun K' => by
    change ι (partialTower K₁ F) K' ≫ map (partialTowerMap F a) ≫
        reindexComparison (withLeft K₀) F =
      ι (partialTower K₁ F) K' ≫ reindexComparison (withLeft K₁) F ≫ translate F (a.element, 1)
    rw [ι_map_assoc, partialTowerMap_app, ι_reindexComparison (withLeft K₀) F K',
      ι_reindexComparison_assoc (withLeft K₁) F K']
    exact map_ι F (prodArrow a (𝟙 K'))

end Colimit

section Smooth

variable [IsTopologicalGroup H] [IsTopologicalGroup H'] {R : Type t} [CommRing R]
  [HasColimitsOfShape (Ordered H')ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ (ModuleCat.{w} R)]

/-- The image of the partial colimit at `K₀` is fixed by `K₀ × 1`. -/
theorem translate_partialComparison_apply_of_mem [Nonempty (CompactOpenLevel H')]
    (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F)
    (K₀ : CompactOpenLevel H) {k : H} (hk : k ∈ K₀.subgroup)
    (x : (colimit (diagram (partialTower K₀ F)) : ModuleCat.{w} R)) :
    (translate F (k, 1)).hom ((reindexComparison (withLeft K₀) F).hom x) =
      (reindexComparison (withLeft K₀) F).hom x :=
  translate_reindexComparison_apply_of_mem (withLeft K₀) F hF
    (fun K' => ⟨hk, K'.subgroup.one_mem⟩) x

end Smooth

end Partial

end LevelColimit

end Langlands.Shimura
