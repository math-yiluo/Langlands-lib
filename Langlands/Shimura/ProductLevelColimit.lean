import Langlands.Shimura.PartialLevelTower

/-! # Cofinality of product levels and iterated colimits over partial level towers -/

noncomputable section

universe u v v' w

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

section Inclusion

variable {G : Type v} [Group G] [TopologicalSpace G]

theorem inclusion_comp_inclusion {K L M : CompactOpenLevel G} (h₁ : K.subgroup ≤ L.subgroup)
    (h₂ : L.subgroup ≤ M.subgroup) : inclusion h₁ ≫ inclusion h₂ = inclusion (h₁.trans h₂) :=
  Arrow.ext (mul_one 1)

theorem inclusion_eq_id {K : CompactOpenLevel G} (h : K.subgroup ≤ K.subgroup) :
    inclusion h = 𝟙 K :=
  Arrow.ext rfl

end Inclusion

section Factor

variable {H : Type v} {H' : Type v'} [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H']

theorem prodArrow_inclusion {K L : CompactOpenLevel H} {K' L' : CompactOpenLevel H'}
    (h : K.subgroup ≤ L.subgroup) (h' : K'.subgroup ≤ L'.subgroup) :
    prodArrow (inclusion h) (inclusion h') = inclusion (prod_mono h h') :=
  Arrow.ext rfl

variable [IsTopologicalGroup H] [IsTopologicalGroup H']

/-- The first factor `{h | (h, 1) ∈ K}` of a compact open level `K` of `H × H'`. -/
def leftFactor (K : CompactOpenLevel (H × H')) : CompactOpenLevel H where
  openSubgroup := K.openSubgroup.comap (MonoidHom.inl H H') (continuous_id.prodMk continuous_const)
  isCompact := (K.isCompact.image continuous_fst).of_isClosed_subset (OpenSubgroup.isClosed _)
    fun h hh => ⟨(h, 1), hh, rfl⟩

/-- The second factor `{h' | (1, h') ∈ K}` of a compact open level `K` of `H × H'`. -/
def rightFactor (K : CompactOpenLevel (H × H')) : CompactOpenLevel H' where
  openSubgroup := K.openSubgroup.comap (MonoidHom.inr H H') (continuous_const.prodMk continuous_id)
  isCompact := (K.isCompact.image continuous_snd).of_isClosed_subset (OpenSubgroup.isClosed _)
    fun h' hh' => ⟨(1, h'), hh', rfl⟩

omit [IsTopologicalGroup H'] in
theorem mem_leftFactor {K : CompactOpenLevel (H × H')} {h : H} :
    h ∈ (leftFactor K).subgroup ↔ ((h, 1) : H × H') ∈ K.subgroup :=
  Iff.rfl

omit [IsTopologicalGroup H] in
theorem mem_rightFactor {K : CompactOpenLevel (H × H')} {h' : H'} :
    h' ∈ (rightFactor K).subgroup ↔ ((1, h') : H × H') ∈ K.subgroup :=
  Iff.rfl

/-- Every compact open level of `H × H'` contains the product of its two factors. -/
theorem prod_leftFactor_rightFactor_le (K : CompactOpenLevel (H × H')) :
    (prod (leftFactor K) (rightFactor K)).subgroup ≤ K.subgroup := fun x hx => by
  have e : x = ((x.1, 1) : H × H') * ((1, x.2) : H × H') := by
    ext <;> simp
  rw [e]
  exact K.subgroup.mul_mem hx.1 hx.2

omit [IsTopologicalGroup H'] in
theorem leftFactor_mono {K L : CompactOpenLevel (H × H')} (h : K.subgroup ≤ L.subgroup) :
    (leftFactor K).subgroup ≤ (leftFactor L).subgroup :=
  fun _ hx => h hx

omit [IsTopologicalGroup H] in
theorem rightFactor_mono {K L : CompactOpenLevel (H × H')} (h : K.subgroup ≤ L.subgroup) :
    (rightFactor K).subgroup ≤ (rightFactor L).subgroup :=
  fun _ hx => h hx

omit [IsTopologicalGroup H'] in
theorem le_leftFactor_prod (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    K.subgroup ≤ (leftFactor (prod K K')).subgroup :=
  fun _ hx => ⟨hx, K'.subgroup.one_mem⟩

omit [IsTopologicalGroup H] in
theorem le_rightFactor_prod (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    K'.subgroup ≤ (rightFactor (prod K K')).subgroup :=
  fun _ hx => ⟨K.subgroup.one_mem, hx⟩

omit [IsTopologicalGroup H'] in
theorem leftFactor_prod_le (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    (leftFactor (prod K K')).subgroup ≤ K.subgroup :=
  fun _ hx => hx.1

omit [IsTopologicalGroup H] in
theorem rightFactor_prod_le (K : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    (rightFactor (prod K K')).subgroup ≤ K'.subgroup :=
  fun _ hx => hx.2

/-- Product levels are cofinal among the compact open levels of `H × H'`. -/
theorem exists_prod_le (K : CompactOpenLevel (H × H')) :
    ∃ (K₁ : CompactOpenLevel H) (K₂ : CompactOpenLevel H'), (prod K₁ K₂).subgroup ≤ K.subgroup :=
  ⟨leftFactor K, rightFactor K, prod_leftFactor_rightFactor_le K⟩

end Factor

end CompactOpenLevel

namespace LevelColimit

open CompactOpenLevel

section Iterated

variable {H : Type v} {H' : Type v'} [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] [IsTopologicalGroup H'] {C : Type u} [Category.{w} C]
  [HasColimitsOfShape (Ordered H')ᵒᵖ C]

/-- The colimits of the partial towers `K' ↦ F (K₀ × K')`, as a presheaf on the levels of `H`. -/
abbrev partialColimit (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C) : (CompactOpenLevel H)ᵒᵖ ⥤ C :=
  partialColimitFunctor F ⋙ Action.forget C H'

theorem isLevelTrivial_partialColimit {F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C}
    (hF : IsLevelTrivial F) : IsLevelTrivial (partialColimit F) := by
  intro K₀ k hk
  change (Action.forget C H').map ((partialColimitFunctor F).map (selfArrow K₀ k hk).op) = _
  rw [isLevelTrivial_partialColimitFunctor hF K₀ k hk]
  exact (Action.forget C H').map_id _

variable [HasColimitsOfShape (Ordered H)ᵒᵖ C] (F : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C)

/-- The inclusion of the colimit of the partial tower at `K₀` into the iterated colimit
`colim_{K₀} colim_{K'} F (K₀ × K')`. -/
def ιPartial (K₀ : CompactOpenLevel H) :
    colimit (diagram (partialTower K₀ F)) ⟶ colimit (diagram (partialColimit F)) :=
  ι (partialColimit F) K₀

@[reassoc (attr := simp)]
theorem map_partialTowerMap_ιPartial {K₀ K₁ : CompactOpenLevel H}
    (h : K₀.subgroup ≤ K₁.subgroup) :
    map (partialTowerMap F (inclusion h)) ≫ ιPartial F K₀ = ιPartial F K₁ :=
  map_inclusion_ι (partialColimit F) h

theorem ιPartial_hom_ext {Y : C} {f f' : colimit (diagram (partialColimit F)) ⟶ Y}
    (h : ∀ K₀ : CompactOpenLevel H, ιPartial F K₀ ≫ f = ιPartial F K₀ ≫ f') : f = f' :=
  hom_ext (partialColimit F) h

/-- The inclusion of level `K₀ × K'` into the colimit of the partial tower at `K₀`. -/
def ιTower (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    F.obj (op (prod K₀ K')) ⟶ colimit (diagram (partialTower K₀ F)) :=
  ι (partialTower K₀ F) K'

omit [IsTopologicalGroup H'] [HasColimitsOfShape (Ordered H)ᵒᵖ C] in
theorem ιTower_hom_ext (K₀ : CompactOpenLevel H) {Y : C}
    {f f' : colimit (diagram (partialTower K₀ F)) ⟶ Y}
    (h : ∀ K' : CompactOpenLevel H', ιTower F K₀ K' ≫ f = ιTower F K₀ K' ≫ f') : f = f' :=
  hom_ext (partialTower K₀ F) h

/-- The inclusion of level `K₀ × K'` into the iterated colimit, through the partial colimit at
`K₀`. -/
def ι₂ (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    F.obj (op (prod K₀ K')) ⟶ colimit (diagram (partialColimit F)) :=
  ιTower F K₀ K' ≫ ιPartial F K₀

theorem ι₂_def (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    ι₂ F K₀ K' = ιTower F K₀ K' ≫ ιPartial F K₀ :=
  rfl

@[reassoc]
theorem map_inclusion_ι₂ {K₀ K₁ : CompactOpenLevel H} {K' K₂ : CompactOpenLevel H'}
    (h : K₀.subgroup ≤ K₁.subgroup) (h' : K'.subgroup ≤ K₂.subgroup) :
    F.map (inclusion (prod_mono h h')).op ≫ ι₂ F K₀ K' = ι₂ F K₁ K₂ := by
  have e1 : ιTower F K₁ K' ≫ map (partialTowerMap F (inclusion h)) =
      F.map (prodArrow (inclusion h) (𝟙 K')).op ≫ ιTower F K₀ K' :=
    ι_map (partialTowerMap F (inclusion h)) K'
  have e2 : F.map (prodArrow (𝟙 K₁) (inclusion h')).op ≫ ιTower F K₁ K' = ιTower F K₁ K₂ :=
    map_inclusion_ι (partialTower K₁ F) h'
  have e3 : inclusion (prod_mono h h') =
      prodArrow (inclusion h) (𝟙 K') ≫ prodArrow (𝟙 K₁) (inclusion h') := by
    rw [← prodArrow_comp, Category.comp_id, Category.id_comp, prodArrow_inclusion]
  rw [ι₂_def, ι₂_def, e3, op_comp, F.map_comp, Category.assoc,
    ← Category.assoc (F.map (prodArrow (inclusion h) (𝟙 K')).op), ← e1, Category.assoc,
    map_partialTowerMap_ιPartial, ← Category.assoc, e2]

/-- `ι₂` is compatible with the inclusion `prod K₁ K₂ ≤ prod K₀ K'` when also
`K₀ ≤ K₁` and `K' ≤ K₂`, so that the two product levels have the same subgroup. -/
theorem map_inclusion_ι₂_of_le {K₀ K₁ : CompactOpenLevel H} {K' K₂ : CompactOpenLevel H'}
    (h : K₀.subgroup ≤ K₁.subgroup) (h' : K'.subgroup ≤ K₂.subgroup)
    (hle : (prod K₁ K₂).subgroup ≤ (prod K₀ K').subgroup) :
    F.map (inclusion hle).op ≫ ι₂ F K₁ K₂ = ι₂ F K₀ K' := by
  rw [← map_inclusion_ι₂ F h h', ← Category.assoc, ← F.map_comp, ← op_comp,
    inclusion_comp_inclusion, inclusion_eq_id, op_id, F.map_id, Category.id_comp]

/-- Translation by `h' ∈ H'` on the partial colimits, natural in the level of `H`. -/
def partialTranslate (h' : H') : partialColimit F ⟶ partialColimit F where
  app K₀ := translate (partialTower K₀.unop F) h'
  naturality _ _ a := (((partialColimitFunctor F).map a).comm h').symm

/-- Translation by `h' ∈ H'` on the iterated colimit. -/
def iteratedTranslate (h' : H') :
    colimit (diagram (partialColimit F)) ⟶ colimit (diagram (partialColimit F)) :=
  map (partialTranslate F h')

@[reassoc]
theorem ιPartial_iteratedTranslate (h' : H') (K₀ : CompactOpenLevel H) :
    ιPartial F K₀ ≫ iteratedTranslate F h' = translate (partialTower K₀ F) h' ≫ ιPartial F K₀ :=
  ι_map (partialTranslate F h') K₀

theorem iteratedTranslate_one : iteratedTranslate F 1 = 𝟙 _ :=
  ιPartial_hom_ext F fun K₀ => by
    rw [ιPartial_iteratedTranslate, translate_one, Category.id_comp, Category.comp_id]

theorem iteratedTranslate_mul (g h : H') :
    iteratedTranslate F (g * h) = iteratedTranslate F h ≫ iteratedTranslate F g :=
  ιPartial_hom_ext F fun K₀ => by
    rw [ιPartial_iteratedTranslate, translate_mul, ιPartial_iteratedTranslate_assoc,
      ιPartial_iteratedTranslate, Category.assoc]

/-- The iterated colimit with the action of `H'` through the partial colimits. -/
def iteratedAction : Action C H' where
  V := colimit (diagram (partialColimit F))
  ρ :=
    { toFun := iteratedTranslate F
      map_one' := iteratedTranslate_one F
      map_mul' := fun g h => iteratedTranslate_mul F g h }

@[simp] theorem iteratedAction_ρ (h' : H') : (iteratedAction F).ρ h' = iteratedTranslate F h' :=
  rfl

variable [IsTopologicalGroup H]

@[reassoc]
theorem ιPartial_translate (h : H) (K₀ : CompactOpenLevel H) :
    ιPartial F K₀ ≫ translate (partialColimit F) h =
      map (partialTowerMap F (conjArrow h K₀)) ≫ ιPartial F (conjLevel h K₀) :=
  ι_translate (partialColimit F) h K₀

/-- The translations by `h` and `h'` on the iterated colimit commute. -/
theorem translate_comm_iteratedTranslate (h : H) (h' : H') :
    translate (partialColimit F) h ≫ iteratedTranslate F h' =
      iteratedTranslate F h' ≫ translate (partialColimit F) h :=
  translate_map (partialTranslate F h') h

variable [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C]

/-- The cocone on the levels of `H` whose leg at `K₀` is the comparison from the partial colimit
at `K₀` to the colimit over all levels of `H × H'`. -/
def iteratedCocone : Cocone (diagram (partialColimit F)) where
  pt := colimit (diagram F)
  ι :=
    { app := fun K₀ => reindexComparison (withLeft K₀.unop) F
      naturality := fun _ _ a => by
        have e := partialColimitFunctor_map_comparison F (inclusion (leOfHom a.unop))
        rw [show ((inclusion (leOfHom a.unop)).element, (1 : H')) = 1 from rfl,
          translate_one] at e
        exact e }

/-- The comparison from the iterated colimit `colim_{K₀} colim_{K'} F (K₀ × K')` to the colimit
over all levels of `H × H'`. -/
def iteratedComparison : colimit (diagram (partialColimit F)) ⟶ colimit (diagram F) :=
  colimit.desc _ (iteratedCocone F)

@[reassoc (attr := simp)]
theorem ιPartial_iteratedComparison (K₀ : CompactOpenLevel H) :
    ιPartial F K₀ ≫ iteratedComparison F = reindexComparison (withLeft K₀) F :=
  colimit.ι_desc (iteratedCocone F) (op K₀)

@[reassoc (attr := simp)]
theorem ι₂_iteratedComparison (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    ι₂ F K₀ K' ≫ iteratedComparison F = ι F (prod K₀ K') := by
  rw [ι₂_def, Category.assoc, ιPartial_iteratedComparison]
  exact ι_reindexComparison (withLeft K₀) F K'

omit [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C] in
theorem factorCocone_naturality {K L : CompactOpenLevel (H × H')}
    (hle : L.subgroup ≤ K.subgroup) :
    F.map (inclusion hle).op ≫ F.map (inclusion (prod_leftFactor_rightFactor_le L)).op ≫
        ι₂ F (leftFactor L) (rightFactor L) =
      F.map (inclusion (prod_leftFactor_rightFactor_le K)).op ≫
        ι₂ F (leftFactor K) (rightFactor K) := by
  rw [← map_inclusion_ι₂ F (leftFactor_mono hle) (rightFactor_mono hle), ← Category.assoc,
    ← F.map_comp, ← op_comp, inclusion_comp_inclusion, ← Category.assoc, ← F.map_comp,
    ← op_comp, inclusion_comp_inclusion]

/-- The cocone on the levels of `H × H'` whose leg at `K` restricts from `K` to the product
`leftFactor K × rightFactor K` of its factors. -/
def factorCocone : Cocone (diagram F) where
  pt := colimit (diagram (partialColimit F))
  ι :=
    { app := fun K => F.map (inclusion (prod_leftFactor_rightFactor_le K.unop)).op ≫
          ι₂ F (leftFactor K.unop) (rightFactor K.unop)
      naturality := fun _ _ a =>
        (factorCocone_naturality F (leOfHom a.unop)).trans (Category.comp_id _).symm }

/-- The inverse comparison, from the colimit over all levels of `H × H'` to the iterated
colimit. -/
def iteratedComparisonInv : colimit (diagram F) ⟶ colimit (diagram (partialColimit F)) :=
  colimit.desc _ (factorCocone F)

@[reassoc (attr := simp)]
theorem ι_iteratedComparisonInv (K : CompactOpenLevel (H × H')) :
    ι F K ≫ iteratedComparisonInv F =
      F.map (inclusion (prod_leftFactor_rightFactor_le K)).op ≫
        ι₂ F (leftFactor K) (rightFactor K) :=
  colimit.ι_desc (factorCocone F) (op K)

/-- Since product levels are cofinal, the colimit over all levels of `H × H'` is the colimit over
`K₀` of the colimits of the partial towers `K' ↦ F (K₀ × K')`. -/
@[simps]
def iteratedColimitIso : colimit (diagram (partialColimit F)) ≅ colimit (diagram F) where
  hom := iteratedComparison F
  inv := iteratedComparisonInv F
  hom_inv_id := ιPartial_hom_ext F fun K₀ => ιTower_hom_ext F K₀ fun K' => by
    rw [Category.comp_id, ← Category.assoc, ← ι₂_def, ι₂_iteratedComparison_assoc,
      ι_iteratedComparisonInv]
    exact map_inclusion_ι₂_of_le F (le_leftFactor_prod K₀ K') (le_rightFactor_prod K₀ K') _
  inv_hom_id := hom_ext F fun K => by
    rw [ι_iteratedComparisonInv_assoc, ι₂_iteratedComparison, map_inclusion_ι, Category.comp_id]

/-- The comparison intertwines translation by `h ∈ H` on the iterated colimit with translation
by `(h, 1)`. -/
@[reassoc]
theorem translate_iteratedComparison (h : H) :
    translate (partialColimit F) h ≫ iteratedComparison F =
      iteratedComparison F ≫ translate F (h, 1) :=
  ιPartial_hom_ext F fun K₀ => by
    rw [ιPartial_translate_assoc, ιPartial_iteratedComparison, ιPartial_iteratedComparison_assoc]
    exact partialColimitFunctor_map_comparison F (conjArrow h K₀)

/-- The comparison intertwines translation by `h' ∈ H'` on the iterated colimit with translation
by `(1, h')`. -/
@[reassoc]
theorem iteratedTranslate_iteratedComparison (h' : H') :
    iteratedTranslate F h' ≫ iteratedComparison F =
      iteratedComparison F ≫ translate F (1, h') :=
  ιPartial_hom_ext F fun K₀ => by
    rw [ιPartial_iteratedTranslate_assoc, ιPartial_iteratedComparison,
      ιPartial_iteratedComparison_assoc]
    exact translate_reindexComparison (withLeft K₀) F h'

/-- Under the comparison isomorphism, translation by `x ∈ H × H'` on the full colimit is
translation by `x.2` followed by translation by `x.1` on the iterated colimit. -/
theorem iteratedColimitIso_conj_translate (x : H × H') :
    (iteratedColimitIso F).hom ≫ translate F x ≫ (iteratedColimitIso F).inv =
      iteratedTranslate F x.2 ≫ translate (partialColimit F) x.1 := by
  have e : x = (x.1, 1) * (1, x.2) := by
    ext <;> simp
  rw [← Category.assoc, Iso.comp_inv_eq, iteratedColimitIso_hom, Category.assoc,
    translate_iteratedComparison, ← Category.assoc, iteratedTranslate_iteratedComparison,
    Category.assoc, ← translate_mul, ← e]

/-- The comparison isomorphism as an isomorphism of objects with an action of `H`, where `H`
acts on the full colimit through `H → H × H'`. -/
def iteratedColimitIsoLeft :
    action (partialColimit F) ≅ (Action.res C (MonoidHom.inl H H')).obj (action F) :=
  Action.mkIso (iteratedColimitIso F) fun h => translate_iteratedComparison F h

/-- The comparison isomorphism as an isomorphism of objects with an action of `H'`, where `H'`
acts on the full colimit through `H' → H × H'`. -/
def iteratedColimitIsoRight :
    iteratedAction F ≅ (Action.res C (MonoidHom.inr H H')).obj (action F) :=
  Action.mkIso (iteratedColimitIso F) fun h' => iteratedTranslate_iteratedComparison F h'

end Iterated

end LevelColimit

end Langlands.Shimura
