import Langlands.Shimura.RestrictedLevelColimit
import Langlands.Shimura.CofinalLevelReindex

/-! # Colimits over levels satisfying a property, reindexed along level functors

A level functor `Φ` over `φ : H →* G` sending the levels satisfying `P'` to levels satisfying `P`
restricts presheaves on the levels satisfying `P` to presheaves on the levels satisfying `P'`.
The colimit of the restriction maps to the colimit of the original presheaf, equivariantly for
`H` acting through `φ`, and this map is an isomorphism when the image levels are cofinal.
See `RestrictedLevelReindex.md`.
-/

noncomputable section

universe u v v' w t

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

/-- Inclusion arrows between levels satisfying a property compose to the inclusion arrow. -/
theorem restrictedHom_comp {G : Type v} [Group G] [TopologicalSpace G]
    {P : ObjectProperty (CompactOpenLevel G)} {K L M : P.FullSubcategory}
    (h₁ : K.obj.subgroup ≤ L.obj.subgroup) (h₂ : L.obj.subgroup ≤ M.obj.subgroup) :
    restrictedHom P h₁ ≫ restrictedHom P h₂ = restrictedHom P (h₁.trans h₂) :=
  P.hom_ext (Arrow.ext (mul_one (1 : G)))

namespace FunctorOver

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {φ : H →* G} (Φ : FunctorOver φ) {P : ObjectProperty (CompactOpenLevel G)}
  {P' : ObjectProperty (CompactOpenLevel H)}

/-- The functor from levels satisfying `P'` to levels satisfying `P` induced by a level functor
`Φ` that sends levels satisfying `P'` to levels satisfying `P`. -/
def restrictedFunctor (hΦ : ∀ K, P' K → P (Φ.functor.obj K)) :
    P'.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P'.ι ⋙ Φ.functor) fun K => hΦ K.obj K.property

variable (hΦ : ∀ K, P' K → P (Φ.functor.obj K))

@[simp] theorem restrictedFunctor_obj_obj (K : P'.FullSubcategory) :
    ((Φ.restrictedFunctor hΦ).obj K).obj = Φ.functor.obj K.obj := rfl

@[simp] theorem restrictedFunctor_map_hom {K L : P'.FullSubcategory} (a : K ⟶ L) :
    ((Φ.restrictedFunctor hΦ).map a).hom = Φ.functor.map a.hom := rfl

/-- Followed by the inclusion of levels satisfying `P`, the restricted functor is `Φ` on the
levels satisfying `P'`. -/
theorem restrictedFunctor_comp_ι : Φ.restrictedFunctor hΦ ⋙ P.ι = P'.ι ⋙ Φ.functor := rfl

theorem restrictedFunctor_map_restrictedHom {K L : P'.FullSubcategory}
    (h : K.obj.subgroup ≤ L.obj.subgroup) :
    (Φ.restrictedFunctor hΦ).map (restrictedHom P' h) =
      restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K)
        (L := (Φ.restrictedFunctor hΦ).obj L) (Φ.le_of_le h) :=
  P.hom_ext (Φ.map_inclusion h)

theorem restrictedFunctor_map_restrictedSelfArrow (K : P'.FullSubcategory) (k : H)
    (hk : k ∈ K.obj.subgroup) :
    (Φ.restrictedFunctor hΦ).map (restrictedSelfArrow P' K k hk) =
      restrictedSelfArrow P ((Φ.restrictedFunctor hΦ).obj K) (φ k) (Φ.map_mem K.obj hk) :=
  P.hom_ext (Φ.map_selfArrow K.obj k hk)

section Preimage

/-- The image of a conjugate level `h K h⁻¹` lies in the conjugate `φ(h) Φ(K) φ(h)⁻¹` of the image
level. -/
theorem conjLevel_le [IsTopologicalGroup H] [IsTopologicalGroup G] (h : H)
    (K : CompactOpenLevel H) :
    (Φ.functor.obj (conjLevel h K)).subgroup ≤ (conjLevel (φ h) (Φ.functor.obj K)).subgroup := by
  have e := le_conjLevel (Φ.functor.map (conjArrow h K))
  rwa [Φ.map_element, conjArrow_element] at e

/-- The preimage of a downward closed property is downward closed. -/
instance isDownwardClosed_inverseImage [IsDownwardClosed P] :
    IsDownwardClosed (P.inverseImage Φ.functor) :=
  ⟨fun h hL => IsDownwardClosed.of_le (P := P) (Φ.le_of_le h) hL⟩

/-- The preimage of a downward closed, conjugation stable property is conjugation stable. -/
instance isConjStable_inverseImage [IsTopologicalGroup H] [IsTopologicalGroup G]
    [IsDownwardClosed P] [IsConjStable P] : IsConjStable (P.inverseImage Φ.functor) :=
  ⟨fun h {K} hK => IsDownwardClosed.of_le (P := P) (Φ.conjLevel_le h K)
    (IsConjStable.conjLevel (P := P) (φ h) hK)⟩

/-- The levels whose image satisfies `P` are mapped to levels satisfying `P`. -/
theorem mapsTo_inverseImage : ∀ K, P.inverseImage Φ.functor K → P (Φ.functor.obj K) :=
  fun _ hK => hK

end Preimage

/-- Every level satisfying `P` contains the image of a level satisfying `P'`. -/
def IsRestrictedCofinal (P' : ObjectProperty (CompactOpenLevel H))
    (P : ObjectProperty (CompactOpenLevel G)) : Prop :=
  ∀ L : P.FullSubcategory, ∃ K : P'.FullSubcategory, (Φ.functor.obj K.obj).subgroup ≤ L.obj.subgroup

variable {Φ} in
/-- If `Φ` has cofinal image and `P` is downward closed, the levels whose image satisfies `P` have
cofinal image among the levels satisfying `P`. -/
theorem IsCofinal.isRestrictedCofinal_inverseImage [IsDownwardClosed P] (hcof : Φ.IsCofinal) :
    Φ.IsRestrictedCofinal (P.inverseImage Φ.functor) P := fun L =>
  let ⟨K, hK⟩ := hcof L.obj
  ⟨⟨K, IsDownwardClosed.of_le (P := P) hK L.property⟩, hK⟩

end FunctorOver

end CompactOpenLevel

namespace RestrictedLevelColimit

open CompactOpenLevel CompactOpenLevel.FunctorOver

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {C : Type u} [Category.{w} C] {φ : H →* G} (Φ : FunctorOver φ)
  {P : ObjectProperty (CompactOpenLevel G)} {P' : ObjectProperty (CompactOpenLevel H)}
  (hΦ : ∀ K, P' K → P (Φ.functor.obj K))

/-- The presheaf on the levels satisfying `P'` obtained from a presheaf on the levels satisfying
`P` by restriction along `Φ`. -/
abbrev reindex (F : P.FullSubcategoryᵒᵖ ⥤ C) : P'.FullSubcategoryᵒᵖ ⥤ C :=
  (Φ.restrictedFunctor hΦ).op ⋙ F

variable (C) in
/-- Restriction along `Φ`, as a functor of presheaves on levels satisfying a property. -/
abbrev reindexFunctor : (P.FullSubcategoryᵒᵖ ⥤ C) ⥤ (P'.FullSubcategoryᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (Φ.restrictedFunctor hΦ).op

theorem isLevelTrivial_reindex {F : P.FullSubcategoryᵒᵖ ⥤ C} (hF : IsLevelTrivial F) :
    IsLevelTrivial (reindex Φ hΦ F) := by
  intro K k hk
  change F.map ((Φ.restrictedFunctor hΦ).map (restrictedSelfArrow P' K k hk)).op = 𝟙 _
  rw [restrictedFunctor_map_restrictedSelfArrow]
  exact hF _ _ _

/-- The restriction of a presheaf on all levels of `G` to the levels satisfying `P`, reindexed
along `Φ`, is the restriction of the reindexed presheaf to the levels satisfying `P'`. -/
theorem reindex_restrict (F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    reindex Φ hΦ (P.ι.op ⋙ F₀) = P'.ι.op ⋙ LevelColimit.reindex Φ F₀ := rfl

variable [HasColimitsOfShape (RestrictedOrdered P')ᵒᵖ C] [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ C]
  (F : P.FullSubcategoryᵒᵖ ⥤ C)

omit [HasColimitsOfShape (RestrictedOrdered P')ᵒᵖ C] in
theorem map_reindex_restrictedHom_ι {K L : P'.FullSubcategory}
    (h : K.obj.subgroup ≤ L.obj.subgroup) :
    F.map ((Φ.restrictedFunctor hΦ).map (restrictedHom P' h)).op ≫
        ι F ((Φ.restrictedFunctor hΦ).obj K) =
      ι F ((Φ.restrictedFunctor hΦ).obj L) := by
  rw [restrictedFunctor_map_restrictedHom]
  exact map_restrictedHom_ι F _

/-- The cocone on the reindexed diagram whose level-`K` leg is the inclusion of level `Φ K` into
the colimit of `F`. -/
def reindexCocone : Cocone (diagram (reindex Φ hΦ F)) where
  pt := colimit (diagram F)
  ι :=
    { app := fun K => ι F ((Φ.restrictedFunctor hΦ).obj ⟨K.unop.val, K.unop.property⟩)
      naturality := fun _ _ h =>
        (map_reindex_restrictedHom_ι Φ hΦ F (leOfHom h.unop)).trans (Category.comp_id _).symm }

/-- The comparison map from the colimit of the reindexed presheaf to the colimit of `F`. -/
def reindexComparison : colimit (diagram (reindex Φ hΦ F)) ⟶ colimit (diagram F) :=
  colimit.desc _ (reindexCocone Φ hΦ F)

@[reassoc (attr := simp)]
theorem ι_reindexComparison (K : P'.FullSubcategory) :
    ι (reindex Φ hΦ F) K ≫ reindexComparison Φ hΦ F = ι F ((Φ.restrictedFunctor hΦ).obj K) :=
  colimit.ι_desc (reindexCocone Φ hΦ F) (op ⟨K.obj, K.property⟩)

variable {F} in
/-- The comparison map is natural in the presheaf. -/
@[reassoc]
theorem map_reindexComparison {F' : P.FullSubcategoryᵒᵖ ⥤ C} (α : F ⟶ F') :
    map (Functor.whiskerLeft (Φ.restrictedFunctor hΦ).op α) ≫ reindexComparison Φ hΦ F' =
      reindexComparison Φ hΦ F ≫ map α :=
  hom_ext _ fun K => by
    rw [ι_map_assoc, ι_reindexComparison, ι_reindexComparison_assoc, ι_map]
    rfl

section Translate

variable [IsTopologicalGroup H] [IsTopologicalGroup G] [IsConjStable P] [IsConjStable P']

/-- The comparison map intertwines translation by `h` with translation by `φ h`. -/
@[reassoc]
theorem translate_reindexComparison (h : H) :
    translate (reindex Φ hΦ F) h ≫ reindexComparison Φ hΦ F =
      reindexComparison Φ hΦ F ≫ translate F (φ h) :=
  hom_ext (reindex Φ hΦ F) fun K => by
    have e := map_ι F ((Φ.restrictedFunctor hΦ).map (restrictedConjArrow P' h K))
    rw [restrictedFunctor_map_hom, Φ.map_element, restrictedConjArrow_hom,
      conjArrow_element] at e
    rw [ι_translate_assoc, ι_reindexComparison, ι_reindexComparison_assoc]
    exact e

/-- The comparison map as a morphism of objects with an action of `H`, where `H` acts on the
colimit of `F` through `φ`. -/
def reindexComparisonHom : action (reindex Φ hΦ F) ⟶ (Action.res C φ).obj (action F) where
  hom := reindexComparison Φ hΦ F
  comm h := translate_reindexComparison Φ hΦ F h

@[simp] theorem reindexComparisonHom_hom :
    (reindexComparisonHom Φ hΦ F).hom = reindexComparison Φ hΦ F := rfl

variable (C) in
/-- The comparison maps, natural in the presheaf on the levels satisfying `P`. -/
def reindexComparisonNatTrans :
    reindexFunctor C Φ hΦ ⋙ functor P' C ⟶ functor P C ⋙ Action.res C φ where
  app F := reindexComparisonHom Φ hΦ F
  naturality _ _ α := Action.Hom.ext (map_reindexComparison Φ hΦ α)

@[simp] theorem reindexComparisonNatTrans_app :
    (reindexComparisonNatTrans C Φ hΦ).app F = reindexComparisonHom Φ hΦ F := rfl

end Translate

section Smooth

variable {R : Type t} [CommRing R] [HasColimitsOfShape (RestrictedOrdered P')ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]

theorem reindexComparison_ι_apply (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R)
    (K : P'.FullSubcategory) (x : F.obj (op ((Φ.restrictedFunctor hΦ).obj K))) :
    (reindexComparison Φ hΦ F).hom ((ι (reindex Φ hΦ F) K).hom x) =
      (ι F ((Φ.restrictedFunctor hΦ).obj K)).hom x :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_reindexComparison Φ hΦ F K)

/-- An element `g` lying in every level `Φ K` with `K` satisfying `P'` fixes the image of the
comparison map. -/
theorem translate_reindexComparison_apply_of_mem [IsTopologicalGroup G] [IsConjStable P]
    [IsTopologicalGroup H] [IsDownwardClosed P'] [Nonempty P'.FullSubcategory]
    (F : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F) {g : G}
    (hg : ∀ K : P'.FullSubcategory, g ∈ (Φ.functor.obj K.obj).subgroup)
    (x : (colimit (diagram (reindex Φ hΦ F)) : ModuleCat.{w} R)) :
    (translate F g).hom ((reindexComparison Φ hΦ F).hom x) = (reindexComparison Φ hΦ F).hom x := by
  obtain ⟨K, y, rfl⟩ := exists_ι_apply (reindex Φ hΦ F) x
  rw [reindexComparison_ι_apply]
  exact translate_ι_apply_of_mem F hF (hg K) y

end Smooth

/-! ## Cofinal image levels -/

section Cofinal

variable [IsTopologicalGroup H] [IsDownwardClosed P']

omit [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ C] in
/-- Restricting from a level `L` satisfying `P` to an image level `Φ K ⊆ L` and including level
`K` into the colimit of the reindexed presheaf does not depend on `K`. -/
theorem map_restrictedHom_ι_reindex_eq {L : P.FullSubcategory} {K K' : P'.FullSubcategory}
    (hK : (Φ.functor.obj K.obj).subgroup ≤ L.obj.subgroup)
    (hK' : (Φ.functor.obj K'.obj).subgroup ≤ L.obj.subgroup) :
    F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K) (L := L) hK).op ≫
        ι (reindex Φ hΦ F) K =
      F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K') (L := L) hK').op ≫
        ι (reindex Φ hΦ F) K' := by
  let M : P'.FullSubcategory :=
    ⟨inf K.obj K'.obj, IsDownwardClosed.of_le (P := P') (fun _ hx => hx.1) K.property⟩
  have key : ∀ {K₁ : P'.FullSubcategory} (h₁ : (Φ.functor.obj K₁.obj).subgroup ≤ L.obj.subgroup)
      (h : M.obj.subgroup ≤ K₁.obj.subgroup),
      F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K₁) (L := L) h₁).op ≫
          ι (reindex Φ hΦ F) K₁ =
        F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj M) (L := L)
          ((Φ.le_of_le h).trans h₁)).op ≫ ι (reindex Φ hΦ F) M := by
    intro K₁ h₁ h
    have e : F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K₁) (L := L) h₁).op ≫
        F.map ((Φ.restrictedFunctor hΦ).map (restrictedHom P' h)).op =
          F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj M) (L := L)
            ((Φ.le_of_le h).trans h₁)).op := by
      rw [← F.map_comp, ← op_comp]
      exact congrArg (fun a => F.map a.op)
        ((congrArg (· ≫ restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj K₁) (L := L) h₁)
          (restrictedFunctor_map_restrictedHom Φ hΦ h)).trans (restrictedHom_comp _ _))
    rw [← map_restrictedHom_ι (reindex Φ hΦ F) (K := M) (L := K₁) h, ← Category.assoc]
    exact congrArg (· ≫ ι (reindex Φ hΦ F) M) e
  rw [key hK (fun _ hx => hx.1), key hK' (fun _ hx => hx.2)]

variable {Φ} (hc : Φ.IsRestrictedCofinal P' P)

/-- A chosen level satisfying `P'` whose image lies in the level `L` satisfying `P`. -/
def cofinalLevel (L : P.FullSubcategory) : P'.FullSubcategory :=
  (hc L).choose

omit [IsTopologicalGroup H] [IsDownwardClosed P'] in
theorem cofinalLevel_le (L : P.FullSubcategory) :
    (Φ.functor.obj (cofinalLevel hc L).obj).subgroup ≤ L.obj.subgroup :=
  (hc L).choose_spec

omit [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ C] in
theorem cofinalCocone_naturality {L L' : P.FullSubcategory}
    (hle : L'.obj.subgroup ≤ L.obj.subgroup) :
    F.map (restrictedHom P hle).op ≫
        F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc L')) (L := L')
          (cofinalLevel_le hc L')).op ≫ ι (reindex Φ hΦ F) (cofinalLevel hc L') =
      F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc L)) (L := L)
          (cofinalLevel_le hc L)).op ≫ ι (reindex Φ hΦ F) (cofinalLevel hc L) := by
  rw [← Category.assoc, ← F.map_comp, ← op_comp]
  have e := restrictedHom_comp (P := P) (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc L'))
    (cofinalLevel_le hc L') hle
  exact (congrArg (fun a => F.map (Quiver.Hom.op a) ≫ ι (reindex Φ hΦ F) (cofinalLevel hc L'))
    e).trans (map_restrictedHom_ι_reindex_eq Φ hΦ F _ _)

/-- The cocone on the levels satisfying `P` whose leg at `L` restricts to the chosen image level
inside `L` and includes it into the colimit of the reindexed presheaf. -/
def cofinalCocone : Cocone (diagram F) where
  pt := colimit (diagram (reindex Φ hΦ F))
  ι :=
    { app := fun L => F.map (restrictedHom P
          (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc ⟨L.unop.val, L.unop.property⟩))
          (L := ⟨L.unop.val, L.unop.property⟩) (cofinalLevel_le hc _)).op ≫
          ι (reindex Φ hΦ F) (cofinalLevel hc ⟨L.unop.val, L.unop.property⟩)
      naturality := fun _ _ a =>
        (cofinalCocone_naturality hΦ F hc (leOfHom a.unop)).trans (Category.comp_id _).symm }

/-- The inverse comparison, from the colimit of `F` to the colimit of the reindexed presheaf. -/
def reindexComparisonInv : colimit (diagram F) ⟶ colimit (diagram (reindex Φ hΦ F)) :=
  colimit.desc _ (cofinalCocone hΦ F hc)

@[reassoc (attr := simp)]
theorem ι_reindexComparisonInv (L : P.FullSubcategory) :
    ι F L ≫ reindexComparisonInv hΦ F hc =
      F.map (restrictedHom P (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc L)) (L := L)
          (cofinalLevel_le hc L)).op ≫ ι (reindex Φ hΦ F) (cofinalLevel hc L) :=
  colimit.ι_desc (cofinalCocone hΦ F hc) (op ⟨L.obj, L.property⟩)

/-- If every level satisfying `P` contains the image of a level satisfying `P'`, the comparison
of colimits is an isomorphism. -/
@[simps]
def reindexColimitIso : colimit (diagram (reindex Φ hΦ F)) ≅ colimit (diagram F) where
  hom := reindexComparison Φ hΦ F
  inv := reindexComparisonInv hΦ F hc
  hom_inv_id := hom_ext _ fun K => by
    rw [ι_reindexComparison_assoc, ι_reindexComparisonInv, Category.comp_id,
      map_restrictedHom_ι_reindex_eq Φ hΦ F (K' := K) _ (Φ.le_of_le (le_refl K.obj.subgroup)),
      ← restrictedFunctor_map_restrictedHom Φ hΦ (le_refl K.obj.subgroup)]
    exact map_restrictedHom_ι (reindex Φ hΦ F) (K := K) (L := K) (le_refl K.obj.subgroup)
  inv_hom_id := hom_ext _ fun L => by
    rw [ι_reindexComparisonInv_assoc, ι_reindexComparison, Category.comp_id]
    exact map_restrictedHom_ι F (K := (Φ.restrictedFunctor hΦ).obj (cofinalLevel hc L)) (L := L) _

include hc in
theorem isIso_reindexComparison : IsIso (reindexComparison Φ hΦ F) :=
  (reindexColimitIso hΦ F hc).isIso_hom

variable [IsTopologicalGroup G] [IsConjStable P] [IsConjStable P']

/-- If every level satisfying `P` contains the image of a level satisfying `P'`, the comparison
is an isomorphism of objects with an action of `H`, where `H` acts on the colimit of `F` through
`φ`. -/
def reindexActionIso : action (reindex Φ hΦ F) ≅ (Action.res C φ).obj (action F) :=
  Action.mkIso (reindexColimitIso hΦ F hc) fun h => translate_reindexComparison Φ hΦ F h

@[simp] theorem reindexActionIso_hom :
    (reindexActionIso hΦ F hc).hom = reindexComparisonHom Φ hΦ F :=
  rfl

variable (C) in
/-- Under the same hypothesis, the comparison maps form a natural isomorphism of functors from
presheaves on the levels satisfying `P` to objects with an action of `H`. -/
def reindexNatIso : reindexFunctor C Φ hΦ ⋙ functor P' C ≅ functor P C ⋙ Action.res C φ :=
  NatIso.ofComponents (fun F => reindexActionIso hΦ F hc) fun α =>
    Action.Hom.ext (map_reindexComparison Φ hΦ α)

@[simp] theorem reindexNatIso_hom :
    (reindexNatIso C hΦ hc).hom = reindexComparisonNatTrans C Φ hΦ :=
  rfl

end Cofinal

/-! ## Comparison with colimits over all levels -/

section Restrict

variable [IsTopologicalGroup H] [IsTopologicalGroup G] [IsDownwardClosed P]
  [Nonempty P.FullSubcategory] [IsDownwardClosed P'] [Nonempty P'.FullSubcategory]
  [HasColimitsOfShape (Ordered H)ᵒᵖ C] [HasColimitsOfShape (Ordered G)ᵒᵖ C]
  (F₀ : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- Under the identifications of colimits over levels satisfying a property with colimits over
all levels, the restricted comparison along `Φ` is the comparison along `Φ` over all levels. -/
@[reassoc]
theorem reindexComparison_colimitRestrictIso_hom :
    reindexComparison Φ hΦ (P.ι.op ⋙ F₀) ≫ (colimitRestrictIso (P := P) F₀).hom =
      (colimitRestrictIso (P := P') (LevelColimit.reindex Φ F₀)).hom ≫
        LevelColimit.reindexComparison Φ F₀ :=
  hom_ext _ fun K => by
    rw [ι_reindexComparison_assoc, ι_colimitRestrictIso_hom]
    exact ((ι_colimitRestrictIso_hom_assoc (P := P') (LevelColimit.reindex Φ F₀) K _).trans
      (LevelColimit.ι_reindexComparison Φ F₀ K.obj)).symm

variable [IsConjStable P] [IsConjStable P']

/-- The same compatibility for the comparison morphisms of objects with an action of `H`. -/
theorem reindexComparisonHom_actionRestrictIso_hom :
    reindexComparisonHom Φ hΦ (P.ι.op ⋙ F₀) ≫
        (Action.res C φ).map (actionRestrictIso (P := P) F₀).hom =
      (actionRestrictIso (P := P') (LevelColimit.reindex Φ F₀)).hom ≫
        LevelColimit.reindexComparisonHom Φ F₀ :=
  Action.Hom.ext (reindexComparison_colimitRestrictIso_hom Φ hΦ F₀)

end Restrict

end RestrictedLevelColimit

end Langlands.Shimura
