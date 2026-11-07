import Langlands.Shimura.CofinalLevelReindex
import Langlands.Shimura.ProductLevelColimit

/-! # Level towers through a splitting of the group as a product -/

noncomputable section

universe u v v₁ v₂ w t

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

section Split

variable {G : Type v} {H : Type v₁} {H' : Type v₂} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H')

/-- The first factor `H`, as a subgroup of `G` through the splitting `e`. -/
def factorHom : H →* G :=
  (e.symm : H × H' →* G).comp (MonoidHom.inl H H')

/-- The second factor `H'`, as a subgroup of `G` through the splitting `e`. -/
def awayHom : H' →* G :=
  (e.symm : H × H' →* G).comp (MonoidHom.inr H H')

@[simp] theorem factorHom_apply (h : H) : factorHom e h = e.symm (h, 1) :=
  rfl

@[simp] theorem awayHom_apply (h' : H') : awayHom e h' = e.symm (1, h') :=
  rfl

/-- Every element of `G` is the product of its two factors. -/
theorem factorHom_mul_awayHom (g : G) : factorHom e (e g).1 * awayHom e (e g).2 = g := by
  rw [factorHom_apply, awayHom_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
    Prod.mk.eta, e.symm_apply_apply]

/-- The two factors commute in `G`. -/
theorem factorHom_commute_awayHom (h : H) (h' : H') :
    Commute (factorHom e h) (awayHom e h') := by
  rw [factorHom_apply, awayHom_apply, Commute, SemiconjBy, ← map_mul, ← map_mul,
    Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul, mul_one, one_mul]

/-- The levels `e⁻¹ (K₀ × K')` of `G` with the first factor `K₀` fixed, over `awayHom e`. -/
def awayOver (K₀ : CompactOpenLevel H) : FunctorOver (awayHom e) :=
  (withLeft K₀).comp (transportOver e.symm)

/-- The levels `e⁻¹ (K × K₀')` of `G` with the second factor `K₀'` fixed, over `factorHom e`. -/
def factorOver (K₀' : CompactOpenLevel H') : FunctorOver (factorHom e) :=
  (withRight K₀').comp (transportOver e.symm)

@[simp] theorem awayOver_functor_obj (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    (awayOver e K₀).functor.obj K' = transport e.symm (prod K₀ K') :=
  rfl

@[simp] theorem factorOver_functor_obj (K₀' : CompactOpenLevel H') (K : CompactOpenLevel H) :
    (factorOver e K₀').functor.obj K = transport e.symm (prod K K₀') :=
  rfl

theorem mem_transport_symm_prod {K : CompactOpenLevel H} {K' : CompactOpenLevel H'} {g : G} :
    g ∈ (transport e.symm (prod K K')).subgroup ↔ (e g).1 ∈ K.subgroup ∧ (e g).2 ∈ K'.subgroup :=
  Iff.rfl

theorem factorHom_mem_transport_symm_prod {K : CompactOpenLevel H} (K' : CompactOpenLevel H')
    {k : H} (hk : k ∈ K.subgroup) : factorHom e k ∈ (transport e.symm (prod K K')).subgroup := by
  rw [mem_transport_symm_prod, factorHom_apply, e.apply_symm_apply]
  exact ⟨hk, K'.subgroup.one_mem⟩

theorem awayHom_mem_transport_symm_prod (K : CompactOpenLevel H) {K' : CompactOpenLevel H'}
    {k' : H'} (hk : k' ∈ K'.subgroup) :
    awayHom e k' ∈ (transport e.symm (prod K K')).subgroup := by
  rw [mem_transport_symm_prod, awayHom_apply, e.apply_symm_apply]
  exact ⟨K.subgroup.one_mem, hk⟩

end Split

end CompactOpenLevel

namespace LevelColimit

open CompactOpenLevel

section Split

variable {G : Type v} {H : Type v₁} {H' : Type v₂} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H')
  {C : Type u} [Category.{w} C]

/-- The presheaf `K ↦ F (e⁻¹ K)` on the levels of `H × H'`. -/
abbrev splitTower (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) : (CompactOpenLevel (H × H'))ᵒᵖ ⥤ C :=
  reindex (transportOver e.symm) F

/-- The tower `K' ↦ F (e⁻¹ (K₀ × K'))` away from the first factor, with `K₀` fixed. -/
abbrev awayTower (K₀ : CompactOpenLevel H) (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    (CompactOpenLevel H')ᵒᵖ ⥤ C :=
  reindex (awayOver e K₀) F

/-- The tower `K ↦ F (e⁻¹ (K × K₀'))` with the second factor `K₀'` fixed. -/
abbrev factorTower (K₀' : CompactOpenLevel H') (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    (CompactOpenLevel H)ᵒᵖ ⥤ C :=
  reindex (factorOver e K₀') F

/-- The away tower is the partial tower of the split presheaf. -/
theorem awayTower_eq (K₀ : CompactOpenLevel H) (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    awayTower e K₀ F = partialTower K₀ (splitTower e F) :=
  rfl

theorem isLevelTrivial_splitTower {F : (CompactOpenLevel G)ᵒᵖ ⥤ C} (hF : IsLevelTrivial F) :
    IsLevelTrivial (splitTower e F) :=
  isLevelTrivial_reindex _ hF

theorem isLevelTrivial_awayTower (K₀ : CompactOpenLevel H) {F : (CompactOpenLevel G)ᵒᵖ ⥤ C}
    (hF : IsLevelTrivial F) : IsLevelTrivial (awayTower e K₀ F) :=
  isLevelTrivial_reindex _ hF

theorem isLevelTrivial_factorTower (K₀' : CompactOpenLevel H') {F : (CompactOpenLevel G)ᵒᵖ ⥤ C}
    (hF : IsLevelTrivial F) : IsLevelTrivial (factorTower e K₀' F) :=
  isLevelTrivial_reindex _ hF

variable (C) in
/-- The away towers, as a functor of presheaves on levels. -/
abbrev awayTowerFunctor (K₀ : CompactOpenLevel H) :
    ((CompactOpenLevel G)ᵒᵖ ⥤ C) ⥤ ((CompactOpenLevel H')ᵒᵖ ⥤ C) :=
  reindexFunctor C (awayOver e K₀)

section Comparison

variable [HasColimitsOfShape (Ordered G)ᵒᵖ C] [HasColimitsOfShape (Ordered H')ᵒᵖ C]
  [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C] (F : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- The comparison of the away colimit at `K₀` with the colimit of `F` is the partial comparison
of the split presheaf followed by transport along `e`. -/
theorem reindexComparison_awayOver [IsTopologicalGroup G] [IsTopologicalGroup H]
    [IsTopologicalGroup H'] (K₀ : CompactOpenLevel H) :
    reindexComparison (awayOver e K₀) F =
      reindexComparison (withLeft K₀) (splitTower e F) ≫ (transportColimitIso e.symm F).hom :=
  hom_ext (awayTower e K₀ F) fun K' => by
    refine (ι_reindexComparison (awayOver e K₀) F K').trans ?_
    rw [transportColimitIso_hom]
    exact ((ι_reindexComparison_assoc (withLeft K₀) (splitTower e F) K' _).trans
      (ι_reindexComparison (transportOver e.symm) F _)).symm

end Comparison

section Translate

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H']
  [HasColimitsOfShape (Ordered G)ᵒᵖ C] [HasColimitsOfShape (Ordered H')ᵒᵖ C]
  (F : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- The comparison from the colimit of the away tower at `K₀` to the colimit of `F`, as a
morphism of objects with an action of `H'`, where `H'` acts on the colimit of `F` through
`awayHom e`. -/
abbrev awayComparison (K₀ : CompactOpenLevel H) :
    action (awayTower e K₀ F) ⟶ (Action.res C (awayHom e)).obj (action F) :=
  reindexComparisonHom (awayOver e K₀) F

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] [HasColimitsOfShape (Ordered H')ᵒᵖ C] in
/-- Translation by `factorHom e h` commutes with translation by `awayHom e h'` on the colimit
of `F`. -/
theorem translate_factorHom_comm_awayHom (h : H) (h' : H') :
    translate F (factorHom e h) ≫ translate F (awayHom e h') =
      translate F (awayHom e h') ≫ translate F (factorHom e h) := by
  rw [← translate_mul, ← translate_mul, (factorHom_commute_awayHom e h h').eq]

variable [HasColimitsOfShape (Ordered H)ᵒᵖ C] [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C]

/-- The comparison from the colimit of the factor tower at `K₀'` to the colimit of `F`, as a
morphism of objects with an action of `H`. -/
abbrev factorComparison (K₀' : CompactOpenLevel H') :
    action (factorTower e K₀' F) ⟶ (Action.res C (factorHom e)).obj (action F) :=
  reindexComparisonHom (factorOver e K₀') F

/-- The colimit of `F` is the colimit over the levels `K₀` of `H` of the colimits of the away
towers `K' ↦ F (e⁻¹ (K₀ × K'))`. -/
def splitColimitIso :
    colimit (diagram (partialColimit (splitTower e F))) ≅ colimit (diagram F) :=
  iteratedColimitIso (splitTower e F) ≪≫ transportColimitIso e.symm F

omit [IsTopologicalGroup G] in
theorem splitColimitIso_hom :
    (splitColimitIso e F).hom =
      iteratedComparison (splitTower e F) ≫ reindexComparison (transportOver e.symm) F :=
  rfl

/-- On the away colimit at `K₀`, the isomorphism is the away comparison. -/
@[reassoc (attr := simp)]
theorem ιPartial_splitColimitIso_hom (K₀ : CompactOpenLevel H) :
    ιPartial (splitTower e F) K₀ ≫ (splitColimitIso e F).hom =
      reindexComparison (awayOver e K₀) F := by
  rw [splitColimitIso, Iso.trans_hom, iteratedColimitIso_hom,
    ιPartial_iteratedComparison_assoc, reindexComparison_awayOver]

/-- On level `K₀ × K'` the isomorphism is the inclusion of level `e⁻¹ (K₀ × K')`. -/
@[reassoc (attr := simp)]
theorem ι₂_splitColimitIso_hom (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    ι₂ (splitTower e F) K₀ K' ≫ (splitColimitIso e F).hom =
      ι F (transport e.symm (prod K₀ K')) := by
  rw [ι₂_def, Category.assoc, ιPartial_splitColimitIso_hom]
  exact ι_reindexComparison (awayOver e K₀) F K'

/-- The isomorphism intertwines translation by `h ∈ H` on the iterated colimit with
translation by `factorHom e h`. -/
@[reassoc]
theorem translate_splitColimitIso_hom (h : H) :
    translate (partialColimit (splitTower e F)) h ≫ (splitColimitIso e F).hom =
      (splitColimitIso e F).hom ≫ translate F (factorHom e h) := by
  rw [splitColimitIso_hom, translate_iteratedComparison_assoc, Category.assoc,
    translate_reindexComparison]
  rfl

/-- The isomorphism intertwines translation by `h' ∈ H'` on the iterated colimit with
translation by `awayHom e h'`. -/
@[reassoc]
theorem iteratedTranslate_splitColimitIso_hom (h' : H') :
    iteratedTranslate (splitTower e F) h' ≫ (splitColimitIso e F).hom =
      (splitColimitIso e F).hom ≫ translate F (awayHom e h') := by
  rw [splitColimitIso_hom, iteratedTranslate_iteratedComparison_assoc, Category.assoc,
    translate_reindexComparison]
  rfl

/-- Under the isomorphism, translation by `g ∈ G` is translation by the second component of
`e g` followed by translation by its first component. -/
theorem splitColimitIso_conj_translate (g : G) :
    (splitColimitIso e F).hom ≫ translate F g ≫ (splitColimitIso e F).inv =
      iteratedTranslate (splitTower e F) (e g).2 ≫
        translate (partialColimit (splitTower e F)) (e g).1 := by
  have ht : translate F g =
      translate F (awayHom e (e g).2) ≫ translate F (factorHom e (e g).1) := by
    rw [← translate_mul, factorHom_mul_awayHom]
  rw [← Category.assoc, Iso.comp_inv_eq, ht, Category.assoc, translate_splitColimitIso_hom,
    ← Category.assoc, ← Category.assoc, iteratedTranslate_splitColimitIso_hom, Category.assoc]

/-- The isomorphism as an isomorphism of objects with an action of `H`, where `H` acts on the
colimit of `F` through `factorHom e`. -/
def splitColimitIsoFactor :
    action (partialColimit (splitTower e F)) ≅ (Action.res C (factorHom e)).obj (action F) :=
  Action.mkIso (splitColimitIso e F) fun h => translate_splitColimitIso_hom e F h

/-- The isomorphism as an isomorphism of objects with an action of `H'`, where `H'` acts on the
colimit of `F` through `awayHom e`. -/
def splitColimitIsoAway :
    iteratedAction (splitTower e F) ≅ (Action.res C (awayHom e)).obj (action F) :=
  Action.mkIso (splitColimitIso e F) fun h' => iteratedTranslate_splitColimitIso_hom e F h'

end Translate

section Functorial

variable [IsTopologicalGroup H'] [HasColimitsOfShape (Ordered H')ᵒᵖ C]

/-- The colimits of the away towers as a presheaf on the levels of `H` with values objects with an
action of `H'`: along `a : K₀ ⟶ K₁` the transition is `H'`-equivariant. -/
abbrev awayColimitFunctor (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) :
    (CompactOpenLevel H)ᵒᵖ ⥤ Action C H' :=
  partialColimitFunctor (splitTower e F)

theorem awayColimitFunctor_obj (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) (K₀ : CompactOpenLevel H) :
    (awayColimitFunctor e F).obj (op K₀) = action (awayTower e K₀ F) :=
  rfl

/-- The transition of away colimits along `a : K₀ ⟶ K₁`, followed by the comparison at `K₀`, is
the comparison at `K₁` followed by translation by `factorHom e a.element`. -/
@[reassoc]
theorem awayColimitFunctor_map_comparison [IsTopologicalGroup G] [IsTopologicalGroup H]
    [HasColimitsOfShape (Ordered G)ᵒᵖ C] [HasColimitsOfShape (Ordered (H × H'))ᵒᵖ C]
    (F : (CompactOpenLevel G)ᵒᵖ ⥤ C) {K₀ K₁ : CompactOpenLevel H} (a : K₀ ⟶ K₁) :
    ((awayColimitFunctor e F).map a.op).hom ≫ reindexComparison (awayOver e K₀) F =
      reindexComparison (awayOver e K₁) F ≫ translate F (factorHom e a.element) := by
  rw [reindexComparison_awayOver, reindexComparison_awayOver, transportColimitIso_hom]
  refine (Category.assoc _ _ _).symm.trans ((partialColimitFunctor_map_comparison_assoc
    (splitTower e F) a (reindexComparison (transportOver e.symm) F)).trans ?_)
  exact (Category.assoc _ _ _).trans ((whisker_eq _ (translate_reindexComparison
    (transportOver e.symm) F (a.element, 1))).trans (Category.assoc _ _ _).symm)

end Functorial

section Smooth

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H'] {R : Type t}
  [CommRing R] [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]
  [HasColimitsOfShape (Ordered H')ᵒᵖ (ModuleCat.{w} R)]

/-- The smooth representation of `H'` on the colimit of the away tower at `K₀` of a level-trivial
presheaf of modules. -/
def awaySmoothRep (K₀ : CompactOpenLevel H) (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R)
    (hF : IsLevelTrivial F) : SmoothRep.{t, v₂, w} R H' :=
  smoothRep (awayTower e K₀ F) (isLevelTrivial_awayTower e K₀ hF)

omit [IsTopologicalGroup H] in
/-- The image of the away colimit at `K₀` is fixed by `factorHom e k` for `k ∈ K₀`. -/
theorem translate_awayComparison_apply_of_mem [Nonempty (CompactOpenLevel H')]
    (F : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{w} R) (hF : IsLevelTrivial F)
    (K₀ : CompactOpenLevel H) {k : H} (hk : k ∈ K₀.subgroup)
    (x : (colimit (diagram (awayTower e K₀ F)) : ModuleCat.{w} R)) :
    (translate F (factorHom e k)).hom ((reindexComparison (awayOver e K₀) F).hom x) =
      (reindexComparison (awayOver e K₀) F).hom x :=
  translate_reindexComparison_apply_of_mem (awayOver e K₀) F hF
    (fun K' => factorHom_mem_transport_symm_prod e K' hk) x

end Smooth

end Split

end LevelColimit

end Langlands.Shimura
