import Langlands.Shimura.PartialLevelTower
import Langlands.Shimura.PEL.TraceSimilitudesLevels

/-! # Colimits over levels reindexed along cofinal level functors -/

noncomputable section

universe u v v' w t

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite

namespace CompactOpenLevel

namespace FunctorOver

section Cofinal

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {φ : H →* G}

/-- The image levels of `Φ` are cofinal: every level of `G` contains the image of a level of
`H`. -/
def IsCofinal (Φ : FunctorOver φ) : Prop :=
  ∀ L : CompactOpenLevel G, ∃ K : CompactOpenLevel H, (Φ.functor.obj K).subgroup ≤ L.subgroup

theorem isCofinal_id (E : Type t) [Group E] [TopologicalSpace E] : (id E).IsCofinal :=
  fun L => ⟨L, le_rfl⟩

theorem IsCofinal.comp {E : Type t} [Group E] [TopologicalSpace E] {ψ : G →* E}
    {Φ : FunctorOver φ} {Ψ : FunctorOver ψ} (hΦ : Φ.IsCofinal) (hΨ : Ψ.IsCofinal) :
    (Φ.comp Ψ).IsCofinal := fun L =>
  let ⟨M, hM⟩ := hΨ L
  let ⟨K, hK⟩ := hΦ M
  ⟨K, (Ψ.le_of_le hK).trans hM⟩

end Cofinal

end FunctorOver

section Transport

variable {G : Type v} {H : Type v'} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Transport of levels along a topological group isomorphism `e`, as a level functor over `e`. -/
def transportOver (e : G ≃ₜ* H) : FunctorOver (e : G →* H) where
  functor := transportFunctor e
  map_element _ := rfl
  map_mem K _ hk := (transport_mem e K _).2 hk

@[simp] theorem transportOver_functor (e : G ≃ₜ* H) :
    (transportOver e).functor = transportFunctor e :=
  rfl

theorem transport_transport_symm (e : G ≃ₜ* H) (L : CompactOpenLevel H) :
    transport e (transport e.symm L) = L :=
  transport_symm e.symm L

theorem isCofinal_transportOver (e : G ≃ₜ* H) : (transportOver e).IsCofinal := fun L =>
  ⟨transport e.symm L, (congrArg subgroup (transport_transport_symm e L)).le⟩

end Transport

end CompactOpenLevel

namespace LevelColimit

open CompactOpenLevel

section Cofinal

variable {H : Type v'} {G : Type v} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {C : Type u} [Category.{w} C] {φ : H →* G} (Φ : FunctorOver φ)
  (F : (CompactOpenLevel G)ᵒᵖ ⥤ C)

/-- Restrictions along two successive inclusions of levels compose to the restriction along
the composite inclusion. -/
theorem map_inclusion_op_comp {K L M : CompactOpenLevel G} (h₁ : K.subgroup ≤ L.subgroup)
    (h₂ : L.subgroup ≤ M.subgroup) :
    F.map (inclusion h₂).op ≫ F.map (inclusion h₁).op = F.map (inclusion (h₁.trans h₂)).op := by
  rw [← F.map_comp, ← op_comp]
  exact congrArg (fun a : K ⟶ M => F.map a.op) (Arrow.ext (mul_one (1 : G)))

theorem reindex_map_inclusion_op {K L : CompactOpenLevel H} (h : K.subgroup ≤ L.subgroup) :
    (reindex Φ F).map (inclusion h).op = F.map (inclusion (Φ.le_of_le h)).op := by
  change F.map (Φ.functor.map (inclusion h)).op = _
  rw [Φ.map_inclusion]

variable [HasColimitsOfShape (Ordered H)ᵒᵖ C] [IsTopologicalGroup H]

/-- Restricting from a level `L` of `G` to an image level `Φ K ⊆ L` and including level `K` into
the colimit of the reindexed presheaf does not depend on `K`. -/
theorem map_inclusion_ι_reindex_eq {L : CompactOpenLevel G} {K K' : CompactOpenLevel H}
    (hK : (Φ.functor.obj K).subgroup ≤ L.subgroup)
    (hK' : (Φ.functor.obj K').subgroup ≤ L.subgroup) :
    F.map (inclusion hK).op ≫ ι (reindex Φ F) K =
      F.map (inclusion hK').op ≫ ι (reindex Φ F) K' := by
  have key : ∀ {K₁ : CompactOpenLevel H} (h₁ : (Φ.functor.obj K₁).subgroup ≤ L.subgroup)
      (h : (inf K K').subgroup ≤ K₁.subgroup),
      F.map (inclusion h₁).op ≫ ι (reindex Φ F) K₁ =
        F.map (inclusion ((Φ.le_of_le h).trans h₁)).op ≫ ι (reindex Φ F) (inf K K') := by
    intro K₁ h₁ h
    rw [← map_inclusion_ι (reindex Φ F) h, reindex_map_inclusion_op, ← Category.assoc,
      map_inclusion_op_comp]
  rw [key hK (fun _ hx => hx.1), key hK' (fun _ hx => hx.2)]

variable [HasColimitsOfShape (Ordered G)ᵒᵖ C] {Φ} (hΦ : Φ.IsCofinal)

/-- A chosen level of `H` whose image lies in the level `L` of `G`. -/
def cofinalLevel (L : CompactOpenLevel G) : CompactOpenLevel H :=
  (hΦ L).choose

omit [IsTopologicalGroup H] in
theorem cofinalLevel_le (L : CompactOpenLevel G) :
    (Φ.functor.obj (cofinalLevel hΦ L)).subgroup ≤ L.subgroup :=
  (hΦ L).choose_spec

omit [HasColimitsOfShape (Ordered G)ᵒᵖ C] in
theorem cofinalCocone_naturality {L L' : CompactOpenLevel G} (hle : L'.subgroup ≤ L.subgroup) :
    F.map (inclusion hle).op ≫ F.map (inclusion (cofinalLevel_le hΦ L')).op ≫
        ι (reindex Φ F) (cofinalLevel hΦ L') =
      F.map (inclusion (cofinalLevel_le hΦ L)).op ≫ ι (reindex Φ F) (cofinalLevel hΦ L) := by
  rw [← Category.assoc, map_inclusion_op_comp]
  exact map_inclusion_ι_reindex_eq Φ F _ _

/-- The cocone on the levels of `G` whose leg at `L` restricts to the chosen image level inside
`L` and includes it into the colimit of the reindexed presheaf. -/
def cofinalCocone : Cocone (diagram F) where
  pt := colimit (diagram (reindex Φ F))
  ι :=
    { app := fun L => F.map (inclusion (cofinalLevel_le hΦ L.unop)).op ≫
          ι (reindex Φ F) (cofinalLevel hΦ L.unop)
      naturality := fun _ _ a =>
        (cofinalCocone_naturality F hΦ (leOfHom a.unop)).trans (Category.comp_id _).symm }

/-- The inverse comparison, from the colimit of `F` to the colimit of the reindexed presheaf. -/
def reindexComparisonInv : colimit (diagram F) ⟶ colimit (diagram (reindex Φ F)) :=
  colimit.desc _ (cofinalCocone F hΦ)

@[reassoc (attr := simp)]
theorem ι_reindexComparisonInv (L : CompactOpenLevel G) :
    ι F L ≫ reindexComparisonInv F hΦ =
      F.map (inclusion (cofinalLevel_le hΦ L)).op ≫ ι (reindex Φ F) (cofinalLevel hΦ L) :=
  colimit.ι_desc (cofinalCocone F hΦ) (op L)

/-- Along a level functor with cofinal image, the comparison of colimits is an isomorphism. -/
@[simps]
def reindexColimitIso : colimit (diagram (reindex Φ F)) ≅ colimit (diagram F) where
  hom := reindexComparison Φ F
  inv := reindexComparisonInv F hΦ
  hom_inv_id := hom_ext _ fun K => by
    rw [ι_reindexComparison_assoc, ι_reindexComparisonInv, Category.comp_id,
      map_inclusion_ι_reindex_eq Φ F _ (Φ.le_of_le (le_refl K.subgroup)),
      ← reindex_map_inclusion_op Φ F (le_refl K.subgroup), map_inclusion_ι]
  inv_hom_id := hom_ext _ fun L => by
    rw [ι_reindexComparisonInv_assoc, ι_reindexComparison, map_inclusion_ι, Category.comp_id]

include hΦ in
theorem isIso_reindexComparison : IsIso (reindexComparison Φ F) :=
  (reindexColimitIso F hΦ).isIso_hom

variable [IsTopologicalGroup G]

/-- Along a level functor with cofinal image, the comparison of colimits is an isomorphism of
objects with an action of `H`, where `H` acts on the colimit of `F` through `φ`. -/
def reindexActionIso : action (reindex Φ F) ≅ (Action.res C φ).obj (action F) :=
  Action.mkIso (reindexColimitIso F hΦ) fun h => translate_reindexComparison Φ F h

@[simp] theorem reindexActionIso_hom :
    (reindexActionIso F hΦ).hom = reindexComparisonHom Φ F :=
  rfl

variable (C) in
/-- Along a level functor with cofinal image, the comparison maps form a natural isomorphism of
functors from presheaves on the levels of `G` to objects with an action of `H`. -/
def reindexNatIso : reindexFunctor C Φ ⋙ functor H C ≅ functor G C ⋙ Action.res C φ :=
  NatIso.ofComponents (fun F => reindexActionIso F hΦ) fun α =>
    Action.Hom.ext (map_reindexComparison Φ α)

@[simp] theorem reindexNatIso_hom :
    (reindexNatIso C hΦ).hom = reindexComparisonNatTrans C Φ :=
  rfl

end Cofinal

section Transport

variable {G : Type v} {H : Type v'} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {C : Type u} [Category.{w} C]
  [HasColimitsOfShape (Ordered G)ᵒᵖ C] [HasColimitsOfShape (Ordered H)ᵒᵖ C]
  (e : G ≃ₜ* H) (F : (CompactOpenLevel H)ᵒᵖ ⥤ C)

/-- The colimit over the levels of `G` of the presheaf `K ↦ F (e K)` is the colimit of `F`. -/
def transportColimitIso :
    colimit (diagram (reindex (transportOver e) F)) ≅ colimit (diagram F) :=
  reindexColimitIso F (isCofinal_transportOver e)

omit [IsTopologicalGroup H] in
@[simp] theorem transportColimitIso_hom :
    (transportColimitIso e F).hom = reindexComparison (transportOver e) F :=
  rfl

/-- Transport of the colimit along `e`, as an isomorphism of objects with an action of `G`,
where `G` acts on the colimit of `F` through `e`. -/
def transportActionIso :
    action (reindex (transportOver e) F) ≅ (Action.res C (e : G →* H)).obj (action F) :=
  reindexActionIso F (isCofinal_transportOver e)

theorem translate_transportColimitIso (g : G) :
    translate (reindex (transportOver e) F) g ≫ (transportColimitIso e F).hom =
      (transportColimitIso e F).hom ≫ translate F (e g) :=
  translate_reindexComparison (transportOver e) F g

variable (C) in
/-- Transport along `e`, as a natural isomorphism of functors from presheaves on the levels of
`H` to objects with an action of `G`. -/
def transportNatIso :
    reindexFunctor C (transportOver e) ⋙ functor G C ≅ functor H C ⋙ Action.res C (e : G →* H) :=
  reindexNatIso C (isCofinal_transportOver e)

end Transport

end LevelColimit

end Langlands.Shimura
