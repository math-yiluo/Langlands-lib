/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluedStages

/-!
# A scheme with a finite affine gluing presentation is the limit of its glued stages

Let `G` be a finite affine gluing presentation of a scheme `S`. The inclusions `Aₐ ⊆ Γ(S, Uₐ)` of
the coefficient subrings of a stage `l` induce compatible morphisms `S ⟶ S_l` to the glued
finite-type stages (`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.stageCone`), and we
show that they exhibit `S` as the limit of the `S_l`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.isLimitStageCone`). This gives an
explicit Noetherian approximation of `S`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.noetherianApproximation`), independent
of `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation` except for the cofinality of the
stages.

## Implementation details

The limit property is checked chart by chart: over the chart `Spec Aₐ` of a stage, the system
restricts to the spectra `Spec A'ₐ` of the coefficient subrings of the larger stages, whose limit
is `Spec Γ(S, Uₐ) = Uₐ` since `Γ(S, Uₐ)` is the directed union of the `A'ₐ`. The cofinality of
the stages (`exists_stage_superset`) is used to show that `Γ(S, Uₐ)` is this union.

Instead of forming the limit `lim S_l` and the comparison map `κ_S : S ⟶ lim S_l` explicitly, we
show that the cone `stageCone` is a limit cone, which says precisely that `κ_S` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry


namespace Scheme.FiniteAffineGluingPresentation

variable {S : Scheme.{u}} {G : S.FiniteAffineGluingPresentation}

/-- Opens of `S` are determined by their preimages in the charts of a finite affine gluing
presentation. -/
lemma opens_ext (G : S.FiniteAffineGluingPresentation) {O₁ O₂ : S.Opens}
    (h : ∀ a, (G.U a : S.Opens).ι ⁻¹ᵁ O₁ = (G.U a : S.Opens).ι ⁻¹ᵁ O₂) : O₁ = O₂ := by
  ext x
  have hx : x ∈ ⨆ a, (G.U a : S.Opens) := by
    rw [G.iSup_U]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have := SetLike.ext_iff.mp (h a) ⟨x, ha⟩
  exact this

namespace Stage

variable (l : G.Stage)

lemma subringChart_homOfLE_eq (a b : G.ι) :
    S.homOfLE (inf_le_left : (G.U a : S.Opens) ⊓ G.U b ≤ G.U a) ≫
        subringChart (l.A a) le_rfl ≫ l.ι a =
      S.homOfLE (inf_le_right : (G.U a : S.Opens) ⊓ G.U b ≤ G.U b) ≫
        subringChart (l.A b) le_rfl ≫ l.ι b := by
  rw [homOfLE_subringChart_assoc, homOfLE_subringChart_assoc, ← l.chartLiftOverlap_ι_assoc,
    ← l.glue_condition, l.trans_ι_assoc, l.chartLiftOverlap_toChart_assoc]

/-- The comparison morphism `S ⟶ S_l`, glued from the chart maps `Uₐ ⟶ Spec Aₐ` induced by the
inclusions `Aₐ ⊆ Γ(S, Uₐ)`. -/
noncomputable def fromS : S ⟶ l.scheme :=
  G.openCover.glueMorphisms (fun a ↦ subringChart (l.A a) le_rfl ≫ l.ι a) fun a b ↦ by
    have hP : IsPullback (S.homOfLE inf_le_left) (S.homOfLE inf_le_right) (G.openCover.f a)
        (G.openCover.f b) :=
      isPullback_opens_inf (G.U a : S.Opens) (G.U b)
    rw [← hP.isoPullback_inv_fst, ← hP.isoPullback_inv_snd, Category.assoc, Category.assoc,
      l.subringChart_homOfLE_eq a b]

lemma openCover_f (a : G.ι) : G.openCover.f a = (G.U a : S.Opens).ι :=
  rfl

@[reassoc (attr := simp)]
lemma ι_fromS (a : G.ι) : (G.U a : S.Opens).ι ≫ l.fromS = subringChart (l.A a) le_rfl ≫ l.ι a :=
  G.openCover.ι_glueMorphisms _ _ a

@[reassoc (attr := simp)]
lemma fromS_transition {l' : G.Stage} (hll : l ≤ l') : l'.fromS ≫ transition hll = l.fromS :=
  G.openCover.hom_ext _ _ fun a ↦ by
    rw [openCover_f, ι_fromS_assoc, ι_transition, ι_fromS,
      subringChart_comp_SpecMap_inclusion_assoc]

lemma fromS_preimage_opensRange_ι (a : G.ι) : l.fromS ⁻¹ᵁ (l.ι a).opensRange = G.U a := by
  refine G.opens_ext fun b ↦ ?_
  rw [← Scheme.Hom.comp_preimage, ι_fromS, Scheme.Hom.comp_preimage, preimage_opensRange_ι,
    overlap, subringChart_preimage_iSup_basicOpen, ← l.inf_eq_iSup_basicOpen,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

end Stage

/-- The cone over the diagram of glued stages formed by the compatible morphisms `S ⟶ S_l`
(`Stage.fromS`) induced by the inclusions of the coefficient subrings `Aₐ ⊆ Γ(S, Uₐ)`. -/
noncomputable def stageCone (G : S.FiniteAffineGluingPresentation) : Cone G.stageDiagram where
  pt := S
  π :=
    { app l := l.unop.fromS
      naturality _ _ f := (Category.id_comp _).trans
        (Stage.fromS_transition _ (leOfHom f.unop)).symm }

@[simp]
lemma stageCone_π_app (l : (G.Stage)ᵒᵖ) : G.stageCone.π.app l = l.unop.fromS := rfl

/-! ### The chart systems -/

/-- The coefficient rings of the chart `a` of the stages, as a diagram of rings. -/
@[simps]
def chartRing (G : S.FiniteAffineGluingPresentation) (a : G.ι) : G.Stage ⥤ CommRingCat.{u} where
  obj l := l.ring a
  map f := Stage.incl (leOfHom f) a

/-- `Γ(S, Uₐ)` as a cocone over the coefficient rings of the chart `a`. -/
@[simps]
def chartCocone (G : S.FiniteAffineGluingPresentation) (a : G.ι) : Cocone (G.chartRing a) where
  pt := Γ(S, G.U a)
  ι := { app l := CommRingCat.ofHom (l.A a).subtype }

instance : IsFiltered G.Stage := isFiltered_of_directed_le_nonempty _

/-- `Γ(S, Uₐ)` is the filtered colimit (the directed union) of the coefficient subrings of the
chart `a` of the stages: every section lies in the coefficient subring of some stage. -/
noncomputable def isColimitChartCocone (G : S.FiniteAffineGluingPresentation) (a : G.ι) :
    IsColimit (G.chartCocone a) := by
  have : ReflectsColimit (G.chartRing a) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun l y z hyz ↦ ?_)
  · obtain ⟨l, hl⟩ := G.exists_stage_mem a x
    exact ⟨l, ⟨x, hl⟩, rfl⟩
  · exact ⟨l, 𝟙 l, Subtype.ext hyz⟩

/-- The spectra of the coefficient rings of the chart `a`. -/
noncomputable abbrev chartSpecDiagram (G : S.FiniteAffineGluingPresentation) (a : G.ι) :
    (G.Stage)ᵒᵖ ⥤ Scheme.{u} :=
  (G.chartRing a).op ⋙ Scheme.Spec

/-- `Spec Γ(S, Uₐ)` as a cone over the spectra of the coefficient rings of the chart `a`. -/
noncomputable def chartSpecCone (G : S.FiniteAffineGluingPresentation) (a : G.ι) :
    Cone (G.chartSpecDiagram a) :=
  Scheme.Spec.mapCone (G.chartCocone a).op

lemma chartSpecCone_π_app (a : G.ι) (l : (G.Stage)ᵒᵖ) :
    (G.chartSpecCone a).π.app l = Spec.map (CommRingCat.ofHom (l.unop.A a).subtype) :=
  rfl

/-- `Spec Γ(S, Uₐ)` is the limit of the spectra of the coefficient rings of the chart `a`. -/
noncomputable def isLimitChartSpecCone (G : S.FiniteAffineGluingPresentation) (a : G.ι) :
    IsLimit (G.chartSpecCone a) :=
  isLimitOfPreserves Scheme.Spec (G.isColimitChartCocone a).op

/-- The chart `Spec Aₐ` of a stage, as an open of the glued stage. -/
noncomputable def chartOpen (G : S.FiniteAffineGluingPresentation) (l : (G.Stage)ᵒᵖ) (a : G.ι) :
    (G.stageDiagram.obj l).Opens :=
  (l.unop.ι a).opensRange

lemma stageDiagram_map_preimage_chartOpen {l l' : (G.Stage)ᵒᵖ} (f : l' ⟶ l) (a : G.ι) :
    G.stageDiagram.map f ⁻¹ᵁ G.chartOpen l a = G.chartOpen l' a :=
  Stage.transition_preimage_opensRange_ι _ a

lemma stageCone_π_preimage_chartOpen (l : (G.Stage)ᵒᵖ) (a : G.ι) :
    G.stageCone.π.app l ⁻¹ᵁ G.chartOpen l a = (G.U a).1 :=
  l.unop.fromS_preimage_opensRange_ι a

/-- The chart `Spec Aₐ` of the stages above `l₀`, as an open subscheme of the glued stages. -/
noncomputable def chartIso (G : S.FiniteAffineGluingPresentation) (l₀ : (G.Stage)ᵒᵖ) (a : G.ι) :
    Over.forget l₀ ⋙ G.chartSpecDiagram a ≅ opensDiagram G.stageDiagram l₀ (G.chartOpen l₀ a) :=
  NatIso.ofComponents
    (fun j ↦ IsOpenImmersion.isoOfRangeEq (j.left.unop.ι a)
      (Scheme.Opens.ι (G.stageDiagram.map j.hom ⁻¹ᵁ G.chartOpen l₀ a))
      (Scheme.Hom.range_eq_range_ι_of_opensRange_eq _
        (G.stageDiagram_map_preimage_chartOpen j.hom a).symm))
    (fun {j j'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (G.stageDiagram.map j'.hom ⁻¹ᵁ G.chartOpen l₀ a)),
        Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, stageDiagram_map,
        Stage.ι_transition]
      rfl)

@[reassoc (attr := simp)]
lemma chartIso_hom_app_ι (l₀ : (G.Stage)ᵒᵖ) (a : G.ι) (j : Over l₀) :
    (G.chartIso l₀ a).hom.app j ≫
        Scheme.Opens.ι (G.stageDiagram.map j.hom ⁻¹ᵁ G.chartOpen l₀ a) = j.left.unop.ι a :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (Scheme.Hom.range_eq_range_ι_of_opensRange_eq
    (j.left.unop.ι a) (G.stageDiagram_map_preimage_chartOpen j.hom a).symm)

/-- The restriction of the stage cone to a chart `Spec Aₐ` of a stage is a limit cone. -/
noncomputable def isLimitOpensConeChart (G : S.FiniteAffineGluingPresentation)
    (l₀ : (G.Stage)ᵒᵖ) (a : G.ι) :
    IsLimit (opensCone G.stageDiagram G.stageCone l₀ (G.chartOpen l₀ a)) :=
  IsLimit.equivOfNatIsoOfIso (G.chartIso l₀ a)
    ((G.chartSpecCone a).whisker (Over.forget l₀))
    (opensCone G.stageDiagram G.stageCone l₀ (G.chartOpen l₀ a))
    (Cone.ext ((G.U a).2.isoSpec.symm ≪≫ S.isoOfEq (G.stageCone_π_preimage_chartOpen l₀ a).symm)
      (fun j ↦ by
        rw [← cancel_mono (Scheme.Opens.ι (G.stageDiagram.map j.hom ⁻¹ᵁ G.chartOpen l₀ a))]
        simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
          Functor.whiskerLeft_app, Category.assoc, chartIso_hom_app_ι, opensCone_π_ι,
          Iso.trans_hom, Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, stageCone_π_app,
          Stage.ι_fromS, chartSpecCone_π_app, Over.forget_obj]
        rw [subringChart, ← IsAffineOpen.isoSpec_hom (G.U a).2, Category.assoc,
          Iso.inv_hom_id_assoc]
        congr 2
        ext x
        exact (resLE_refl x.1).symm))
    ((Functor.Initial.isLimitWhiskerEquiv _ (G.chartSpecCone a)).symm
      (G.isLimitChartSpecCone a))

/-- The stage cone is a limit cone. -/
noncomputable def isLimitStageCone (G : S.FiniteAffineGluingPresentation) :
    IsLimit G.stageCone :=
  isLimitOfIsLimitOpensCone' G.stageDiagram _ (op G.glueStage)
    (fun a ↦ G.chartOpen (op G.glueStage) a) G.glueStage.iSup_opensRange_ι
    fun a ↦ G.isLimitOpensConeChart (op G.glueStage) a

/-- The Noetherian approximation of a scheme `S` with a finite affine gluing presentation `G`,
given by the glued finite-type stages `S_l` (`Stage.scheme`), indexed by the opposite of the
directed set of valid stages, with the affine transition morphisms `S_{l'} ⟶ S_l`
(`Stage.transition`) and the comparison cone `S ⟶ S_l` (`stageCone`), which is a limit cone
(`isLimitStageCone`). -/
noncomputable def noetherianApproximation (G : S.FiniteAffineGluingPresentation) :
    S.NoetherianApproximation where
  I := (G.Stage)ᵒᵖ
  D := G.stageDiagram
  locallyOfFiniteType_obj l := inferInstanceAs
    (LocallyOfFiniteType (specULiftZIsTerminal.from l.unop.scheme))
  compactSpace_obj l := inferInstanceAs (CompactSpace l.unop.scheme)
  isAffineHom_map f := inferInstanceAs (IsAffineHom (Stage.transition (leOfHom f.unop)))
  π := G.stageCone.π
  isLimit := G.isLimitStageCone

@[simp]
lemma noetherianApproximation_D :
    G.noetherianApproximation.D = G.stageDiagram := rfl

end Scheme.FiniteAffineGluingPresentation

end AlgebraicGeometry
