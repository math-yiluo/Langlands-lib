import Langlands.GroupScheme.Descent.Data
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd

/-! # Finite coefficient models of separated finitely presented groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

private theorem separated_fg_tower (T : Subalgebra R A) (U : Subalgebra T A)
    (hT : T.FG) (hU : U.FG) : (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem separated_of_group_iso {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) (h : IsSeparated G.X.hom) : IsSeparated H.X.hom := by
  have sq : IsPullback e.inv.hom.hom.left H.X.hom G.X.hom (𝟙 S) :=
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    IsPullback.of_horiz_isIso
      ⟨by rw [Category.comp_id]; exact e.inv.hom.hom.w⟩
  exact MorphismProperty.of_isPullback sq h

/-- An actual separated finitely presented group over finite coefficients,
with an isomorphism recovering the supplied group. -/
structure SeparatedGroupModel (G : GroupScheme (Spec (CommRingCat.of A))) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  group : GroupScheme (Spec (CommRingCat.of coefficients))
  separated : IsSeparated group.X.hom
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  iso : G ≅ (baseChange (Spec.algebraMap coefficients A)).obj group

/-- A separated finitely presented group descends to finitely generated
coefficients containing any prescribed finite set. -/
theorem exists_separatedGroupModel
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] (s : Finset A) :
    ∃ D : SeparatedGroupModel R A G, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨T, hT, hs, X₀, f₀, π, hfp, hqc, hqs, hπ⟩ :=
    exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := R) G.X.hom s
  let := hfp
  let := hqc
  let := hqs
  obtain ⟨U, hU, -, H, a, ha, -, ⟨e⟩⟩ :=
    Langlands.GroupScheme.subalgebraDescent f₀ G π hπ (∅ : Finset A)
  have hHqc : QuasiCompact H.X.hom :=
    MorphismProperty.of_isPullback ha hqc
  have hHqs : QuasiSeparated H.X.hom :=
    MorphismProperty.of_isPullback ha hqs
  have hHfp : LocallyOfFinitePresentation H.X.hom :=
    MorphismProperty.of_isPullback ha hfp
  let := hHqc
  let := hHqs
  let := hHfp
  have hsep : IsSeparated (pullback.snd H.X.hom (Spec.algebraMap U A)) :=
    separated_of_group_iso e inferInstance
  let := hsep
  obtain ⟨V, hV, -, hVsep⟩ :=
    IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd H.X.hom (∅ : Finset A)
  have hcomp : Spec.algebraMap V A ≫ Spec.algebraMap U V =
      Spec.algebraMap U A := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let D : SeparatedGroupModel R A G :=
    { coefficients := V.restrictScalars R
      finite := separated_fg_tower R A (U.restrictScalars R) V
        (separated_fg_tower R A T U hT hU) hV
      group := (baseChange (Spec.algebraMap U V)).obj H
      separated := hVsep
      finitePresentation := by
        change LocallyOfFinitePresentation (pullback.snd H.X.hom (Spec.algebraMap U V))
        infer_instance
      quasiCompact := by
        change QuasiCompact (pullback.snd H.X.hom (Spec.algebraMap U V))
        infer_instance
      iso := e ≪≫
        (pullbackComparison (Spec.algebraMap U V) (Spec.algebraMap V A)
          (Spec.algebraMap U A) hcomp H).symm }
  refine ⟨D, ?_⟩
  intro x hx
  have hxT : x ∈ T := hs hx
  have hxU : x ∈ U := U.algebraMap_mem ⟨x, hxT⟩
  exact V.algebraMap_mem ⟨x, hxU⟩

/-- Choose a separated finitely presented model over finite coefficients. -/
def separatedGroupModel
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] : SeparatedGroupModel R A G :=
  Classical.choose (exists_separatedGroupModel R A G ∅)

end Langlands.GroupScheme.Descent.FiniteCoefficient
