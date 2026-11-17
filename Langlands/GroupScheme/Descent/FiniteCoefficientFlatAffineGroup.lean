import Langlands.GroupScheme.Descent.Data
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType

/-! # Finite coefficient models of affine flat finitely presented groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

private theorem flatAffine_fg_tower (T : Subalgebra R A) (U : Subalgebra T A)
    (hT : T.FG) (hU : U.FG) : (U.restrictScalars R).FG := by
  have h₁ : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).mp hT
  have h₂ : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have h₃ : Algebra.FiniteType R U := Algebra.FiniteType.trans h₁ h₂
  exact (Subalgebra.fg_iff_finiteType (U.restrictScalars R)).mpr h₃

private theorem flat_of_group_iso {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) (h : Flat G.X.hom) : Flat H.X.hom := by
  have sq : IsPullback e.inv.hom.hom.left H.X.hom G.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [Category.comp_id]; exact e.inv.hom.hom.w⟩
  exact MorphismProperty.of_isPullback sq h

/-- A finite coefficient model retaining affineness, flatness, finite
presentation and any commutativity of the actual group. -/
structure FlatAffineGroupModel (G : GroupScheme (Spec (CommRingCat.of A))) where
  coefficients : Subalgebra R A
  finite : coefficients.FG
  group : GroupScheme (Spec (CommRingCat.of coefficients))
  affine : IsAffineHom group.X.hom
  flat : Flat group.X.hom
  finitePresentation : LocallyOfFinitePresentation group.X.hom
  commutative : IsCommMonObj G.X → IsCommMonObj group.X
  iso : G ≅ (baseChange (Spec.algebraMap coefficients A)).obj group

/-- Every affine flat finitely presented group descends to finite coefficients
containing any prescribed finite subset of the base algebra. -/
theorem exists_flatAffineGroupModel
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (s : Finset A) :
    ∃ D : FlatAffineGroupModel R A G, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨T, hT, hs, -, X₀, f₀, π, hX₀, hfp, hqc, hqs, hπ⟩ :=
    exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
      (A₀ := R) (R := R) G.X.hom s
  let := hX₀
  let := hfp
  let := hqc
  let := hqs
  obtain ⟨U, hU, -, H, a, ha, hcomm, ⟨e⟩⟩ :=
    Langlands.GroupScheme.subalgebraDescent f₀ G π hπ (∅ : Finset A)
  have hHaff : IsAffineHom H.X.hom :=
    MorphismProperty.of_isPullback ha (inferInstance : IsAffineHom f₀)
  have hHqc : QuasiCompact H.X.hom :=
    MorphismProperty.of_isPullback ha hqc
  have hHfp : LocallyOfFinitePresentation H.X.hom :=
    MorphismProperty.of_isPullback ha hfp
  let := hHqc
  let := hHfp
  have hflat : Flat (pullback.snd H.X.hom (Spec.algebraMap U A)) :=
    flat_of_group_iso e inferInstance
  let := hflat
  obtain ⟨V, hV, -, hVflat⟩ :=
    Flat.exists_fg_subalgebra_of_flat_pullback_snd H.X.hom (∅ : Finset A)
  have hcomp : Spec.algebraMap V A ≫ Spec.algebraMap U V =
      Spec.algebraMap U A := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let D : FlatAffineGroupModel R A G :=
    { coefficients := V.restrictScalars R
      finite := flatAffine_fg_tower R A (U.restrictScalars R) V
        (flatAffine_fg_tower R A T U hT hU) hV
      group := (baseChange (Spec.algebraMap U V)).obj H
      affine := by
        let := hHaff
        change IsAffineHom (pullback.snd H.X.hom (Spec.algebraMap U V))
        infer_instance
      flat := hVflat
      finitePresentation := by
        change LocallyOfFinitePresentation (pullback.snd H.X.hom (Spec.algebraMap U V))
        infer_instance
      commutative := fun hc => by
        let := hcomm hc
        exact inferInstanceAs
          (IsCommMonObj ((baseChange (Spec.algebraMap U V)).obj H).X)
      iso := e ≪≫
        (pullbackComparison (Spec.algebraMap U V) (Spec.algebraMap V A)
          (Spec.algebraMap U A) hcomp H).symm }
  refine ⟨D, ?_⟩
  intro x hx
  have hxT : x ∈ T := hs hx
  have hxU : x ∈ U := U.algebraMap_mem ⟨x, hxT⟩
  exact V.algebraMap_mem ⟨x, hxU⟩

/-- Choose a finite coefficient model without imposing smoothness on the group. -/
def flatAffineGroupModel
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    FlatAffineGroupModel R A G :=
  Classical.choose (exists_flatAffineGroupModel R A G ∅)

/-- Finite coefficients over a noetherian ring are noetherian. -/
theorem FlatAffineGroupModel.noetherian [IsNoetherianRing R]
    {G : GroupScheme (Spec (CommRingCat.of A))} (D : FlatAffineGroupModel R A G) :
    IsNoetherianRing D.coefficients := by
  have : Algebra.FiniteType R D.coefficients :=
    (Subalgebra.fg_iff_finiteType _).mp D.finite
  exact Algebra.FiniteType.isNoetherianRing R D.coefficients

end Langlands.GroupScheme.Descent.FiniteCoefficient
