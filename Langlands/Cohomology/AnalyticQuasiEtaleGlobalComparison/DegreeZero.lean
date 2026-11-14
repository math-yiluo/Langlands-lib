import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement

/-! # Smooth global sections on a compact analytic space -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G] (ρ : G →* Aut X)

/-- The original continuous action lifts to the identity of the analytic space. -/
def identityActionLift (hρ : IsContinuousAction ρ) : ActionLift ρ (𝟙 X) where
  subgroup := ⊤
  isOpen_subgroup := isOpen_univ
  action := ρ.comp (⊤ : Subgroup G).subtype
  isContinuousAction := hρ.comp ⟨(⊤ : Subgroup G).subtype, continuous_subtype_val⟩
  equivariant h := by simp

variable (R : Type (max u (v + 1) uL)) [CommRing R]

omit [IsTopologicalGroup G] in
/-- Every global section of a quasi-étale `G`-sheaf on a compact space is smooth. -/
theorem isSmooth_quasiEtaleGlobalSections (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Langlands.IsSmooth ((sheafGlobalSectionsRep (quasiEtaleTopology X) R).obj F.obj).ρ := by
  intro s
  let l : ActionLift ρ (TwistedOver.hom (base quasiEtale ρ)) :=
    identityActionLift ρ hρ
  have ha : (compactLiftSystem ρ).IsAdmissible (base quasiEtale ρ)
      (liftOpenSubgroup l) (liftAction (U := base quasiEtale ρ) l) := by
    refine ⟨hX, l, le_rfl, ?_⟩
    ext g
    rfl
  obtain ⟨N, _, hN⟩ := F.property _ _ _ ha s
  refine ⟨N, ?_⟩
  intro g
  exact hN ⟨g, Subgroup.mem_top _⟩ g.property

/-- The inclusion of smooth global sections is an isomorphism for compact `X`. -/
theorem isIso_quasiEtaleGlobalInclusion (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) :
    IsIso (quasiEtaleGlobalInclusion.{u, v, uL} ρ R) := by
  have (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
      IsIso ((quasiEtaleGlobalInclusion.{u, v, uL} ρ R).app F) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro s t h
      exact Subtype.ext h
    · intro s
      exact ⟨⟨s, isSmooth_quasiEtaleGlobalSections.{u, v, uL, z} ρ R hX hρ F s⟩, rfl⟩
  exact NatIso.isIso_of_isIso_app _

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
