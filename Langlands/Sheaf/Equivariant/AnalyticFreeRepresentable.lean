import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableMono
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRefinements
import Langlands.Sheaf.Equivariant.AnalyticSubgroupRestriction
import Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityStatement

/-! # Analytic actions and discrete free lifted representables -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}

section Action

variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))}
variable (U : P.Over ⊤ X) (σ : G →* Aut U.left)
variable (hσ : ∀ g : G, (σ g).hom ≫ U.hom = U.hom ≫ (ρ g).hom)

/-- A full equivariant analytic action gives the global lift used to normalize
the ordinary representable. Continuity is not needed for this construction. -/
def actionGlobalLift : GlobalLift (P := P) (ρ := ρ) where
  obj := U
  action :=
    { toFun g := MulOpposite.op (homMk g⁻¹ (σ g⁻¹).hom (hσ g⁻¹))
      map_one' := by
        apply MulOpposite.unop_injective
        refine hom_ext inv_one ?_
        change (σ 1⁻¹).hom = 𝟙 _
        rw [inv_one, map_one]
        rfl
      map_mul' g h := by
        apply MulOpposite.unop_injective
        refine hom_ext (mul_inv_rev g h) ?_
        change (σ (g * h)⁻¹).hom = (σ g⁻¹).hom ≫ (σ h⁻¹).hom
        rw [mul_inv_rev, map_mul]
        rfl }
  twist _ := rfl

omit [TopologicalSpace G] in
@[simp]
theorem actionGlobalLift_action_left (g : G) :
    Hom.left ((actionGlobalLift U σ hσ).action g).unop = (σ g⁻¹).hom := rfl

/-- A continuous full action, viewed as a local lift with subgroup top. -/
def fullActionLift (hcont : IsContinuousAction σ) : ActionLift ρ U.hom where
  subgroup := ⊤
  isOpen_subgroup := isOpen_univ
  action := σ.comp (⊤ : Subgroup G).subtype
  isContinuousAction := hcont.comp ⟨_, continuous_subtype_val⟩
  equivariant g := hσ g

end Action

/-- The published compatibility proposition supplies the fixed-action
compatibility condition; it remains an explicit premise here. -/
theorem hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement
    [IsTopologicalGroup G] (hKL : QuasiEtaleLiftCompatibilityStatement.{u, v, z} K)
    (hX : T2Space (localizedSpaceFunctor.obj X)) (hρ : IsContinuousAction ρ) :
    HasCompatibleCompactQuasiEtaleLifts ρ := by
  intro U V f hU hV a b
  exact hKL G X U.left V.left ρ U.hom V.hom f.left
    (MorphismProperty.Over.w f) hX hρ U.prop V.prop hU hV a b

/-- Compact-lift compatibility restricts to each open subgroup. -/
theorem hasCompatibleCompactQuasiEtaleLifts_subgroup (H : OpenSubgroup G)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) :
    HasCompatibleCompactQuasiEtaleLifts (ρ.comp (H : Subgroup G).subtype) := by
  intro U V f hU hV a b
  obtain ⟨N, hN, hNa, hNb, hf⟩ :=
    hC f hU hV (liftOfSubgroup H.isOpen a) (liftOfSubgroup H.isOpen b)
  refine ⟨N.comap (H : Subgroup G).subtype,
    hN.preimage continuous_subtype_val,
    (fun g hg => mk_mem_of_mem_map_subtype (hNa hg)),
    (fun g hg => mk_mem_of_mem_map_subtype (hNb hg)), fun g hg => ?_⟩
  exact hf (g : G) hg

variable (U : QuasiEtaleSite X) (σ : G →* Aut U.left)
variable (hσ : ∀ g : G, (σ g).hom ≫ U.hom = U.hom ≫ (ρ g).hom)

/-- Compatibility of compact analytic lifts gives eventual equivariance of
the actual globally lifted ordinary representable. -/
theorem actionGlobalLift_eventuallyEquivariant
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) (hU : IsCompactSpace U.left)
    (hcont : IsContinuousAction σ) :
    (actionGlobalLift U σ hσ).EventuallyEquivariant (compactLiftSystem ρ) := by
  rintro V H a ⟨hV, b, hH, rfl⟩ k
  obtain ⟨N, hN, hNa, hNb, hf⟩ :=
    hC k hU hV (fullActionLift U σ hσ hcont) b
  refine ⟨(⟨N, hN⟩ : OpenSubgroup G) ⊓ H, inf_le_right, fun h hh => ?_⟩
  refine hom_ext ((one_mul _).trans (mul_one _).symm) ?_
  exact hf (h : G)⁻¹ (inv_mem hh.1)

variable [LocallySmall.{w} (QuasiEtaleSite X)]

/-- Under compact-lift compatibility, the analytic lifted representable is
discrete for all admissible compact local actions. -/
theorem actionGlobalLift_isDiscrete
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) (hU : IsCompactSpace U.left)
    (hcont : IsContinuousAction σ) :
    (compactLiftSystem ρ).IsDiscrete (actionGlobalLift U σ hσ).presheaf :=
  (actionGlobalLift U σ hσ).isDiscrete_presheaf (compactLiftSystem ρ)
    (isLiftSystem_liftSystem _) (actionGlobalLift_eventuallyEquivariant U σ hσ hC hU hcont)

section Sheaf

variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedQuasiEtaleTopology ρ) (ModuleCat.{w} R)]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The analytic free lifted representable in the actual quasi-étale
`G`-sheaf category, under explicit compact-lift compatibility. -/
def actionDiscreteFreeSheaf
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) (hU : IsCompactSpace U.left)
    (hcont : IsContinuousAction σ) : QuasiEtaleGSheaf ρ (ModuleCat.{w} R) :=
  (actionGlobalLift U σ hσ).discreteFreeSheaf (compactLiftSystem ρ) (quasiEtaleTopology X) R
    (isLiftSystem_liftSystem _) (actionGlobalLift_eventuallyEquivariant U σ hσ hC hU hcont)

/-- For a monomorphic structure map, equivariance alone gives an actual free
quasi-étale `G`-sheaf. Compactness and analytic continuity are not required. -/
def actionDiscreteFreeSheafOfMono [Mono U.hom] : QuasiEtaleGSheaf ρ (ModuleCat.{w} R) := by
  letI : Mono (actionGlobalLift U σ hσ).obj.hom := ‹Mono U.hom›
  exact (actionGlobalLift U σ hσ).discreteFreeSheaf (compactLiftSystem ρ) (quasiEtaleTopology X) R
    (isLiftSystem_liftSystem _)
    ((actionGlobalLift U σ hσ).eventuallyEquivariant_of_mono (compactLiftSystem ρ)
      (isLiftSystem_liftSystem _))

end Sheaf

end Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable (U : QuasiEtaleSite X) (a : ActionLift ρ U.hom)
variable (H : OpenSubgroup G) (hH : (H : Subgroup G) ≤ a.subgroup)

/-- A local analytic lift becomes a full global lift for each chosen open
subgroup contained in its acting subgroup. -/
def liftGlobalLift :
    GlobalLift (P := quasiEtale) (ρ := ρ.comp (H : Subgroup G).subtype) :=
  actionGlobalLift U (a.action.comp (Subgroup.inclusion hH))
    (fun h => a.equivariant (Subgroup.inclusion hH h))

/-- Compact-lift compatibility makes the representable of a restricted local
analytic lift eventually equivariant in the subgroup's actual lift system. -/
theorem liftGlobalLift_eventuallyEquivariant
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) (hU : IsCompactSpace U.left) :
    (liftGlobalLift U a H hH).EventuallyEquivariant
      (compactLiftSystem (ρ.comp (H : Subgroup G).subtype)) :=
  actionGlobalLift_eventuallyEquivariant U _ _
    (hasCompatibleCompactQuasiEtaleLifts_subgroup H hC) hU
    (a.isContinuousAction.comp ⟨Subgroup.inclusion hH, continuous_inclusion hH⟩)

variable [LocallySmall.{w} (QuasiEtaleSite X)]
variable (R : Type w) [CommRing R]
variable [HasSheafify (twistedQuasiEtaleTopology (ρ.comp (H : Subgroup G).subtype))
  (ModuleCat.{w} R)]
variable [(compactLiftSystem (ρ.comp (H : Subgroup G).subtype)).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology (ρ.comp (H : Subgroup G).subtype))]

/-- The free quasi-étale `H`-sheaf supplied by a local analytic lift. -/
def liftDiscreteFreeSheaf
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) (hU : IsCompactSpace U.left) :
    QuasiEtaleGSheaf (ρ.comp (H : Subgroup G).subtype) (ModuleCat.{w} R) :=
  (liftGlobalLift U a H hH).discreteFreeSheaf
    (compactLiftSystem (ρ.comp (H : Subgroup G).subtype)) (quasiEtaleTopology X) R
    (isLiftSystem_liftSystem _) (liftGlobalLift_eventuallyEquivariant U a H hH hC hU)

end Langlands.Sheaf.Equivariant.Analytic
