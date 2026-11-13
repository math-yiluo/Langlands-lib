import Langlands.Global.Factors.RelativeWeilLocalHecke

/-! # Local restrictions of a relation among induced Hecke characters -/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

attribute [local instance] relativeGaloisTopology

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- The restriction to `W_{F_z}` of `Σ_j r_j Ind_{W_{E/K_j}} ([θh_j ∘ τ] - [θh'_j ∘ τ])`, along a
local map `ιd` satisfying the local restriction formula for every `K_j`, is
`Σ_{(j, u)} r_j Ind_{K_{j,u}}^{F_z} ([θh_{j,u} ∘ rec] - [θh'_{j,u} ∘ rec])`, with the finite
components of the Hecke characters at the places `u` of `K_j` above `z` and the transported
reciprocity candidates of a normalized family of `F_z`. -/
theorem continuousRestrict_sum_induce_eq_weilCharacter
    (h : FundamentalClass.Restriction c)
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    {J : Type*} [Fintype J] (r : J → ℤ) (K : J → IntermediateField F E)
    (θh θh' : ∀ j, HeckeCharacter (K j))
    {z : Langlands.Global.FinitePlace F}
    (ιd : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hloc : ∀ j, LocalInducedRestriction.{max u uV, u} c F (K j) E h z ιd)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC) :
    ExactGrothendieckGroup.continuousRestrict ιd
        (∑ j, r j • ExactGrothendieckGroup.continuousInduceAlong
          (restrictionInclusion c F E (K j) h)
          (isOpenEmbedding_restrictionInclusion c F E (K j) h)
          (ExactGrothendieckGroup.characterClass.{u, max u uV}
              (continuousReciprocityCharacter c (K j) E (θh j)) -
            ExactGrothendieckGroup.characterClass.{u, max u uV}
              (continuousReciprocityCharacter c (K j) E (θh' j)))) =
      ∑ j : (Σ j, FinitePlacesAbove (K j) z), r j.1 •
        ExactGrothendieckGroup.continuousInduceAlong
          (Weil.Local.extensionWeilMap (padicField z) (towerPadicField z j.2.1)
            (completionPadicAlgHom z j.2.1))
          (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
          (ExactGrothendieckGroup.characterClass.{u, max u uV}
              (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                (LocalClassField.extensionReciprocityCandidate (padicField z)
                  (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                  ((θh j.1).finiteComponent j.2.1))) -
            ExactGrothendieckGroup.characterClass.{u, max u uV}
              (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                (LocalClassField.extensionReciprocityCandidate (padicField z)
                  (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                  ((θh' j.1).finiteComponent j.2.1)))) := by
  choose ιu hτ hres using hloc
  rw [map_sum]
  refine Eq.trans ?_ (Fintype.sum_sigma _).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_zsmul (ExactGrothendieckGroup.continuousRestrict ιd) (r j) _).trans ?_
  refine (congrArg (r j • ·) (hres j _)).trans ?_
  refine (Finset.smul_sum ..).trans ?_
  refine Finset.sum_congr rfl fun u _ => congrArg (r j • ·) ?_
  have hu := (hgeo _ _ eC heC).2 (towerPadicField z u.1) (completionPadicAlgHom z u.1)
  have h1 := continuousReciprocityCharacter_comp_eq_weilCharacter (θh j) u.1
    (residuePrime_eq z u.1) _ (ιu j u) (hτ j u _ hu)
  have h2 := continuousReciprocityCharacter_comp_eq_weilCharacter (θh' j) u.1
    (residuePrime_eq z u.1) _ (ιu j u) (hτ j u _ hu)
  exact congrArg (ExactGrothendieckGroup.continuousInduceAlong (completionWeilMap z u.1)
    (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _))
    ((map_sub (ExactGrothendieckGroup.continuousRestrict (ιu j u)) _ _).trans
      (congrArg₂ (· - ·)
        ((ExactGrothendieckGroup.continuousRestrict_characterClass _ _).trans
          (congrArg ExactGrothendieckGroup.characterClass.{u, max u uV} h1))
        ((ExactGrothendieckGroup.continuousRestrict_characterClass _ _).trans
          (congrArg ExactGrothendieckGroup.characterClass.{u, max u uV} h2))))

/-- **Local relations.** If `Σ_j r_j Ind_{W_{E/K_j}} ([θh_j ∘ τ] - [θh'_j ∘ τ]) = 0` in the
continuous exact virtual group of `W_{E/F}`, then at every finite place `z` and local map
`ιd` satisfying the local restriction formula,
`Σ_{(j, u)} r_j Ind_{K_{j,u}}^{F_z} ([θh_{j,u} ∘ rec] - [θh'_{j,u} ∘ rec]) = 0`. -/
theorem sum_induce_weilCharacter_eq_zero
    (h : FundamentalClass.Restriction c)
    (hgeo : LocalClassField.CommonClosureGeometricStatement.{u, u})
    {J : Type*} [Fintype J] (r : J → ℤ) (K : J → IntermediateField F E)
    (θh θh' : ∀ j, HeckeCharacter (K j))
    (hrel : ∑ j, r j • ExactGrothendieckGroup.continuousInduceAlong
          (restrictionInclusion c F E (K j) h)
          (isOpenEmbedding_restrictionInclusion c F E (K j) h)
          (ExactGrothendieckGroup.characterClass.{u, max u uV}
              (continuousReciprocityCharacter c (K j) E (θh j)) -
            ExactGrothendieckGroup.characterClass.{u, max u uV}
              (continuousReciprocityCharacter c (K j) E (θh' j))) =
      (0 : ContinuousVirtual.{u, uV} c F E))
    {z : Langlands.Global.FinitePlace F}
    (ιd : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hloc : ∀ j, LocalInducedRestriction.{max u uV, u} c F (K j) E h z ιd)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC) :
    ∑ j : (Σ j, FinitePlacesAbove (K j) z), r j.1 •
        ExactGrothendieckGroup.continuousInduceAlong
          (Weil.Local.extensionWeilMap (padicField z) (towerPadicField z j.2.1)
            (completionPadicAlgHom z j.2.1))
          (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
          (ExactGrothendieckGroup.characterClass.{u, max u uV}
              (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                (LocalClassField.extensionReciprocityCandidate (padicField z)
                  (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                  ((θh j.1).finiteComponent j.2.1))) -
            ExactGrothendieckGroup.characterClass.{u, max u uV}
              (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
                (LocalClassField.extensionReciprocityCandidate (padicField z)
                  (towerPadicField z j.2.1) (completionPadicAlgHom z j.2.1) eC)
                (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                  ((θh' j.1).finiteComponent j.2.1)))) = 0 := by
  refine
    (continuousRestrict_sum_induce_eq_weilCharacter h hgeo r K θh θh' ιd hloc eC heC).symm.trans ?_
  exact (congrArg (ExactGrothendieckGroup.continuousRestrict ιd) hrel).trans (map_zero _)

end Langlands.ClassField.Global.RelativeWeilGroup
