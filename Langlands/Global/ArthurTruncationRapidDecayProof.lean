import Langlands.Global.ArthurNormOneFamilyEstimateProof
import Langlands.Global.AdelicCompatibleIwasawaCompact
import Langlands.Global.AdelicSiegelSetupExistence
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.Global.FinitePlaceIwasawaProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.StandardMinimalLeviStructure

/-! # Arthur's Proposition 13.2 on `G(F) \ G(𝔸_F)¹`

Arthur 2005, Proposition 13.2(a),(b) and (13.5)–(13.6); Arthur 1980, Lemma 1.4. A maximal compact
subgroup `K` of `G(𝔸_F)` with `P₀(𝔸_F) K = G(𝔸_F)`, compatible with the positive torus of every
Siegel setup, is assembled from the finite-place Iwasawa decompositions and Levi-compatible
archimedean Iwasawa compacts. For it, `exists_isNormOneFamilyEstimate` gives the family estimate,
which proves `NormOneTruncationFamilyEstimateStatement`; the reduction
`truncationRapidDecayStatement_of_familyEstimate` then gives `TruncationRapidDecayStatement`. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

set_option backward.isDefEq.respectTransparency false

/-- A maximal compact subgroup `K` of `G(𝔸_F)` with `P₀(𝔸_F) K = G(𝔸_F)` whose parabolic part
commutes with the positive torus of every Siegel setup for the same `T`, `i`, `ν`. The
archimedean factors are Levi-compatible Iwasawa compacts, which depend on `P₀` and its Levi
only; the finite factors come from the finite-place Iwasawa decompositions. -/
theorem exists_parabolicIwasawaCompact_positiveTorusCompatible
    (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ K : Subgroup (AdelicGroupPoints F G),
      IsParabolicIwasawaCompact F G (Standard.parabolicScheme i ν ∅)
          (Standard.parabolicHom i ν ∅) K ∧
        ∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
          IsSiegelAlgebraicSetup F G T i ν T₀ j → IsPositiveTorusCompatible F G T i ν T₀ j K := by
  have hp : IsParabolicSubgroup (Standard.parabolicHom i ν ∅) :=
    (Standard.isMinimalParabolicSubgroup_parabolicHom_of_genericMinimal i ν
      genericMinimalParabolic hG hi hν).isParabolicSubgroup
  have hl : IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) :=
    (standardMinimalLeviStructure F G T i ν hG hi hν).2.1
  have : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
    hp.isClosedSubgroup
  have : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left
  obtain ⟨K₀, hK₀⟩ := IntegralIwasawaFamily.existenceStatement F G hG _ _ hp
  obtain ⟨Kloc, hKarch, hK⟩ := exists_leviCompatible_parabolicIwasawaCompact F G
    (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
    (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅)
    (InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement F G hG _ _ hp _ _ hl)
    (FinitePlaceGroupPoints.parabolicIwasawaStatement F G hG _ _ hp) K₀ hK₀
  exact ⟨_, hK, fun T₀ j hS =>
    isPositiveTorusCompatible_coordinateSubgroup F G T i ν T₀ j hS Kloc hKarch⟩

/-- **Arthur 2005, Proposition 13.2(b), for a suitable maximal compact subgroup.** -/
theorem normOneTruncationFamilyEstimate : NormOneTruncationFamilyEstimateStatement.{u, v} := by
  intro F _ _ G _ _ T i _ ν hG hi hν e At
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨K, hKP, hKc⟩ :=
    exists_parabolicIwasawaCompact_positiveTorusCompatible F G T i ν hG hi hν
  refine ⟨K, hKP.isIwasawaCompact, hKP.1, hKc, fun D hρ N rho hN hcl => ?_⟩
  exact exists_isNormOneFamilyEstimate.{u, v} hG hi hν D hKP.isIwasawaCompact hρ At rho hN hcl

/-- **Arthur 2005, Proposition 13.2, on `G(F) \ G(𝔸_F)¹`.** -/
theorem truncationRapidDecay : TruncationRapidDecayStatement.{u, v} :=
  truncationRapidDecayStatement_of_familyEstimate normOneTruncationFamilyEstimate

end Langlands.Global.ArthurTruncation
