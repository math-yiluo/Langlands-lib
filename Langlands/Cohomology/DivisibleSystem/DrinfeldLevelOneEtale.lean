import Langlands.Geometry.Analytic.DrinfeldLevelOneBase
import Langlands.Cohomology.DivisibleSystem.AnalyticEtaleConstant
import Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements
import Langlands.Sheaf.Equivariant.AnalyticSubgroupRestriction
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactSmoothness

/-!
# Harris's level-one space `ℳ_1 = Ω × Δ`: étale sheaves and compactly supported cohomology

The level-one space `Ω × Δ` of Drinfeld's tower for the matrix factor `GL_{d+1}(F)`
(`levelOneBase`, module `DrinfeldLevelOneBase`) carries an action of `GL_{d+1}(F)`. This module
specializes the étale `G`-sheaf constructions of `AnalyticEtaleRefinements`,
`DivisibleSystem.AnalyticEtale`, `DivisibleSystem.AnalyticEtaleConstant`,
`AnalyticSubgroupRestriction` and `AnalyticEtaleCompactSmoothness` to this action: the
admissible refinement condition, Berkovich's `H^q_c(ℳ_1{G}, -)`, the constant `ℓ`-divisible
system, Harris's Lemma 2.2 and 2.2 bis, the isomorphism (2.3), the map to plain compactly
supported cohomology, restriction to subgroups (for instance to the stabilizer `detNormOne` of
every copy of `Ω`), and smoothness of the action of `GL_{d+1}(F)` on `H^q_c(ℳ_1, b^*F)` granting
Berkovich's comparison statement and the continuity hypotheses of `levelOneGSpace`.
-/

noncomputable section

universe u uL

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open _root_.CategoryTheory SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ) [NeZero d]

/-- Harris's level-one space `ℳ_1 = Ω × Δ`, for the matrix factor `GL_{d+1}(F)`, as an
analytic space. -/
abbrev levelOneSpace : LocalizedCategory.{u, u, u} (K := K) :=
  (levelOneBase (F := F) (d := d) K).V

/-- The action of `GL_{d+1}(F)` on `Ω × Δ` by automorphisms. -/
abbrev levelOneρ : Matrix.GeneralLinearGroup (Fin (d + 1)) F →* Aut (levelOneSpace F K d) :=
  (levelOneBase (F := F) (d := d) K).ρAut

/-- The admissible refinement condition of the étale `GL_{d+1}(F)`-sheaves on `Ω × Δ`. It
follows from the existence of distinguished étale neighbourhoods on `Ω × Δ`, of lifts of the
action to distinguished étale objects, and of their compatibility (`AnalyticEtaleRefinements`). -/
theorem hasAdmissibleRefinements_levelOne
    (hA : HasDistinguishedEtaleNeighbourhoods (levelOneSpace F K d))
    (hB : HasDistinguishedEtaleLifts (levelOneρ F K d))
    (hC : HasCompatibleDistinguishedEtaleLifts (levelOneρ F K d)) :
    (distinguishedLiftSystem (levelOneρ F K d)).HasAdmissibleRefinements
      (twistedEtaleTopology (levelOneρ F K d)) :=
  hasAdmissibleRefinements_distinguishedLiftSystem _ hA hB hC

variable [IsUltrametricDist F]

/-- Given continuity of the action on `Ω` and `SetInducedSpace.ContinuityStatement`, the space
of `Ω × Δ` is Hausdorff (the first condition of `levelOneGSpace`). -/
theorem t2Space_levelOneSpace (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hSI : SetInducedSpace.ContinuityStatement.{u, u, u}) :
    T2Space (localizedSpaceFunctor.obj (levelOneSpace F K d)) :=
  (levelOneGSpace K hΩ hSI).property.1

/-- Given continuity of the action on `Ω` and `SetInducedSpace.ContinuityStatement`, the action
of `GL_{d+1}(F)` on `Ω × Δ` is continuous (the second condition of `levelOneGSpace`). -/
theorem isContinuousAction_levelOneρ (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
    (hSI : SetInducedSpace.ContinuityStatement.{u, u, u}) :
    IsContinuousAction (levelOneρ F K d) :=
  (levelOneGSpace K hΩ hSI).property.2

end Langlands.Analytic.DrinfeldUpperHalfSpace

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Analytic.DrinfeldUpperHalfSpace
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.Analytic
open Langlands.Cohomology.AnalyticEtaleCompactComparison

section LevelOne

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ) [NeZero d]
variable (R : Type (max u (u + 1) uL)) [CommRing R]

/-- Étale `GL_{d+1}(F)`-sheaves of `R`-modules on `Ω × Δ`. -/
abbrev LevelOneEtaleSheaf : Type _ :=
  EtaleGSheaf (levelOneρ F K d) (ModuleCat.{max u (u + 1) uL} R)

/-- Restriction of étale `GL_{d+1}(F)`-sheaves on `Ω × Δ` to étale `H`-sheaves, for any subgroup
`H` of `GL_{d+1}(F)` (`etaleGSheafSubgroupRestriction`). -/
abbrev levelOneEtaleSubgroupRestriction (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :
    LevelOneEtaleSheaf F K d R ⥤
      EtaleGSheaf ((levelOneρ F K d).comp H.subtype) (ModuleCat.{max u (u + 1) uL} R) :=
  etaleGSheafSubgroupRestriction (levelOneρ F K d) H (ModuleCat.{max u (u + 1) uL} R)

variable [(distinguishedLiftSystem (levelOneρ F K d)).HasAdmissibleRefinements
    (twistedEtaleTopology (levelOneρ F K d))]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj (levelOneSpace F K d),
  EtaleSite.PointAxioms L x)

/-- Berkovich's `H^q_c(ℳ_1{G}, -)`, `G = GL_{d+1}(F)`, on étale `G`-sheaves of `R`-modules on
`ℳ_1 = Ω × Δ`. -/
abbrev levelOneEtaleCompactCohomology (q : ℕ) :
    LevelOneEtaleSheaf F K d R ⥤
      SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R
        (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  etaleGSheafCompactCohomology L (levelOneρ F K d) h R q

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of étale `GL_{d+1}(F)`-sheaves on
`Ω × Δ`. -/
abbrev levelOneEtaleConstantSystem :
    EtaleDivisibleSystem.{u, u, uL} (levelOneρ F K d) R ℓ :=
  etaleConstantSystem.{u, u, uL} (levelOneρ F K d) R hℓ

variable {I : Type (max u (u + 1) uL)}
  (points : I → (etaleTopology (levelOneSpace F K d)).Point.{max u (u + 1) uL})
variable [PreservesFiniteLimits
    (etaleFamilyGodementFunctor.{u, u, uL} (levelOneρ F K d) points R)]
  [PreservesFiniteColimits
    (etaleFamilyGodementFunctor.{u, u, uL} (levelOneρ F K d) points R)]
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (u + 1) uL} R))

/-- Harris's Lemma 2.2 on `Ω × Δ` for étale sheaves: the `ℓ`-divisible system of the Godement
resolutions of the constant étale `GL_{d+1}(F)`-sheaves `R / ℓ ^ m R`, for the family
`points`. -/
abbrev levelOneEtaleConstantGodementResolutionSystem :
    EtaleComplexDivisibleSystem.{u, u, uL} (levelOneρ F K d) R ℓ :=
  etaleConstantFamilyGodementResolutionSystem.{u, u, uL} (levelOneρ F K d) points R hℓ hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis on `Ω × Δ` for étale sheaves: the truncation `τ_{≤ D+1}` of the
Godement resolution system of the constant system. -/
abbrev levelOneEtaleConstantGodementTruncatedResolutionSystem :
    EtaleComplexDivisibleSystem.{u, u, uL} (levelOneρ F K d) R ℓ :=
  etaleConstantFamilyGodementTruncatedResolutionSystem.{u, u, uL} (levelOneρ F K d) points R hℓ
    hpoints D

/-- Level `m` of the truncated resolution system on `Ω × Δ` resolves the constant étale
`GL_{d+1}(F)`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_levelOneEtaleConstantGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, u, uL} (levelOneSpace F K d) (levelOneρ F K d) R
    QuasiIso (etaleConstantFamilyGodementTruncatedAugmentation.{u, u, uL} (levelOneρ F K d)
      points R hℓ hpoints D m) :=
  quasiIso_etaleConstantFamilyGodementTruncatedAugmentation (levelOneρ F K d) points R hℓ
    hpoints D m

variable (hF : ∀ (M : LevelOneEtaleSheaf F K d R) (r : ℕ),
    IsZero ((levelOneEtaleCompactCohomology F K d R L h (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, u, uL} (levelOneρ F K d) points R).obj M)))
  (hdim : ∀ m n : ℕ, D < n →
    IsZero ((levelOneEtaleCompactCohomology F K d R L h n).obj
      ((etaleConstantSheaf.{u, u, uL} (levelOneρ F K d) R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- Harris's system of complexes `Γ_{c,ℳ_1{G}}(G^•_m)` of smooth representations of
`G = GL_{d+1}(F)` for the constant étale sheaves `R / ℓ ^ m R` on `Ω × Δ`. -/
abbrev levelOneEtaleConstantCompactSectionsSystem :
    DivisibleSystem (CochainComplex (SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R
      (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) ℕ) ℓ :=
  etaleConstantFamilyCompactSectionsSystem.{u, u, uL} (levelOneρ F K d) points R hℓ L h
    hpoints D hF hdim

/-- Harris (2.3) on `Ω × Δ` for étale sheaves: the cohomology of level `m` of the compact
section complexes is `H^n_c(ℳ_1{G}, R / ℓ ^ m R)`. -/
def levelOneEtaleConstantCompactHomologyIso (m n : ℕ) :
    ((levelOneEtaleConstantCompactSectionsSystem F K d R hℓ L h points hpoints D hF
      hdim).obj m).homology n ≅
      (levelOneEtaleCompactCohomology F K d R L h n).obj
        ((etaleConstantSheaf.{u, u, uL} (levelOneρ F K d) R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  etaleConstantFamilyCompactHomologyIso.{u, u, uL} (levelOneρ F K d) points R hℓ L h hpoints
    D hF hdim m n

/-- The map `H^n(Γ_{c,ℳ_1{G}}(G^•_m)) → H^n_c(ℳ_1, R / ℓ ^ m R)` from the cohomology of Harris's
complex of level `m`, with the action of `G = GL_{d+1}(F)` forgotten, to the plain compactly
supported étale cohomology of `Ω × Δ` with constant coefficients. That it is an isomorphism is
not proved. -/
abbrev levelOneEtaleConstantCompactHomologyToPlain (m n : ℕ) :
    haveI := etale_hasSheafify.{u, u, uL} (levelOneSpace F K d) R
    (smoothForget R (Matrix.GeneralLinearGroup (Fin (d + 1)) F)).obj
        (((levelOneEtaleConstantCompactSectionsSystem F K d R hℓ L h points hpoints D hF
          hdim).obj m).homology n) ⟶
      (etaleCompactCohomology L h R n).obj
        ((constantSheaf (etaleTopology (levelOneSpace F K d))
          (ModuleCat.{max u (u + 1) uL} R)).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  etaleConstantCompactHomologyToPlain.{u, u, uL} (levelOneρ F K d) points R hℓ L h hpoints D
    hF hdim m n

end LevelOne

section LevelOneRestriction

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ) [NeZero d]
variable (R : Type (max u (u + 1) uL)) [CommRing R]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj (levelOneSpace F K d),
  EtaleSite.PointAxioms L x)
variable (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F))

/-- The restriction to a subgroup `H` of the representation of `GL_{d+1}(F)` on
`H^q_c(ℳ_1, b^*F)` is the representation of `H` on `H^q_c(ℳ_1, b^*F|_H)`, naturally in the
étale `GL_{d+1}(F)`-sheaf `F` on `Ω × Δ`. -/
def levelOneEtaleSubgroupRestrictionCompactCohomologyIso (q : ℕ) :
    etaleRestrictionCompactCohomologyRep L (levelOneρ F K d) h R q ⋙
        Rep.resFunctor H.subtype ≅
      levelOneEtaleSubgroupRestriction F K d R H ⋙
        etaleRestrictionCompactCohomologyRep L ((levelOneρ F K d).comp H.subtype) h R q :=
  etaleSubgroupRestrictionCompactCohomologyIso (levelOneρ F K d) H R L h q

end LevelOneRestriction

section LevelOneSmoothness

variable (F : Type u) [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ) [NeZero d]
variable (R : Type (max u (u + 1) uL)) [CommRing R]
variable [(distinguishedLiftSystem (levelOneρ F K d)).HasAdmissibleRefinements
    (twistedEtaleTopology (levelOneρ F K d))]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj (levelOneSpace F K d),
  EtaleSite.PointAxioms L x)
variable (hB : AnalyticEtaleCompactComparisonStatement L (levelOneSpace F K d) h
    (Matrix.GeneralLinearGroup (Fin (d + 1)) F) (levelOneρ F K d) R)
  (hS : Function.Surjective (pointProjection L (levelOneSpace F K d)))
  (hΩ : IsContinuousAction (omegaAction F K d).ρAut)
  (hSI : SetInducedSpace.ContinuityStatement.{u, u, u})

include hB hS hΩ hSI

/-- Granting `AnalyticEtaleCompactComparisonStatement` for `Ω × Δ`, surjectivity of the
projection from `L`-valued points, continuity of the action on `Ω` and
`SetInducedSpace.ContinuityStatement`: the canonical action of `GL_{d+1}(F)` on
`H^q_c(ℳ_1, b^*F)` is smooth, for every étale `GL_{d+1}(F)`-sheaf `F` on `Ω × Δ`. -/
theorem levelOneEtaleRestrictionCompactCohomologyAction_isSmooth_of_statement (q : ℕ)
    (M : LevelOneEtaleSheaf F K d R) :
    Langlands.IsSmooth (etaleRestrictionCompactCohomologyAction L (levelOneρ F K d) h R q M) :=
  etaleRestrictionCompactCohomologyAction_isSmooth_of_statement L (levelOneρ F K d) h R hB
    (t2Space_levelOneSpace F K d hΩ hSI) hS (isContinuousAction_levelOneρ F K d hΩ hSI) q M

/-- Under the same hypotheses, the restriction of this action to any subgroup `H` of
`GL_{d+1}(F)` (for instance `detNormOne F d`, the stabilizer of every copy of `Ω`) is
smooth. -/
theorem levelOneEtaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement
    (q : ℕ) (M : LevelOneEtaleSheaf F K d R)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) :
    Langlands.IsSmooth
      ((etaleRestrictionCompactCohomologyAction L (levelOneρ F K d) h R q M).comp H.subtype) :=
  etaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement L
    (levelOneρ F K d) h R hB (t2Space_levelOneSpace F K d hΩ hSI) hS
    (isContinuousAction_levelOneρ F K d hΩ hSI) q M H

/-- Under the same hypotheses, Berkovich's comparison map
`H^q_c(ℳ_1{G}, F) → H^q_c(ℳ_1, b^*F)`, `G = GL_{d+1}(F)`, is bijective. -/
theorem levelOneEtaleCompactComparison_app_bijective_of_statement (q : ℕ)
    (M : LevelOneEtaleSheaf F K d R) :
    Function.Bijective ((etaleCompactComparison L (levelOneρ F K d) h R q).app M).hom :=
  etaleCompactComparison_app_bijective_of_statement L (levelOneρ F K d) h R hB
    (t2Space_levelOneSpace F K d hΩ hSI) hS (isContinuousAction_levelOneρ F K d hΩ hSI) q M

/-- Under the same hypotheses, Berkovich's comparison
`H^q_c(ℳ_1{G}, F) → H^q_c(ℳ_1, b^*F)`, `G = GL_{d+1}(F)`, is an isomorphism of smooth
representations. -/
def levelOneEtaleCompactComparisonSmoothIsoOfStatement (q : ℕ)
    (M : LevelOneEtaleSheaf F K d R) :
    (levelOneEtaleCompactCohomology F K d R L h q).obj M ≅
      etaleRestrictionCompactCohomologySmoothRep L (levelOneρ F K d) h R q M
        (levelOneEtaleCompactComparison_app_bijective_of_statement F K d R L h hB hS hΩ hSI q
          M).2 :=
  etaleCompactComparisonSmoothIsoOfStatement L (levelOneρ F K d) h R hB
    (t2Space_levelOneSpace F K d hΩ hSI) hS (isContinuousAction_levelOneρ F K d hΩ hSI) q M

end LevelOneSmoothness

end Langlands.Cohomology.DivisibleSystem.Analytic
