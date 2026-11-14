import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Sheaf.Equivariant.AnalyticRepComparison
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement
import Langlands.Representation.Category.Basic

/-!
# Smoothness of the action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)`

Let `G` act on an analytic space `X` and let `F` be an étale (or quasi-étale) `G`-sheaf of
modules. Berkovich deduces that the canonical action of `G` on `H^q_c(X, b^*F)`
(Corollary 1.5.2(i)) and, for compact `X`, on `H^q(X, b^*F)` (Theorem 1.6.1(ii)) is discrete
from the comparison isomorphisms with `H^q_c(X{G}, F)` and `H^q(X{G}, F)`, which are smooth
representations. This module formalizes this deduction. Each comparison map is an
intertwining map (`AnalyticRepComparison`). If it is surjective, the action on its target is
smooth, and the target is bundled as a smooth representation. If it is bijective, it is an
isomorphism of smooth representations. For compact `X` with a continuous action, the
quasi-étale case of Theorem 1.6.1(ii), stated as
`AnalyticQuasiEtaleGlobalComparisonStatement`, implies bijectivity. The surjectivity and
bijectivity of the comparison maps are hypotheses here, not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section EtaleGlobal

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` for an étale `G`-sheaf `F`, as an
intertwining map from the action of `G` on `H^q(X{G}, F)` to the canonical action on
`H^q(X, b^*F)`. -/
def etaleComparisonIntertwiningMap (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    ((etaleGSheafCohomology.{u, v, uL} ρ R q).obj F).representation.IntertwiningMap
      (etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((etaleComparison.{u, v, uL} ρ R q).app F).hom
    (etaleComparison_representation.{u, v, uL} ρ R q F)

/-- The underlying map of `etaleComparisonIntertwiningMap` is the comparison map. -/
theorem etaleComparisonIntertwiningMap_apply (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (x : (etaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G).obj F) :
    etaleComparisonIntertwiningMap.{u, v, uL} ρ R q F x =
      ((etaleComparison.{u, v, uL} ρ R q).app F).hom x :=
  rfl

/-- If the comparison `H^q(X{G}, F) → H^q(X, b^*F)` is surjective, the canonical action of
`G` on `H^q(X, b^*F)` is smooth. -/
theorem etaleRestrictionCohomologyAction_isSmooth_of_surjective (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleComparison.{u, v, uL} ρ R q).app F).hom) :
    Langlands.IsSmooth (etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) :=
  Langlands.isSmooth_of_surjective (etaleComparisonIntertwiningMap.{u, v, uL} ρ R q F) hs
    (SmoothRep.isSmooth _)

/-- `H^q(X, b^*F)` with the canonical action of `G`, as a smooth representation, when the
comparison `H^q(X{G}, F) → H^q(X, b^*F)` is surjective. -/
def etaleRestrictionCohomologySmoothRep (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleComparison.{u, v, uL} ρ R q).app F).hom) :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  SmoothRep.of (etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F)
    (etaleRestrictionCohomologyAction_isSmooth_of_surjective.{u, v, uL} ρ R q F hs)

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` as a morphism of smooth representations,
when it is surjective. -/
def etaleComparisonSmoothHom (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (etaleGSheafCohomology.{u, v, uL} ρ R q).obj F ⟶
      etaleRestrictionCohomologySmoothRep.{u, v, uL} ρ R q F hs :=
  SmoothRep.ofHom (etaleComparisonIntertwiningMap.{u, v, uL} ρ R q F)

/-- If the comparison `H^q(X{G}, F) → H^q(X, b^*F)` is bijective, it is an isomorphism of
smooth representations. -/
def etaleComparisonSmoothIso (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((etaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (etaleGSheafCohomology.{u, v, uL} ρ R q).obj F ≅
      etaleRestrictionCohomologySmoothRep.{u, v, uL} ρ R q F hb.2 :=
  SmoothRep.mkIso ((etaleComparisonIntertwiningMap.{u, v, uL} ρ R q F).ofBijective hb)

/-- The isomorphism `etaleComparisonSmoothIso` is `etaleComparisonSmoothHom`. -/
theorem etaleComparisonSmoothIso_hom (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((etaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (etaleComparisonSmoothIso.{u, v, uL} ρ R q F hb).hom =
      etaleComparisonSmoothHom.{u, v, uL} ρ R q F hb.2 :=
  rfl

end EtaleGlobal

section EtaleCompact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` for an étale `G`-sheaf `F`, with supports
in the `L`-valued points, as an intertwining map from the action of `G` on `H^q_c(X{G}, F)` to
the canonical action on `H^q_c(X, b^*F)`. -/
def etaleCompactComparisonIntertwiningMap (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    ((etaleGSheafCompactCohomology L ρ h R q).obj F).representation.IntertwiningMap
      (etaleRestrictionCompactCohomologyAction L ρ h R q F) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((etaleCompactComparison L ρ h R q).app F).hom
    (etaleCompactComparison_representation L ρ h R q F)

/-- The underlying map of `etaleCompactComparisonIntertwiningMap` is the comparison map. -/
theorem etaleCompactComparisonIntertwiningMap_apply (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (x : (etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G).obj F) :
    etaleCompactComparisonIntertwiningMap L ρ h R q F x =
      ((etaleCompactComparison L ρ h R q).app F).hom x :=
  rfl

/-- If the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is surjective, the canonical action of
`G` on `H^q_c(X, b^*F)` is smooth. -/
theorem etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleCompactComparison L ρ h R q).app F).hom) :
    Langlands.IsSmooth (etaleRestrictionCompactCohomologyAction L ρ h R q F) :=
  Langlands.isSmooth_of_surjective (etaleCompactComparisonIntertwiningMap L ρ h R q F) hs
    (SmoothRep.isSmooth _)

/-- `H^q_c(X, b^*F)` with the canonical action of `G`, as a smooth representation, when the
comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is surjective. -/
def etaleRestrictionCompactCohomologySmoothRep (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleCompactComparison L ρ h R q).app F).hom) :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  SmoothRep.of (etaleRestrictionCompactCohomologyAction L ρ h R q F)
    (etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective L ρ h R q F hs)

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` as a morphism of smooth representations,
when it is surjective. -/
def etaleCompactComparisonSmoothHom (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((etaleCompactComparison L ρ h R q).app F).hom) :
    (etaleGSheafCompactCohomology L ρ h R q).obj F ⟶
      etaleRestrictionCompactCohomologySmoothRep L ρ h R q F hs :=
  SmoothRep.ofHom (etaleCompactComparisonIntertwiningMap L ρ h R q F)

/-- If the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is bijective, it is an isomorphism of
smooth representations. -/
def etaleCompactComparisonSmoothIso (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((etaleCompactComparison L ρ h R q).app F).hom) :
    (etaleGSheafCompactCohomology L ρ h R q).obj F ≅
      etaleRestrictionCompactCohomologySmoothRep L ρ h R q F hb.2 :=
  SmoothRep.mkIso ((etaleCompactComparisonIntertwiningMap L ρ h R q F).ofBijective hb)

/-- The isomorphism `etaleCompactComparisonSmoothIso` is `etaleCompactComparisonSmoothHom`. -/
theorem etaleCompactComparisonSmoothIso_hom (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((etaleCompactComparison L ρ h R q).app F).hom) :
    (etaleCompactComparisonSmoothIso L ρ h R q F hb).hom =
      etaleCompactComparisonSmoothHom L ρ h R q F hb.2 :=
  rfl

end EtaleCompact

section QuasiEtaleGlobal

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` for a quasi-étale `G`-sheaf `F`, as an
intertwining map from the action of `G` on `H^q(X{G}, F)` to the canonical action on
`H^q(X, b^*F)`. -/
def quasiEtaleComparisonIntertwiningMap (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    ((quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F).representation.IntertwiningMap
      (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom
    (quasiEtaleComparison_representation.{u, v, uL} ρ R q F)

/-- The underlying map of `quasiEtaleComparisonIntertwiningMap` is the comparison map. -/
theorem quasiEtaleComparisonIntertwiningMap_apply (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (x : (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G).obj F) :
    quasiEtaleComparisonIntertwiningMap.{u, v, uL} ρ R q F x =
      ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom x :=
  rfl

/-- If the comparison `H^q(X{G}, F) → H^q(X, b^*F)` is surjective, the canonical action of
`G` on `H^q(X, b^*F)` is smooth. -/
theorem quasiEtaleRestrictionCohomologyAction_isSmooth_of_surjective (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom) :
    Langlands.IsSmooth (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) :=
  Langlands.isSmooth_of_surjective
    (quasiEtaleComparisonIntertwiningMap.{u, v, uL} ρ R q F) hs (SmoothRep.isSmooth _)

/-- `H^q(X, b^*F)` with the canonical action of `G`, as a smooth representation, when the
comparison `H^q(X{G}, F) → H^q(X, b^*F)` is surjective. -/
def quasiEtaleRestrictionCohomologySmoothRep (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom) :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  SmoothRep.of (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F)
    (quasiEtaleRestrictionCohomologyAction_isSmooth_of_surjective.{u, v, uL} ρ R q F hs)

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` as a morphism of smooth representations,
when it is surjective. -/
def quasiEtaleComparisonSmoothHom (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F ⟶
      quasiEtaleRestrictionCohomologySmoothRep.{u, v, uL} ρ R q F hs :=
  SmoothRep.ofHom (quasiEtaleComparisonIntertwiningMap.{u, v, uL} ρ R q F)

/-- If the comparison `H^q(X{G}, F) → H^q(X, b^*F)` is bijective, it is an isomorphism of
smooth representations. -/
def quasiEtaleComparisonSmoothIso (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F ≅
      quasiEtaleRestrictionCohomologySmoothRep.{u, v, uL} ρ R q F hb.2 :=
  SmoothRep.mkIso ((quasiEtaleComparisonIntertwiningMap.{u, v, uL} ρ R q F).ofBijective hb)

/-- The isomorphism `quasiEtaleComparisonSmoothIso` is `quasiEtaleComparisonSmoothHom`. -/
theorem quasiEtaleComparisonSmoothIso_hom (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom) :
    (quasiEtaleComparisonSmoothIso.{u, v, uL} ρ R q F hb).hom =
      quasiEtaleComparisonSmoothHom.{u, v, uL} ρ R q F hb.2 :=
  rfl

open AnalyticQuasiEtaleGlobalComparison in
/-- Berkovich's Theorem 1.6.1(ii) for quasi-étale sheaves, stated as
`AnalyticQuasiEtaleGlobalComparisonStatement`, implies that for compact `X` with a continuous
action the comparison `H^q(X{G}, F) → H^q(X, b^*F)` is bijective. -/
theorem quasiEtaleComparison_app_bijective_of_statement
    (hB : AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL} X G ρ R)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Function.Bijective ((quasiEtaleComparison.{u, v, uL} ρ R q).app F).hom := by
  have := hB hX hρ q
  exact ConcreteCategory.bijective_of_isIso ((quasiEtaleComparison.{u, v, uL} ρ R q).app F)

open AnalyticQuasiEtaleGlobalComparison in
/-- Granting `AnalyticQuasiEtaleGlobalComparisonStatement` (Berkovich, Theorem 1.6.1(ii),
quasi-étale case): for compact `X` with a continuous action, the canonical action of `G` on
`H^q(X, b^*F)` is smooth. -/
theorem quasiEtaleRestrictionCohomologyAction_isSmooth_of_statement
    (hB : AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL} X G ρ R)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Langlands.IsSmooth (quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F) :=
  quasiEtaleRestrictionCohomologyAction_isSmooth_of_surjective.{u, v, uL} ρ R q F
    (quasiEtaleComparison_app_bijective_of_statement.{u, v, uL} ρ R hB hX hρ q F).2

open AnalyticQuasiEtaleGlobalComparison in
/-- Granting `AnalyticQuasiEtaleGlobalComparisonStatement` (Berkovich, Theorem 1.6.1(ii),
quasi-étale case): for compact `X` with a continuous action, the comparison
`H^q(X{G}, F) → H^q(X, b^*F)` is an isomorphism of smooth representations. -/
def quasiEtaleComparisonSmoothIsoOfStatement
    (hB : AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL} X G ρ R)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F ≅
      quasiEtaleRestrictionCohomologySmoothRep.{u, v, uL} ρ R q F
        (quasiEtaleComparison_app_bijective_of_statement.{u, v, uL} ρ R hB hX hρ q F).2 :=
  quasiEtaleComparisonSmoothIso.{u, v, uL} ρ R q F
    (quasiEtaleComparison_app_bijective_of_statement.{u, v, uL} ρ R hB hX hρ q F)

end QuasiEtaleGlobal

section QuasiEtaleCompact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` for a quasi-étale `G`-sheaf `F`, with
supports in the `L`-valued points, as an intertwining map from the action of `G` on
`H^q_c(X{G}, F)` to the canonical action on `H^q_c(X, b^*F)`. -/
def quasiEtaleCompactComparisonIntertwiningMap (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj F).representation.IntertwiningMap
      (quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((quasiEtaleCompactComparison L ρ h R q).app F).hom
    (quasiEtaleCompactComparison_representation L ρ h R q F)

/-- The underlying map of `quasiEtaleCompactComparisonIntertwiningMap` is the comparison
map. -/
theorem quasiEtaleCompactComparisonIntertwiningMap_apply (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (x : (quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G).obj F) :
    quasiEtaleCompactComparisonIntertwiningMap L ρ h R q F x =
      ((quasiEtaleCompactComparison L ρ h R q).app F).hom x :=
  rfl

/-- If the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is surjective, the canonical action of
`G` on `H^q_c(X, b^*F)` is smooth. -/
theorem quasiEtaleRestrictionCompactCohomologyAction_isSmooth_of_surjective (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleCompactComparison L ρ h R q).app F).hom) :
    Langlands.IsSmooth (quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F) :=
  Langlands.isSmooth_of_surjective
    (quasiEtaleCompactComparisonIntertwiningMap L ρ h R q F) hs (SmoothRep.isSmooth _)

/-- `H^q_c(X, b^*F)` with the canonical action of `G`, as a smooth representation, when the
comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is surjective. -/
def quasiEtaleRestrictionCompactCohomologySmoothRep (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleCompactComparison L ρ h R q).app F).hom) :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  SmoothRep.of (quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F)
    (quasiEtaleRestrictionCompactCohomologyAction_isSmooth_of_surjective L ρ h R q F hs)

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` as a morphism of smooth representations,
when it is surjective. -/
def quasiEtaleCompactComparisonSmoothHom (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hs : Function.Surjective ((quasiEtaleCompactComparison L ρ h R q).app F).hom) :
    (quasiEtaleGSheafCompactCohomology L ρ h R q).obj F ⟶
      quasiEtaleRestrictionCompactCohomologySmoothRep L ρ h R q F hs :=
  SmoothRep.ofHom (quasiEtaleCompactComparisonIntertwiningMap L ρ h R q F)

/-- If the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` is bijective, it is an isomorphism of
smooth representations. -/
def quasiEtaleCompactComparisonSmoothIso (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((quasiEtaleCompactComparison L ρ h R q).app F).hom) :
    (quasiEtaleGSheafCompactCohomology L ρ h R q).obj F ≅
      quasiEtaleRestrictionCompactCohomologySmoothRep L ρ h R q F hb.2 :=
  SmoothRep.mkIso ((quasiEtaleCompactComparisonIntertwiningMap L ρ h R q F).ofBijective hb)

/-- The isomorphism `quasiEtaleCompactComparisonSmoothIso` is
`quasiEtaleCompactComparisonSmoothHom`. -/
theorem quasiEtaleCompactComparisonSmoothIso_hom (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (hb : Function.Bijective ((quasiEtaleCompactComparison L ρ h R q).app F).hom) :
    (quasiEtaleCompactComparisonSmoothIso L ρ h R q F hb).hom =
      quasiEtaleCompactComparisonSmoothHom L ρ h R q F hb.2 :=
  rfl

end QuasiEtaleCompact

end Langlands.Sheaf.Equivariant.Analytic
