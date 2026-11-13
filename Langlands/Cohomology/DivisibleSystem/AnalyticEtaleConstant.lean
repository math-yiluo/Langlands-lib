import Langlands.Sheaf.Equivariant.LocalActionSmoothConstant
import Langlands.Cohomology.DivisibleSystem.AnalyticEtale
import Langlands.Cohomology.DivisibleSystem.ConstantRestriction

/-!
# The constant `ℓ`-divisible system of étale `G`-sheaves

For a local action system with admissible refinements, the constant sheaf functor with values
in locally discrete sheaves is exact (`LocalActionSmoothConstant`), so it carries the published
`ℓ`-divisible system `scalarSystem R ℓ hℓ = {R / ℓ ^ m R}` to an `ℓ`-divisible system of
constant locally discrete sheaves.

For `G` acting on an analytic space `X`, this gives the constant `ℓ`-divisible system
`{R / ℓ ^ m R}` of Berkovich's étale `G`-sheaves, the system of constant sheaves `ℤ / ℓ ^ m ℤ`
resolved in Harris's Lemma 2.2 when `R = ℤ`. The module specializes Lemma 2.2, Lemma 2.2 bis,
(2.3) and Lemma 2.8 of `DivisibleSystem.AnalyticEtale` to this system. It also shows that
Berkovich's `b^*` takes the constant étale `G`-sheaf `M` to the constant sheaf `M` on the étale
site of `X`, and composes the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of
`AnalyticEtaleComparison` with this identification. The hypotheses of those results stay
hypotheses here. That the comparison maps are isomorphisms is not proved.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

universe u v uL z uG w

section Smooth

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T) (R : Type w) [CommRing R]
variable [HasSheafify J (ModuleCat.{w} R)] [L.HasAdmissibleRefinements J]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of locally discrete sheaves: the image
of `scalarSystem R ℓ hℓ` under the exact constant sheaf functor. -/
def smoothConstantSystem : DivisibleSystem (L.SmoothSheaf (ModuleCat.{w} R) J) ℓ :=
  (scalarSystem R ℓ hℓ).map (LocalActionSystem.smoothConstantSheaf L J R)

/-- Level `m` of the constant system is the constant sheaf `R / ℓ ^ m R`. -/
def smoothConstantSystemObjIso (m : ℕ) :
    (smoothConstantSystem L J R hℓ).obj m ≅
      (LocalActionSystem.smoothConstantSheaf L J R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})) :=
  (LocalActionSystem.smoothConstantSheaf L J R).mapIso (scalarSystemObjIso hℓ m)

/-- The maps `j` of the constant system are the constant sheaf maps of those of
`scalarSystem`. -/
theorem smoothConstantSystem_projection {m' m : ℕ} (h : m' ≤ m) :
    (smoothConstantSystem L J R hℓ).projection h =
      (LocalActionSystem.smoothConstantSheaf L J R).map ((scalarSystem R ℓ hℓ).projection h) :=
  rfl

/-- The maps `i` of the constant system are the constant sheaf maps of those of
`scalarSystem`. -/
theorem smoothConstantSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (smoothConstantSystem L J R hℓ).inclusion h =
      (LocalActionSystem.smoothConstantSheaf L J R).map ((scalarSystem R ℓ hℓ).inclusion h) :=
  rfl

end Smooth

namespace Analytic

open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.Equivariant.Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Constant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The constant étale `G`-sheaf functor: the sheafification on the twisted étale site of the
constant presheaf, which is locally discrete. -/
def etaleConstantSheaf :
    ModuleCat.{max u (v + 1) uL} R ⥤ EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  LocalActionSystem.smoothConstantSheaf (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) R

/-- Followed by the inclusion into all sheaves, the constant étale `G`-sheaf functor is the
constant sheaf functor of the twisted étale site. -/
theorem etaleConstantSheaf_comp_inclusion :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    etaleConstantSheaf.{u, v, uL} ρ R ⋙
        (distinguishedLiftSystem ρ).smoothSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
          (twistedEtaleTopology ρ) =
      constantSheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) :=
  rfl

variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of étale `G`-sheaves; for `R = ℤ` these
are the constant sheaves `ℤ / ℓ ^ m ℤ` of Harris's Lemma 2.2. -/
def etaleConstantSystem : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  smoothConstantSystem (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) R hℓ

/-- Level `m` of the constant system is the constant étale `G`-sheaf `R / ℓ ^ m R`. -/
def etaleConstantSystemObjIso (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (etaleConstantSystem.{u, v, uL} ρ R hℓ).obj m ≅
      (etaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  smoothConstantSystemObjIso (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) R hℓ m

/-- The constant system `{ℤ / ℓ ^ m ℤ}` of étale `G`-sheaves, for `ℓ ≠ 0`, with integers
lifted to the universe of the coefficients. -/
abbrev etaleIntConstantSystem {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    EtaleDivisibleSystem.{u, v, uL} ρ (ULift.{max u (v + 1) uL} ℤ) ℓ :=
  etaleConstantSystem.{u, v, uL} ρ (ULift.{max u (v + 1) uL} ℤ)
    (isSMulRegular_uLiftInt_natCast.{max u (v + 1) uL} hℓ)

end Constant

section ConstantBound

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (D : ℕ)
variable (hC : ∀ m n : ℕ, D < n →
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj
      ((etaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

include hC in
/-- The bound on the compactly supported cohomology of the constant sheaves `R / ℓ ^ m R`
transfers to the levels of the constant system. -/
theorem isZero_etaleGSheafCompactCohomology_constantSystem_obj (m n : ℕ) (hn : D < n) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj
      ((etaleConstantSystem.{u, v, uL} ρ R hℓ).obj m)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  (hC m n hn).of_iso
    ((etaleGSheafCompactCohomology L ρ h R n).mapIso
      (etaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m))

end ConstantBound

section ConstantResolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for the constant sheaves and the family `points`: the `ℓ`-divisible
system of the Godement resolutions of the constant étale `G`-sheaves `R / ℓ ^ m R`. -/
abbrev etaleConstantFamilyGodementResolutionSystem :
    EtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  etaleFamilyGodementResolutionSystem.{u, v, uL} ρ points R (etaleConstantSystem.{u, v, uL} ρ R hℓ)
    hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for the constant sheaves and the family `points`: the truncation
`τ_{≤ D+1}` of the Godement resolution system of the constant system. -/
abbrev etaleConstantFamilyGodementTruncatedResolutionSystem :
    EtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  etaleFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R
    (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D

/-- The augmentation `R / ℓ ^ m R ⟶ G^•_m` of level `m` of the truncated resolution system
of the constant system. -/
def etaleConstantFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj
        ((etaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) ⟶
      (etaleConstantFamilyGodementTruncatedResolutionSystem.{u, v, uL} ρ points R hℓ hpoints D).obj m :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  (CochainComplex.single₀ _).map (etaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m).inv ≫
    etaleFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R
      (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D m

/-- Level `m` of the truncated resolution system is a finite-length resolution of the
constant étale `G`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_etaleConstantFamilyGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (etaleConstantFamilyGodementTruncatedAugmentation.{u, v, uL} ρ points R hℓ hpoints D m) := by
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := quasiIso_etaleFamilyGodementTruncatedAugmentation ρ points R
    (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D m
  exact quasiIso_comp _ _

end ConstantResolution

section ConstantCompact

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj
      ((etaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for the constant sheaves `R / ℓ ^ m R` and the family `points`. -/
abbrev etaleConstantFamilyCompactSectionsSystem :
    DivisibleSystem
      (CochainComplex (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) ℕ) ℓ :=
  etaleFamilyGodementTruncatedCompactSectionsSystem.{u, v, uL} ρ points R L h
    (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_etaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC)

/-- Harris (2.3) for the constant sheaves and the family `points`: the cohomology of level
`m` of the compact section complexes is `H^n_c(X{G}, R / ℓ ^ m R)`. -/
def etaleConstantFamilyCompactHomologyIso (m n : ℕ) :
    ((etaleConstantFamilyCompactSectionsSystem.{u, v, uL} ρ points R hℓ L h hpoints D hF hC).obj
      m).homology n ≅
      (etaleGSheafCompactCohomology L ρ h R n).obj
        ((etaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  etaleFamilyGodementTruncatedCompactHomologyIso.{u, v, uL} ρ points R L h
      (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
      (isZero_etaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) m n ≪≫
    (etaleGSheafCompactCohomology L ρ h R n).mapIso
      (etaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m)

end ConstantCompact

section ConstantInverseLimit

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type u} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj
      ((etaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))
variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((etaleConstantFamilyCompactSectionsSystem.{u, v, uL} ρ points R hℓ L h hpoints D hF
        hC).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim_m C^•_m` for the constant sheaves `R / ℓ ^ m R` and the family `points`. -/
abbrev etaleConstantFamilyQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (v + 1) uL} R G) ℤ :=
  etaleFamilyGodementQuotientInvariantsInverseLimit.{u, v, uL} ρ points R L h
    (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_etaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) H hH hK hk

set_option synthInstance.maxHeartbeats 60000 in
/-- Harris's Lemma 2.8 for the constant sheaves and the family `points`: under the hypotheses
of `etaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso`, the degree-`n`
cohomology of `lim_m C^•_m` is the inverse limit over `m` of `H^n_c(X{G}, R / ℓ ^ m R)`
(level `m` of the constant system). -/
def etaleConstantFamilyQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, max u (v + 1) uL, max u (v + 1) uL})
    (hS' : FiniteCohomologyInverseLimitStatement.{max u (v + 1) uL, max u (v + 1) uL} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj
        ((etaleConstantSystem.{u, v, uL} ρ R hℓ).obj m))).ρ g = LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      Finite (SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj
        ((etaleConstantSystem.{u, v, uL} ρ R hℓ).obj m))))
    (n : ℕ) :
    (etaleConstantFamilyQuotientInvariantsInverseLimit.{u, v, uL} ρ points R hℓ L h hpoints D hF hC H
      hH hK hk).homology n ≅
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      limit ((etaleConstantSystem.{u, v, uL} ρ R hℓ).tower ⋙
        etaleGSheafCompactCohomology L ρ h R n ⋙ SmoothRep.toRep) :=
  etaleFamilyGodementQuotientInvariantsInverseLimitHomologyIso.{u, v, uL} ρ points R L h
    (etaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_etaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) H hH hK hk hS
    hS' hP hR htriv hfin n

end ConstantInverseLimit

end Analytic

end Langlands.Cohomology.DivisibleSystem

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology Langlands.Cohomology.DivisibleSystem
open Langlands.Cohomology.DivisibleSystem.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Restriction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Berkovich's `b^*` takes the constant étale `G`-sheaf `M` to the constant sheaf `M` on the
étale site of `X`. -/
def etaleConstantSheafRestrictionIso :
    haveI := etale_hasSheafify.{u, v, uL} X R
    etaleConstantSheaf.{u, v, uL} ρ R ⋙ etaleGSheafRestriction.{u, v, uL} ρ R ≅
      constantSheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  constantSheafCompRestrictionIso ρ (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)

end Restriction

section Comparison

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, M) → H^q_c(X, M)` for the constant sheaves `M`, natural in the
module `M`: Berkovich's comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` at the constant étale
`G`-sheaf `M`, followed by the identification of `b^*M` with the constant sheaf `M` of `X`.
That it is an isomorphism is not proved. -/
def etaleConstantCompactComparison (q : ℕ) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    etaleConstantSheaf.{u, v, uL} ρ R ⋙
        etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ⟶
      constantSheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⋙
        etaleCompactCohomology L h R q :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  Functor.whiskerLeft (etaleConstantSheaf.{u, v, uL} ρ R) (etaleCompactComparison L ρ h R q) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleConstantSheafRestrictionIso.{u, v, uL} ρ R).hom
      (etaleCompactCohomology L h R q)

/-- The component of the constant comparison at a module `M` is Berkovich's comparison at
the constant étale `G`-sheaf `M`, followed by the map induced by `b^*M ≅ M`. -/
theorem etaleConstantCompactComparison_app (q : ℕ) (M : ModuleCat.{max u (v + 1) uL} R) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    (etaleConstantCompactComparison L ρ h R q).app M =
      (etaleCompactComparison L ρ h R q).app ((etaleConstantSheaf.{u, v, uL} ρ R).obj M) ≫
        (etaleCompactCohomology L h R q).map
          ((etaleConstantSheafRestrictionIso.{u, v, uL} ρ R).hom.app M) := by
  simp [etaleConstantCompactComparison]

end Comparison

section Harris

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable {I : Type (max u (v + 1) uL)}
  (points : I → (etaleTopology X).Point.{max u (v + 1) uL})
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable [PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
  [PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ points R)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((etaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, v, uL} ρ points R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((etaleGSheafCompactCohomology L ρ h R n).obj
      ((etaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- The map `H^n(Γ_{c,X{G}}(G^•_m)) → H^n_c(X, R / ℓ ^ m R)` from the cohomology of Harris's
complex of level `m` for the constant system `{R / ℓ ^ m R}` and the family `points`, with the
action of `G` forgotten, to the plain compactly supported cohomology of `X` with constant
coefficients: Harris's (2.3) followed by the constant comparison. That it is an isomorphism
(Berkovich's Corollary 1.5.2(i)) is not proved. -/
def etaleConstantCompactHomologyToPlain (m n : ℕ) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    (smoothForget R G).obj
        (((etaleConstantFamilyCompactSectionsSystem.{u, v, uL} ρ points R hℓ L h hpoints D hF
          hC).obj m).homology n) ⟶
      (etaleCompactCohomology L h R n).obj
        ((constantSheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  (smoothForget R G).map
      (etaleConstantFamilyCompactHomologyIso.{u, v, uL} ρ points R hℓ L h hpoints D hF hC m
        n).hom ≫
    (etaleConstantCompactComparison L ρ h R n).app
      (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))

end Harris

end Langlands.Sheaf.Equivariant.Analytic
