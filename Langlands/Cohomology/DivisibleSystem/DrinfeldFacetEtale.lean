import Langlands.Cohomology.DivisibleSystem.DrinfeldFacet
import Langlands.Cohomology.DivisibleSystem.AnalyticEtaleConstant
import Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements

/-!
# Harris's §2 constructions for étale sheaves on the domains `U(f)`

For a finite set `f` of vertices of the Bruhat–Tits building and a subgroup `H` of its
stabilizer `S(f)` in `GL_{d+1}(F)`, the open domain `U(f) ⊆ Ω` carries an action of `H`
(`facetAction`, used through `facetSpace` and `facetρ` of `DrinfeldFacet`). This module
specializes the étale `G`-sheaf constructions of `AnalyticEtaleRefinements`,
`DivisibleSystem.AnalyticEtale` and `DivisibleSystem.AnalyticEtaleConstant` to this action:
the admissible refinement condition, the constant `ℓ`-divisible system of étale `H`-sheaves,
Harris's Lemma 2.2 and 2.2 bis, the isomorphism (2.3), Lemma 2.8, and the map from the
cohomology of Harris's complexes to the plain compactly supported étale cohomology of `U(f)`.
The Godement resolutions use an arbitrary family of points of the étale site of `U(f)`.
-/

noncomputable section

universe u uL

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

open CategoryTheory SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

variable {F : Type u} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ} [NeZero d]
  {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
  (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)

/-- The admissible refinement condition of the étale `H`-sheaves on `U(f)`. It follows from
the existence of distinguished étale neighbourhoods on `U(f)`, of lifts of the action to
distinguished étale objects, and of their compatibility (`AnalyticEtaleRefinements`). -/
theorem hasAdmissibleRefinements_facet
    (hA : HasDistinguishedEtaleNeighbourhoods (facetSpace K hS ε H hH))
    (hB : HasDistinguishedEtaleLifts (facetρ K hS ε H hH))
    (hC : HasCompatibleDistinguishedEtaleLifts (facetρ K hS ε H hH)) :
    (distinguishedLiftSystem (facetρ K hS ε H hH)).HasAdmissibleRefinements
      (twistedEtaleTopology (facetρ K hS ε H hH)) :=
  hasAdmissibleRefinements_distinguishedLiftSystem _ hA hB hC

end Langlands.Analytic.DrinfeldUpperHalfSpace

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Analytic.DrinfeldUpperHalfSpace
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf.Equivariant.Analytic

section Facet

variable {F : Type u} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ} [NeZero d]
  {S : Set (NormClass F (Fin (d + 1) → F))} (hS : S.Finite) (ε : ℝ)
  (H : Subgroup (Matrix.GeneralLinearGroup (Fin (d + 1)) F)) (hH : H ≤ facetStabilizer S)
variable (R : Type (max u (u + 1) uL)) [CommRing R]

/-- Étale `H`-sheaves of `R`-modules on `U(f)`. -/
abbrev FacetEtaleSheaf : Type _ :=
  EtaleGSheaf (facetρ K hS ε H hH) (ModuleCat.{max u (u + 1) uL} R)

variable [(distinguishedLiftSystem (facetρ K hS ε H hH)).HasAdmissibleRefinements
    (twistedEtaleTopology (facetρ K hS ε H hH))]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj (facetSpace K hS ε H hH),
  EtaleSite.PointAxioms L x)

/-- Berkovich's `H^q_c(U(f){H}, -)` on étale `H`-sheaves of `R`-modules on `U(f)`. -/
abbrev facetEtaleCompactCohomology (q : ℕ) :
    FacetEtaleSheaf K hS ε H hH R ⥤
      SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R H :=
  etaleGSheafCompactCohomology L (facetρ K hS ε H hH) h R q

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of étale `H`-sheaves on `U(f)`. -/
abbrev facetEtaleConstantSystem : EtaleDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  etaleConstantSystem.{u, u, uL} (facetρ K hS ε H hH) R hℓ

variable {I : Type (max u (u + 1) uL)}
  (points : I → (etaleTopology (facetSpace K hS ε H hH)).Point.{max u (u + 1) uL})
variable [PreservesFiniteLimits
    (etaleFamilyGodementFunctor.{u, u, uL} (facetρ K hS ε H hH) points R)]
  [PreservesFiniteColimits
    (etaleFamilyGodementFunctor.{u, u, uL} (facetρ K hS ε H hH) points R)]
variable (hpoints : JointlyFaithful fun i => (points i).sheafFiber
  (A := ModuleCat.{max u (u + 1) uL} R))

/-- Harris's Lemma 2.2 on `U(f)` for étale sheaves: the `ℓ`-divisible system of the Godement
resolutions of the constant étale `H`-sheaves `R / ℓ ^ m R`, for the family `points`. -/
abbrev facetEtaleConstantGodementResolutionSystem :
    EtaleComplexDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  etaleConstantFamilyGodementResolutionSystem.{u, u, uL} (facetρ K hS ε H hH) points R hℓ
    hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis on `U(f)` for étale sheaves: the truncation `τ_{≤ D+1}` of the
Godement resolution system of the constant system. -/
abbrev facetEtaleConstantGodementTruncatedResolutionSystem :
    EtaleComplexDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  etaleConstantFamilyGodementTruncatedResolutionSystem.{u, u, uL} (facetρ K hS ε H hH) points R
    hℓ hpoints D

/-- Level `m` of the truncated resolution system on `U(f)` resolves the constant étale
`H`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_facetEtaleConstantGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
      (facetρ K hS ε H hH) R
    QuasiIso (etaleConstantFamilyGodementTruncatedAugmentation.{u, u, uL} (facetρ K hS ε H hH)
      points R hℓ hpoints D m) :=
  quasiIso_etaleConstantFamilyGodementTruncatedAugmentation (facetρ K hS ε H hH) points R hℓ
    hpoints D m

variable (hF : ∀ (M : FacetEtaleSheaf K hS ε H hH R) (r : ℕ),
    IsZero ((facetEtaleCompactCohomology K hS ε H hH R L h (r + 1)).obj
      ((etaleFamilyGodementFunctor.{u, u, uL} (facetρ K hS ε H hH) points R).obj M)))
  (hdim : ∀ m n : ℕ, D < n →
    IsZero ((facetEtaleCompactCohomology K hS ε H hH R L h n).obj
      ((etaleConstantSheaf.{u, u, uL} (facetρ K hS ε H hH) R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- Harris's system of complexes `Γ_{c,U(f){H}}(G^•_m)` of smooth representations of `H`
for the constant étale sheaves `R / ℓ ^ m R` on `U(f)`. -/
abbrev facetEtaleConstantCompactSectionsSystem :
    DivisibleSystem (CochainComplex (SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R H) ℕ)
      ℓ :=
  etaleConstantFamilyCompactSectionsSystem.{u, u, uL} (facetρ K hS ε H hH) points R hℓ L h
    hpoints D hF hdim

/-- Harris (2.3) on `U(f)` for étale sheaves: the cohomology of level `m` of the compact
section complexes is `H^n_c(U(f){H}, R / ℓ ^ m R)`. -/
def facetEtaleConstantCompactHomologyIso (m n : ℕ) :
    ((facetEtaleConstantCompactSectionsSystem K hS ε H hH R hℓ L h points hpoints D hF
      hdim).obj m).homology n ≅
      (facetEtaleCompactCohomology K hS ε H hH R L h n).obj
        ((etaleConstantSheaf.{u, u, uL} (facetρ K hS ε H hH) R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  etaleConstantFamilyCompactHomologyIso.{u, u, uL} (facetρ K hS ε H hH) points R hℓ L h hpoints
    D hF hdim m n

/-- The map `H^n(Γ_{c,U(f){H}}(G^•_m)) → H^n_c(U(f), R / ℓ ^ m R)` from the cohomology of
Harris's complex of level `m`, with the action of `H` forgotten, to the plain compactly
supported étale cohomology of `U(f)` with constant coefficients. That it is an isomorphism is
not proved. -/
abbrev facetEtaleConstantCompactHomologyToPlain (m n : ℕ) :
    haveI := etale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH) R
    (smoothForget R H).obj
        (((facetEtaleConstantCompactSectionsSystem K hS ε H hH R hℓ L h points hpoints D hF
          hdim).obj m).homology n) ⟶
      (etaleCompactCohomology L h R n).obj
        ((constantSheaf (etaleTopology (facetSpace K hS ε H hH))
          (ModuleCat.{max u (u + 1) uL} R)).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  etaleConstantCompactHomologyToPlain.{u, u, uL} (facetρ K hS ε H hH) points R hℓ L h hpoints D
    hF hdim m n

variable {ι : Type u} [Preorder ι] (N : ι → Subgroup H) (hN : Antitone N)
  [∀ i, (N i).Normal] [∀ i, (N i).FiniteIndex] [∀ i, Fintype (H ⧸ N i)]
  [∀ i, DecidableEq (H ⧸ N i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (N i)).map
      (((facetEtaleConstantCompactSectionsSystem K hS ε H hH R hℓ L h points hpoints D hF
        hdim).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hN hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim_m C^•_m` on `U(f)` for the constant étale system, built from the subgroups
`N i` of `H`. -/
abbrev facetEtaleConstantQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (u + 1) uL} R H) ℤ :=
  etaleConstantFamilyQuotientInvariantsInverseLimit.{u, u, uL} (facetρ K hS ε H hH) points R hℓ
    L h hpoints D hF hdim N hN hK hk

set_option synthInstance.maxHeartbeats 60000 in
/-- Harris's Lemma 2.8 on `U(f)` for the constant étale system: under the hypotheses of the
general étale version, the degree-`n` cohomology of `lim_m C^•_m` is the inverse limit over
`m` of `H^n_c(U(f){H}, R / ℓ ^ m R)` (level `m` of the constant system). -/
def facetEtaleConstantQuotientInvariantsInverseLimitHomologyIso
    (hPro : ProPInvariantSubcomplexStatement.{u, max u (u + 1) uL, max u (u + 1) uL})
    (hLim : FiniteCohomologyInverseLimitStatement.{max u (u + 1) uL, max u (u + 1) uL} R)
    {p : ℕ} (hP : ∀ i, IsProPSubgroup p (N i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : N i),
      haveI := twistedEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      (SmoothRep.toRep.obj ((facetEtaleCompactCohomology K hS ε H hH R L h q).obj
        ((facetEtaleConstantSystem K hS ε H hH R hℓ).obj m))).ρ g = LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      Finite (SmoothRep.toRep.obj ((facetEtaleCompactCohomology K hS ε H hH R L h q).obj
        ((facetEtaleConstantSystem K hS ε H hH R hℓ).obj m))))
    (n : ℕ) :
    (facetEtaleConstantQuotientInvariantsInverseLimit K hS ε H hH R hℓ L h points hpoints D hF
      hdim N hN hK hk).homology n ≅
      haveI := twistedEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      limit ((facetEtaleConstantSystem K hS ε H hH R hℓ).tower ⋙
        etaleGSheafCompactCohomology L (facetρ K hS ε H hH) h R n ⋙ SmoothRep.toRep) :=
  etaleConstantFamilyQuotientInvariantsInverseLimitHomologyIso.{u, u, uL} (facetρ K hS ε H hH)
    points R hℓ L h hpoints D hF hdim N hN hK hk hPro hLim hP hR htriv hfin n

end Facet

end Langlands.Cohomology.DivisibleSystem.Analytic
