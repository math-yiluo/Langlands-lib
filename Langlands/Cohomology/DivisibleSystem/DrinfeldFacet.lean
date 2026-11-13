import Langlands.Geometry.Analytic.DrinfeldFacetSpaces
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRefinements
import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant

/-!
# Harris's §2 constructions on the domains `U(f)` of Drinfeld's upper half space

For a finite set `f` of vertices of the Bruhat–Tits building and a subgroup `H` of its
stabilizer `S(f)` in `GL_{d+1}(F)`, the open domain `U(f) ⊆ Ω` carries an action of `H`
(`facetAction`). This module specializes the quasi-étale `G`-sheaf constructions of
`AnalyticQuasiEtale` and `AnalyticQuasiEtaleConstant` to this action: the finite
equivariant refinement condition, the constant `ℓ`-divisible system, Harris's Lemma 2.2
and 2.2 bis, the isomorphism (2.3) and Lemma 2.8 for the constant system on `U(f)`.
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

/-- Harris's `U(f)` as an analytic space. -/
abbrev facetSpace : LocalizedCategory.{u, u, u} (K := K) :=
  (facetAction K hS ε H hH).V

/-- The action of `H` on `U(f)` by automorphisms. -/
abbrev facetρ : H →* Aut (facetSpace K hS ε H hH) :=
  (facetAction K hS ε H hH).ρAut

/-- The space of `U(f)` is Hausdorff, as a subspace of `Ω`. -/
instance t2Space_facetSpace :
    T2Space (localizedSpaceFunctor.obj (facetSpace K hS ε H hH)) := by
  have : T2Space (presentationOf (omegaAction F K d).V).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj (omegaAction F K d).V))
  exact inferInstanceAs (T2Space (facetAnalyticDomain K hS ε).carrier)

/-- The finite equivariant refinement condition for the action of `H` on `U(f)`. It follows
from the existence half of `QuasiEtaleActionLiftStatement`, continuity of the action, finite
compact refinements on `U(f)` and compatibility of lifts on compact quasi-étale objects. -/
theorem hasFiniteEquivariantRefinements_facet
    (hKL : QuasiEtaleActionLiftStatement.{u, u, u} K)
    (hc : IsContinuousAction (facetρ K hS ε H hH))
    (hA : HasFiniteCompactQuasiEtaleRefinements (facetSpace K hS ε H hH))
    (hC : HasCompatibleCompactQuasiEtaleLifts (facetρ K hS ε H hH)) :
    (compactLiftSystem (facetρ K hS ε H hH)).HasFiniteEquivariantRefinements
      (twistedQuasiEtaleTopology (facetρ K hS ε H hH)) :=
  hasFiniteEquivariantRefinements_compactLiftSystem _ hA
    (hasCompactQuasiEtaleLifts_of_actionLiftStatement _ hKL inferInstance hc) hC

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

/-- Quasi-étale `H`-sheaves of `R`-modules on `U(f)`. -/
abbrev FacetQuasiEtaleSheaf : Type _ :=
  QuasiEtaleGSheaf (facetρ K hS ε H hH) (ModuleCat.{max u (u + 1) uL} R)

variable [(compactLiftSystem (facetρ K hS ε H hH)).HasFiniteEquivariantRefinements
    (twistedQuasiEtaleTopology (facetρ K hS ε H hH))]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj (facetSpace K hS ε H hH),
  QuasiEtaleSite.PointAxioms L x)

/-- Berkovich's `H^q_c(U(f){H}, -)` on quasi-étale `H`-sheaves of `R`-modules on `U(f)`. -/
abbrev facetCompactCohomology (q : ℕ) :
    FacetQuasiEtaleSheaf K hS ε H hH R ⥤
      SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R H :=
  quasiEtaleGSheafCompactCohomology L (facetρ K hS ε H hH) h R q


/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of quasi-étale `H`-sheaves on `U(f)`. -/
abbrev facetConstantSystem : QuasiEtaleDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  quasiEtaleConstantSystem.{u, u, uL} (facetρ K hS ε H hH) R hℓ

variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L (facetρ K hS ε H hH) h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L (facetρ K hS ε H hH) h R)]
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj
    (facetSpace K hS ε H hH) =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (u + 1) uL} R))

/-- Harris's Lemma 2.2 on `U(f)`: the `ℓ`-divisible system of the Godement resolutions of
the constant quasi-étale `H`-sheaves `R / ℓ ^ m R`. -/
abbrev facetConstantGodementResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  quasiEtaleConstantGodementResolutionSystem (facetρ K hS ε H hH) R hℓ L h hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis on `U(f)`: the truncation `τ_{≤ D+1}` of the Godement resolution
system of the constant system. -/
abbrev facetConstantGodementTruncatedResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, u, uL} (facetρ K hS ε H hH) R ℓ :=
  quasiEtaleConstantGodementTruncatedResolutionSystem (facetρ K hS ε H hH) R hℓ L h hpoints D

/-- Level `m` of the truncated resolution system on `U(f)` resolves the constant
quasi-étale `H`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_facetConstantGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
      (facetρ K hS ε H hH) R
    QuasiIso (quasiEtaleConstantGodementTruncatedAugmentation (facetρ K hS ε H hH) R hℓ L h
      hpoints D m) :=
  quasiIso_quasiEtaleConstantGodementTruncatedAugmentation (facetρ K hS ε H hH) R hℓ L h
    hpoints D m

variable (hF : ∀ (M : FacetQuasiEtaleSheaf K hS ε H hH R) (r : ℕ),
    IsZero ((facetCompactCohomology K hS ε H hH R L h (r + 1)).obj
      ((quasiEtaleGodementFunctor L (facetρ K hS ε H hH) h R).obj M)))
  (hdim : ∀ m n : ℕ, D < n →
    IsZero ((facetCompactCohomology K hS ε H hH R L h n).obj
      ((quasiEtaleConstantSheaf.{u, u, uL} (facetρ K hS ε H hH) R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- Harris's system of complexes `Γ_{c,U(f){H}}(G^•_m)` of smooth representations of `H`
for the constant sheaves `R / ℓ ^ m R` on `U(f)`. -/
abbrev facetConstantCompactSectionsSystem :
    DivisibleSystem (CochainComplex (SmoothRep.{max u (u + 1) uL, u, max u (u + 1) uL} R H) ℕ)
      ℓ :=
  quasiEtaleConstantCompactSectionsSystem (facetρ K hS ε H hH) R hℓ L h hpoints D hF hdim

/-- Harris (2.3) on `U(f)`: the cohomology of level `m` of the compact section complexes is
`H^n_c(U(f){H}, R / ℓ ^ m R)`. -/
def facetConstantCompactHomologyIso (m n : ℕ) :
    ((facetConstantCompactSectionsSystem K hS ε H hH R hℓ L h hpoints D hF hdim).obj
        m).homology n ≅
      (facetCompactCohomology K hS ε H hH R L h n).obj
        ((quasiEtaleConstantSheaf.{u, u, uL} (facetρ K hS ε H hH) R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  quasiEtaleConstantCompactHomologyIso (facetρ K hS ε H hH) R hℓ L h hpoints D hF hdim m n

variable {ι : Type u} [Preorder ι] (N : ι → Subgroup H) (hN : Antitone N)
  [∀ i, (N i).Normal] [∀ i, (N i).FiniteIndex] [∀ i, Fintype (H ⧸ N i)]
  [∀ i, DecidableEq (H ⧸ N i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (N i)).map
      (((facetConstantCompactSectionsSystem K hS ε H hH R hℓ L h hpoints D hF hdim).projection
        hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hN hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim_m C^•_m` on `U(f)` for the constant system, built from the subgroups
`N i` of `H`. -/
abbrev facetConstantQuotientInvariantsInverseLimit :
    CochainComplex (Rep.{max u (u + 1) uL} R H) ℤ :=
  quasiEtaleGodementQuotientInvariantsInverseLimit (facetρ K hS ε H hH) R L h
    (facetConstantSystem K hS ε H hH R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj (facetρ K hS ε H hH) R hℓ L h
      D hdim) N hN hK hk

set_option synthInstance.maxHeartbeats 60000 in
/-- Harris's Lemma 2.8 on `U(f)` for the constant system: under the hypotheses of the general
quasi-étale version, the degree-`n` cohomology of `lim_m C^•_m` is the inverse limit over `m`
of `H^n_c(U(f){H}, R / ℓ ^ m R)` (level `m` of the constant system). -/
def facetConstantQuotientInvariantsInverseLimitHomologyIso
    (hPro : ProPInvariantSubcomplexStatement.{u, max u (u + 1) uL, max u (u + 1) uL})
    (hLim : FiniteCohomologyInverseLimitStatement.{max u (u + 1) uL, max u (u + 1) uL} R)
    {p : ℕ} (hP : ∀ i, IsProPSubgroup p (N i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : N i),
      haveI := twistedQuasiEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      (SmoothRep.toRep.obj ((facetCompactCohomology K hS ε H hH R L h q).obj
        ((facetConstantSystem K hS ε H hH R hℓ).obj m))).ρ g = LinearMap.id)
    (hfin : ∀ m q,
      haveI := twistedQuasiEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      Finite (SmoothRep.toRep.obj ((facetCompactCohomology K hS ε H hH R L h q).obj
        ((facetConstantSystem K hS ε H hH R hℓ).obj m))))
    (n : ℕ) :
    (facetConstantQuotientInvariantsInverseLimit K hS ε H hH R hℓ L h hpoints D hF hdim N hN hK
      hk).homology n ≅
      haveI := twistedQuasiEtale_hasSheafify.{u, u, uL} (facetSpace K hS ε H hH)
        (facetρ K hS ε H hH) R
      limit ((facetConstantSystem K hS ε H hH R hℓ).tower ⋙
        quasiEtaleGSheafCompactCohomology L (facetρ K hS ε H hH) h R n ⋙ SmoothRep.toRep) :=
  quasiEtaleGodementQuotientInvariantsInverseLimitHomologyIso (facetρ K hS ε H hH) R L h
    (facetConstantSystem K hS ε H hH R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj (facetρ K hS ε H hH) R hℓ L h
      D hdim) N hN hK hk hPro hLim hP hR htriv hfin n

end Facet

end Langlands.Cohomology.DivisibleSystem.Analytic
