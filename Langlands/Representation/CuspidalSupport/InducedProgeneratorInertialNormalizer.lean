import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Representation.CuspidalSupport.NormKernelSummandPullback
import Langlands.Representation.Exponents.LeviInductionConjugation
import Langlands.Representation.Geometric.MaximalLeviOppositeNormalizer

/-! # Induced progenerators when a Levi normalizer fixes the inertial class -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport Plancherel

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N Q U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inertialNormalizerAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 800000 in
/-- An inertial normalizer outside the common Levi conjugates the two distinct parabolics
of a maximal opposite pair. Its inverse point map fixes the isomorphism class of the
norm-kernel summand induction, so conjugating gives an isomorphism of the two inductions. -/
def inducedProgeneratorIso_of_inertialNormalizer
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hlevi : lQ ≫ q = l ≫ p)
    (hinf : SubgroupFunctor.range p ⊓ SubgroupFunctor.range q = SubgroupFunctor.range (l ≫ p))
    (hproper : ¬ IsIso p)
    (hmax : ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (j : R ⟶ G) (f : P ⟶ R),
      IsParabolicSubgroup j → f ≫ j = p → IsIso f ∨ IsIso j)
    (hne : SubgroupFunctor.range p ≠ SubgroupFunctor.range q)
    (g : rationalPoints G) (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom)
    (hg : g ∉ pointImage (l ≫ p)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI := leviPointTopology l hl
    ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (_ : π.IsIrreducible)
      (ρ₀ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel M)) (_ : ρ₀.IsIrreducible)
      (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel M) π)
      (_ : Function.Injective (SmoothRep.hom j))
      (χ : unramifiedCharacters
        (fun χ : rationalCharacters M => (rationalNormCharacters M χ).toMul))
      (T : π ≃ₗ[ℂ] π),
      (∀ (m : rationalPoints M) (x : π),
        T (π.representation m x) =
          (((χ : rationalPoints M →ₜ* ℂˣ) (rationalPoints.map φ.hom m) : ℂˣ) : ℂ) •
            π.representation (rationalPoints.map φ.hom m) (T x)) →
      ((leviInductionFunctor p l r hp hr hl hmul).obj (rationalNormKernelSummandInduction M ρ₀) ≅
        (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
          (rationalNormKernelSummandInduction M ρ₀)) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  letI := leviPointTopology l hl
  letI : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ hρ₀ j hj χ T hT
  have hs := (range_swap_or_mem_levi_of_normalizes hG hp hl hq hlQ hlevi hinf hproper hmax
    hne g φ hφ).resolve_right hg
  let e := ambientIsoPointsEquiv φ.symm
  have hcomp (m : rationalPoints M) : rationalPoints.map φ.hom (e m) = m := by
    change ambientIsoPointsEquiv φ ((ambientIsoPointsEquiv φ).symm m) = m
    exact (ambientIsoPointsEquiv φ).apply_symm_apply m
  have he (m : rationalPoints M) : e m ∈ rationalCommonNormKernel M ↔
      m ∈ rationalCommonNormKernel M :=
    Geometry.Building.ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff φ.symm m
  let hχ := unramifiedCharacter_isOpen_ker _ χ
  let E : SmoothRep.pullback e π ≅ π.twist χ.val.toMonoidHom hχ :=
    SmoothRep.mkIso (Representation.Equiv.mk T (fun m => LinearMap.ext fun x => by
      change T (π.representation (e m) x) =
        ((χ.val m : ℂˣ) : ℂ) • π.representation m (T x)
      simpa only [hcomp] using hT (e m) x))
  let A := rationalNormKernelSummandInduction M ρ₀
  let ψ := (nonempty_pullback_rationalNormKernelSummandInduction_iso M hl.isConnectedReductive
    e he π hπ ρ₀ hρ₀ j hj χ hχ E).some
  have hqcomp : lQ ≫ q = φ.symm.hom ≫ l ≫ p ≫ (G.innerIso g).hom := by
    rw [hlevi, ← hφ, Iso.symm_hom, Iso.inv_hom_id_assoc]
  exact leviInductionIsoOfConj p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    g φ.symm hs.1.symm hqcomp A ≪≫ (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).mapIso ψ

end Langlands.Aubert.General.RepresentedParabolic
