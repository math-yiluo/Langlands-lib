import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof
import Langlands.GroupScheme.CentralIsogeny.GaloisDefectLocalPrimitive
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Rational.CentralRootsOfUnityCohomology

/-! # Finite-place vanishing of the unit-valued central defect -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality FundamentalClass
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

set_option backward.isDefEq.respectTransparency false

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (χ : kernel f ⟶ (GroupScheme.Gm (Spec (CommRingCat.of F))).toGrp)

/-- A character of the actual kernel gives a unit on each coefficient point. -/
def kernelUnitMap (A : Type u) [CommRing A] [Algebra F A] :
    GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F A) →* Aˣ :=
  (Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F A)).toMonoidHom.comp
    (GroupScheme.affinePointsTarget hf.commutativeKernel.toGrp χ (CommAlgCat.of F A))

/-- Kernel character values commute with extension of coefficient algebras. -/
theorem kernelUnitMap_naturality {A B : Type u} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (j : A →ₐ[F] B)
    (x : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F A)) :
    hf.kernelUnitMap χ B
        (GroupScheme.affinePointMap hf.commutativeKernel.toGrp (CommAlgCat.ofHom j) x) =
      Units.map j.toRingHom (hf.kernelUnitMap χ A x) := by
  let g := hf.commutativeKernel.toGrp
  let R := CommRingCat.of F
  let t := CommAlgCat.ofHom j
  let S := (GroupScheme.Gm (Spec R)).toGrp
  change Gm.affineUnitsEquiv R (CommAlgCat.of F B)
      (GroupScheme.affinePointsTarget g χ (CommAlgCat.of F B) (GroupScheme.affinePointMap g t x)) = _
  have h := DFunLike.congr_fun (GroupScheme.affinePointsTarget_naturality g (H := S) χ t) x
  change GroupScheme.affinePointMap S t (GroupScheme.affinePointsTarget g χ (CommAlgCat.of F A) x) =
    GroupScheme.affinePointsTarget g χ (CommAlgCat.of F B) (GroupScheme.affinePointMap g t x) at h
  rw [← h]
  exact Gm.affineUnitsEquiv_naturality R t _

variable {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)

/-- Evaluation of the central two-cocycle by a character of the kernel. -/
def kernelUnitDefect : (L ≃ₐ[F] L) × (L ≃ₐ[F] L) → Lˣ :=
  fun q => hf.kernelUnitMap χ L (d.defect q)

theorem kernelUnitDefect_isMulCocycle₂ : IsMulCocycle₂ (hf.kernelUnitDefect χ d) := by
  intro σ τ υ
  have h := congrArg (hf.kernelUnitMap χ L) (hf.galoisLift_isMulCocycle₂ ξ d σ τ υ)
  have hs : hf.kernelUnitMap χ L (σ • d.defect (τ, υ)) =
      σ • hf.kernelUnitMap χ L (d.defect (τ, υ)) :=
    hf.kernelUnitMap_naturality χ σ.toAlgHom (d.defect (τ, υ))
  simpa only [kernelUnitDefect, map_mul, hs] using h

/-- The relative unit class given by a central defect and a character of the kernel. -/
def kernelUnitObstruction : relativeCohomology F L 2 :=
  relativeUnitsClass₂ (hf.kernelUnitDefect χ d) (hf.kernelUnitDefect_isMulCocycle₂ χ d)

variable [NumberField F] [NumberField L] [IsGalois F L]

/-- A trivialization at a finite completion kills the unit-valued central defect at every
place above it, as a class over the original local coefficient extension. -/
theorem unitsLocalMap_kernelUnitObstruction_eq_zero
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (h : let b := Spec.algebraMap F (v.adicCompletion F)
      (ξ.baseChange b ((Over.pullback b).obj (GaloisCocycle.cover F L))
        ((Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L))).IsTrivial) :
    unitsLocalMap v w 2 (hf.kernelUnitObstruction χ d) = 0 := by
  let K := v.adicCompletion F
  let M := w.adicCompletion L
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let : FiniteDimensional K M := FiniteExtension.local_finite v w
  let : IsGalois K M := isGalois_adicCompletion v w
  obtain ⟨N, _, _, _, _, _, _, _, _, _, _, _, _, a, ha⟩ :=
    hf.exists_primitive_of_baseChange_isTrivial (K := K) (M := M) ξ d h
  apply (finiteRelativeH2InflationExactness K M N).1
  rw [map_zero]
  change (unitsLocalMap v w 2 ≫ relativeInflation K M N 2) (hf.kernelUnitObstruction χ d) = 0
  rw [← groupCohomology.map_comp, ← map_zero (H2π (unitsRepresentation K N)).hom]
  apply (map_H2π_eq_H2π_iff _ _ _ _).mpr
  refine ⟨fun σ => Additive.ofMul (hf.kernelUnitMap χ N (a σ)), fun σ τ => ?_⟩
  have hres (ρ : N ≃ₐ[K] N) :
      decompositionHom v w (ρ.restrictNormal M) = (ρ.restrictScalars F).restrictNormal L := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L N).injective
    calc
      _ = algebraMap M N (algebraMap L M (decompositionHom v w (ρ.restrictNormal M) x)) :=
        IsScalarTower.algebraMap_apply L M N _
      _ = algebraMap M N ((ρ.restrictNormal M) (algebraMap L M x)) :=
        congrArg (algebraMap M N) (algebraMap_decompositionHom v w (ρ.restrictNormal M) x)
      _ = ρ (algebraMap M N (algebraMap L M x)) := ρ.restrictNormal_commutes M _
      _ = _ := by
        rw [← IsScalarTower.algebraMap_apply L M N]
        exact ((ρ.restrictScalars F).restrictNormal_commutes L x).symm
  let c := hf.kernelUnitDefect χ d
  let b (ρ : N ≃ₐ[K] N) := hf.kernelUnitMap χ N (a ρ)
  have hb : σ • b τ / b (σ * τ) * b σ =
      Units.map (algebraMap L N) (c ((σ.restrictScalars F).restrictNormal L,
        (τ.restrictScalars F).restrictNormal L)) := by
    have hσ := congrArg (hf.kernelUnitMap χ N) (ha σ τ)
    have he : hf.kernelUnitMap χ N (GaloisPoint.relativeConjugate F K N hf.commutativeKernel.toGrp σ
        (a τ)) = σ • b τ := hf.kernelUnitMap_naturality χ (σ.restrictScalars F).toAlgHom _
    have hu (x : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F L)) :
        hf.kernelUnitMap χ N (GaloisPoint.relativeExtend F L N hf.commutativeKernel.toGrp x) =
          Units.map (algebraMap L N) (hf.kernelUnitMap χ L x) :=
      hf.kernelUnitMap_naturality χ (IsScalarTower.toAlgHom F L N) x
    simpa only [b, c, kernelUnitDefect, map_mul, map_div, he, hu] using hσ
  change Additive.ofMul
        (Units.map (algebraMap M N).toMonoidHom (Units.map (algebraMap L M).toMonoidHom
          (c (decompositionHom v w (σ.restrictNormal M), decompositionHom v w (τ.restrictNormal M))))) +
      Additive.ofMul (b (σ * τ)) = Additive.ofMul (b σ) + Additive.ofMul (σ • b τ) + 0
  rw [add_zero, hres, hres]
  have hcomp (x : Lˣ) : Units.map (algebraMap M N).toMonoidHom (Units.map (algebraMap L M).toMonoidHom x) =
      Units.map (algebraMap L N) x :=
    Units.ext ((IsScalarTower.algebraMap_apply L M N (x : L)).symm)
  rw [hcomp, ← hb]
  change Additive.ofMul ((σ • b τ / b (σ * τ) * b σ) * b (σ * τ)) =
    Additive.ofMul (b σ * σ • b τ)
  congr 1
  rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm]

end Langlands.GroupScheme.IsCentralIsogeny
