import Langlands.GaloisCohomology.Global.BrauerSequence.CubicSplitting
import Langlands.GroupScheme.Rational.CentralQuadraticSplittingLift

/-! # Lifting through a mu-three kernel after a cyclic cubic extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology NumberField
open Langlands.ClassFieldTheory.Local
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Over a totally complex number field, a cocycle with central lift data for
an isogeny with kernel `μ₃` lifts after base change to a cyclic cubic field and
a finite Galois refinement over that field. -/
def TotallyComplexCubicCentralLiftStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [IsTotallyComplex F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H) (hf : IsCentralIsogeny f),
    Nonempty (kernel f ≅ splitRootsOfUnityProduct F (fun _ : PUnit.{u + 1} => 3)) →
    ∀ (ξ : Cocycle H (GaloisCocycle.cover F L)), Nonempty (hf.GaloisLift ξ) →
      ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E),
        IsGalois F E ∧ Module.finrank F E = 3 ∧
        ∃ (N : Type u) (_ : Field N) (_ : Algebra E N) (_ : FiniteDimensional E N)
          (_ : IsGalois E N) (_ : Algebra F N) (_ : IsScalarTower F E N) (_ : Algebra L N)
          (_ : IsScalarTower F L N)
          (ζ : Cocycle ((GroupScheme.baseChange (algebraBaseMap F E)).obj G)
            (GaloisCocycle.cover E N)),
          ζ.map ((GroupScheme.baseChange (algebraBaseMap F E)).map f) =
            GaloisCocycle.scalarExtension (K := E) (M := N) ξ

open IsCentralIsogeny in
theorem totallyComplexCubicCentralLift : TotallyComplexCubicCentralLiftStatement.{u} := by
  classical
  intro F L _ _ _ _ _ _ _ G H f hf ⟨e⟩ ξ ⟨d⟩
  let n (_ : PUnit.{u + 1}) : ℕ := 3
  let χ := splitRootsKernelCharacter n e PUnit.unit
  let c := hf.kernelUnitDefect χ d
  have hc : IsMulCocycle₂ c := hf.kernelUnitDefect_isMulCocycle₂ χ d
  have hpow (q : Gal(L/F) × Gal(L/F)) : c q ^ 3 = 1 := by
    change hf.kernelUnitMap χ L (d.defect q) ^ 3 = 1
    rw [← hf.kernelSplitRootsEquiv_val n e]
    exact (mem_rootsOfUnity 3 _).mp (hf.kernelSplitRootsEquiv n e L (d.defect q) PUnit.unit).property
  have hthree : 3 • relativeUnitsClass₂ c hc = 0 := by
    unfold relativeUnitsClass₂
    rw [← map_nsmul]
    refine (congrArg (ConcreteCategory.hom (H2π (unitsRepresentation F L))) ?_).trans (map_zero _)
    apply Subtype.ext
    funext q
    change (3 : ℕ) • Additive.ofMul (c q) = 0
    rw [← ofMul_pow, hpow]
    rfl
  obtain ⟨E, hE, hGalE, hdeg, M, _, _, _, _, _, _, _, _, _, _, hres⟩ :=
    GaloisCohomology.totallyComplexCubicRelativeBrauerSplitting F L (relativeUnitsClass₂ c hc) hthree
  have hu := isMulCoboundary₂_of_relativeRestriction_relativeInflation_eq_zero c hc hres
  let u : Gal(M/E) × Gal(M/E) → Mˣ := fun q => Units.map (algebraMap L M).toMonoidHom
    (c ((q.1.restrictScalars F).restrictNormal L, (q.2.restrictScalars F).restrictNormal L))
  have hupow (q : Gal(M/E) × Gal(M/E)) : u q ^ 3 = 1 := by
    simp only [u, ← map_pow, hpow, map_one]
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨N, _, _, _, _, _, _, a, ha, hprim⟩ :=
    rootsOfUnityPrimitiveAfterRefinement_of_units (F := E) (L := M) 3 (by decide) u hupow hu
  let : Algebra F N := ((algebraMap E N).comp (algebraMap F E)).toAlgebra
  let : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra L N := ((algebraMap M N).comp (algebraMap L M)).toAlgebra
  let : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap E N (algebraMap F E x) = algebraMap M N (algebraMap L M (algebraMap F L x))
    rw [← IsScalarTower.algebraMap_apply F L M, IsScalarTower.algebraMap_apply F E M,
      ← IsScalarTower.algebraMap_apply E M N]
  let d' := hf.scalarExtensionGaloisLift (K := E) (M := N) d
  let eZ := scalarExtensionKernelPointsEquiv (K := E) (M := N) (f := f)
  let ks := hf.kernelSplitRootsEquiv n e N
  let ρ (σ : N ≃ₐ[E] N) : L ≃ₐ[F] L := (σ.restrictScalars F).restrictNormal L
  let pt (σ : N ≃ₐ[E] N) :=
    eZ.symm (ks.symm (fun _ => ⟨a σ, (mem_rootsOfUnity 3 _).mpr (ha σ)⟩))
  let Φ := (hf.kernelUnitMap χ N).comp eZ.toMonoidHom
  have hΦ : Function.Injective Φ := fun x y hxy =>
    eZ.injective (hf.kernelUnitMap_splitRoots_jointly_injective n e N (fun i => by
      cases i
      exact hxy))
  have hΦp (σ : N ≃ₐ[E] N) : Φ (pt σ) = a σ := by
    change hf.kernelUnitMap χ N (eZ (eZ.symm _)) = a σ
    rw [MulEquiv.apply_symm_apply]
    exact hf.kernelUnitMap_splitRoots_symm n e N _ PUnit.unit
  have hΦact (σ : N ≃ₐ[E] N) (x) : Φ (σ • x) = σ • Φ x := by
    change hf.kernelUnitMap χ N (eZ (GaloisCocycle.arrow E N σ ≫ x)) = _
    rw [scalarExtensionKernelPointsEquiv_smul]
    exact (hf.kernelUnitMap_naturality χ (σ.restrictScalars F).toAlgHom _).trans (Units.ext rfl)
  have hΦd (σ τ : N ≃ₐ[E] N) :
      Φ (d'.defect (σ, τ)) = Units.map (algebraMap L N).toMonoidHom (c (ρ σ, ρ τ)) := by
    change hf.kernelUnitMap χ N (eZ (d'.defect (σ, τ))) = _
    rw [scalarExtensionGaloisLift_defect]
    exact hf.kernelUnitMap_naturality χ (IsScalarTower.toAlgHom F L N) _
  have hρ (σ : N ≃ₐ[E] N) : ((σ.restrictNormal M).restrictScalars F).restrictNormal L = ρ σ := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L N).injective
    have h1 := AlgEquiv.restrictNormal_commutes ((σ.restrictNormal M).restrictScalars F) L x
    have h2 := AlgEquiv.restrictNormal_commutes σ M (algebraMap L M x)
    have h3 := AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) L x
    change algebraMap M N (algebraMap L M _) = algebraMap L N ((σ.restrictScalars F).restrictNormal L x)
    rw [h1, h3]
    exact h2
  have hp : IsMulCoboundary₂ d'.defect := by
    refine ⟨pt, fun σ τ => hΦ ?_⟩
    rw [map_mul, map_div, hΦact, hΦp, hΦp, hΦp, hΦd, hprim σ τ]
    simp only [u, hρ]
    rfl
  obtain ⟨ζ, hζ⟩ := ((hf.baseChange (algebraBaseMap F E)).galoisLift_isMulCoboundary₂_iff _ d').mp hp
  exact ⟨E, hE, hGalE, hdeg, N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ζ, hζ⟩

end Langlands.GroupScheme
