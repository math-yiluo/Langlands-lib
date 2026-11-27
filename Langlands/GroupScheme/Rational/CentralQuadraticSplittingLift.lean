import Langlands.GroupScheme.Rational.CentralSplitTorsionCocycleLift
import Langlands.GroupScheme.CentralIsogeny.GaloisLiftScalarExtension
import Langlands.GaloisCohomology.Global.BrauerSequence.QuadraticComplexSplitting

/-! # Lifting through a `μ_2` kernel after a totally complex quadratic extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace IsCentralIsogeny

open Langlands.ClassFieldTheory.Local

variable {F : Type u} [Field F] {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

section KernelPoints

variable {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
  [IsScalarTower F K M]

/-- The comparison of kernel points after scalar extension intertwines the Galois actions. -/
theorem scalarExtensionKernelPointsEquiv_smul (σ : M ≃ₐ[K] M)
    (x : GaloisCocycle.cover K M ⟶
      (kernel ((GroupScheme.baseChange (Spec.algebraMap F K)).map f)).X) :
    scalarExtensionKernelPointsEquiv (f := f) (GaloisCocycle.arrow K M σ ≫ x) =
      GaloisPoint.relativeConjugate F K M (kernel f) σ
        (scalarExtensionKernelPointsEquiv (f := f) x) := by
  rw [scalarExtensionKernelPointsEquiv_apply, scalarExtensionKernelPointsEquiv_apply,
    Category.assoc]
  exact GaloisCocycle.scalarExtensionPointsEquiv_conjugate _ σ

end KernelPoints

end IsCentralIsogeny

section Classes

open Langlands.ClassFieldTheory.Local

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {E M : Type u} [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M] [Algebra L M] [IsScalarTower F L M]

omit [FiniteDimensional F L] in
/-- If the restriction to `E` of the inflation to `M` of the class of a unit two-cocycle of
`L/F` vanishes, the cocycle, restricted and inflated to `Gal(M/E)`, is a coboundary. -/
theorem isMulCoboundary₂_of_relativeRestriction_relativeInflation_eq_zero
    (c : Gal(L/F) × Gal(L/F) → Lˣ) (hc : IsMulCocycle₂ c)
    (h : relativeRestriction F E M 2 (relativeInflation F L M 2 (relativeUnitsClass₂ c hc)) = 0) :
    IsMulCoboundary₂ (fun q : Gal(M/E) × Gal(M/E) => Units.map (algebraMap L M).toMonoidHom
      (c ((q.1.restrictScalars F).restrictNormal L, (q.2.restrictScalars F).restrictNormal L))) := by
  unfold relativeUnitsClass₂ at h
  rw [H2π_comp_map_apply, H2π_comp_map_apply] at h
  obtain ⟨a, ha⟩ := (H2π_eq_zero_iff _).mp h
  refine ⟨fun σ => (a σ).toMul, fun σ τ => ?_⟩
  have hστ := congrArg (fun q => (q (σ, τ)).toMul) ha
  rw [d₁₂_hom_apply] at hστ
  exact hστ

omit [FiniteDimensional F L] [IsGalois F L] in
/-- A unit two-cocycle with values of order dividing two has a relative class killed by two. -/
theorem two_nsmul_relativeUnitsClass₂ (c : Gal(L/F) × Gal(L/F) → Lˣ) (hc : IsMulCocycle₂ c)
    (h2 : ∀ q, c q ^ 2 = 1) : 2 • relativeUnitsClass₂ c hc = 0 := by
  unfold relativeUnitsClass₂
  rw [← map_nsmul]
  refine (congrArg (ConcreteCategory.hom (H2π (unitsRepresentation F L))) ?_).trans (map_zero _)
  apply Subtype.ext
  funext q
  change (2 : ℕ) • Additive.ofMul (c q) = 0
  rw [← ofMul_pow, h2 q]
  rfl

end Classes

namespace IsCentralIsogeny

section Quadratic

variable {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [IsGalois F L] {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f) (e : kernel f ≅ splitRootsOfUnityProduct F (fun _ : PUnit.{u + 1} => (2 : ℕ)))

set_option maxHeartbeats 1600000 in
include e in
/-- Let `f` be a central isogeny over a number field `F` whose kernel is `μ_2`, and let a cocycle
of the target on a finite Galois cover `L/F` have central lift data. Then over some totally
complex quadratic extension `E` of `F` inside the separable closure, its scalar extension to a
finite Galois extension `N/E` containing `L` lifts to a cocycle of the base-changed source. -/
theorem exists_quadratic_isComplex_lift_of_galoisLift {ξ : Cocycle H (GaloisCocycle.cover F L)}
    (d : hf.GaloisLift ξ) :
    ∃ E : IntermediateField F (SeparableClosure F), Module.finrank F E = 2 ∧
      (∀ w : NumberField.InfinitePlace E, w.IsComplex) ∧
      ∃ (N : Type u) (_ : Field N) (_ : Algebra E N) (_ : FiniteDimensional E N)
        (_ : IsGalois E N) (_ : Algebra F N) (_ : IsScalarTower F E N) (_ : Algebra L N)
        (_ : IsScalarTower F L N)
        (ζ : Cocycle ((GroupScheme.baseChange (Spec.algebraMap F E)).obj G)
          (GaloisCocycle.cover E N)),
        ζ.map ((GroupScheme.baseChange (Spec.algebraMap F E)).map f) =
          GaloisCocycle.scalarExtension (K := E) (M := N) ξ := by
  classical
  let χ := splitRootsKernelCharacter (fun _ : PUnit.{u + 1} => (2 : ℕ)) e PUnit.unit
  let c := hf.kernelUnitDefect χ d
  have hc : IsMulCocycle₂ c := hf.kernelUnitDefect_isMulCocycle₂ χ d
  have hpow (q : Gal(L/F) × Gal(L/F)) : c q ^ 2 = 1 := by
    change hf.kernelUnitMap χ L (d.defect q) ^ 2 = 1
    rw [← hf.kernelSplitRootsEquiv_val (fun _ : PUnit.{u + 1} => (2 : ℕ)) e]
    exact (mem_rootsOfUnity 2 _).mp
      (hf.kernelSplitRootsEquiv (fun _ : PUnit.{u + 1} => (2 : ℕ)) e L (d.defect q) PUnit.unit).property
  obtain ⟨E, hE2, hEc, M, _, _, _, _, _, _, _, _, _, _, hres⟩ :=
    GaloisCohomology.exists_quadratic_isComplex_relativeRestriction_eq_zero
      (relativeUnitsClass₂ c hc) (two_nsmul_relativeUnitsClass₂ c hc hpow)
  have hu := isMulCoboundary₂_of_relativeRestriction_relativeInflation_eq_zero c hc hres
  let u : Gal(M/E) × Gal(M/E) → Mˣ := fun q => Units.map (algebraMap L M).toMonoidHom
    (c ((q.1.restrictScalars F).restrictNormal L, (q.2.restrictScalars F).restrictNormal L))
  have hupow (q : Gal(M/E) × Gal(M/E)) : u q ^ 2 = 1 := by
    simp only [u, ← map_pow, hpow, map_one]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨N, _, _, _, _, _, _, a, ha, hprim⟩ :=
    rootsOfUnityPrimitiveAfterRefinement_of_units (F := E) (L := M) 2 two_ne_zero u hupow hu
  let : Algebra F N := ((algebraMap E N).comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq fun x => rfl
  let : Algebra L N := ((algebraMap M N).comp (algebraMap L M)).toAlgebra
  have : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap E N (algebraMap F E x) = algebraMap M N (algebraMap L M (algebraMap F L x))
    rw [← IsScalarTower.algebraMap_apply F L M, IsScalarTower.algebraMap_apply F E M,
      ← IsScalarTower.algebraMap_apply E M N]
  let d' := hf.scalarExtensionGaloisLift (K := E) (M := N) d
  let eZ := scalarExtensionKernelPointsEquiv (K := E) (M := N) (f := f)
  let ks := hf.kernelSplitRootsEquiv (fun _ : PUnit.{u + 1} => (2 : ℕ)) e N
  let ρ (σ : N ≃ₐ[E] N) : L ≃ₐ[F] L := (σ.restrictScalars F).restrictNormal L
  let pt (σ : N ≃ₐ[E] N) :=
    eZ.symm (ks.symm (fun _ => ⟨a σ, (mem_rootsOfUnity 2 _).mpr (ha σ)⟩))
  let Φ := (hf.kernelUnitMap χ N).comp eZ.toMonoidHom
  have hΦ : Function.Injective Φ := fun x y hxy =>
    eZ.injective (hf.kernelUnitMap_splitRoots_jointly_injective (fun _ : PUnit.{u + 1} => (2 : ℕ)) e N (fun i => by
      cases i
      exact hxy))
  have hΦp (σ : N ≃ₐ[E] N) : Φ (pt σ) = a σ := by
    change hf.kernelUnitMap χ N (eZ (eZ.symm _)) = a σ
    rw [MulEquiv.apply_symm_apply]
    exact hf.kernelUnitMap_splitRoots_symm (fun _ : PUnit.{u + 1} => (2 : ℕ)) e N _ PUnit.unit
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
  obtain ⟨ζ, hζ⟩ := ((hf.baseChange (Spec.algebraMap F E)).galoisLift_isMulCoboundary₂_iff _ d').mp hp
  exact ⟨E, hE2, hEc, N, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ζ, hζ⟩

end Quadratic

end IsCentralIsogeny

end Langlands.GroupScheme
