import Langlands.GroupScheme.Rational.CentralMuCocycleLift
import Langlands.GroupScheme.Rational.KummerCocycleUnits
import Langlands.GroupScheme.GaloisCocycleScalarExtension
import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.TensorCore

/-! # Local Kummer corrections for a central isogeny with roots-of-unity kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open GaloisPoint

set_option backward.isDefEq.respectTransparency false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

include hf in
/-- A central isogeny is surjective on points over an algebraically closed coefficient field. -/
theorem exists_coeffPoint_lift_of_isAlgClosed [IsAlgClosed M]
    (a : H.affinePoints (CommAlgCat.of F M)) :
    ∃ x : G.affinePoints (CommAlgCat.of F M), x ≫ f.hom.hom = a := by
  let b := Spec.algebraMap F M
  let p := (GroupScheme.baseChange b).map f
  have hp : IsCentralIsogeny p := hf.baseChange b
  let : Surjective p.hom.hom.left := hp.surjective
  let : IsFinite p.hom.hom.left := hp.isFinite
  let y := (baseChangeBasePointsEquiv b H).symm a
  obtain ⟨z, hz⟩ := SemisimpleIdentityComponent.exists_rationalPoint_lift p.hom.hom y
  refine ⟨baseChangeBasePointsEquiv b G z, ?_⟩
  rw [← baseChangeBasePointsEquiv_comp, hz, MulEquiv.apply_symm_apply]

variable [Normal F L]

/-- A local Kummer correction records a cochain, the resulting kernel coefficients and
the unit whose radical gives them. -/
structure LocalKummerCorrection (n : ℕ)
    (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    (ζ : Cocycle G (GaloisCocycle.cover F L)) where
  /-- The correcting unit of the new base field. -/
  scalar : Kˣ
  /-- The radical in the chosen local coefficient field. -/
  radical : Mˣ
  radical_pow : radical ^ n = Units.map (algebraMap K M) scalar
  /-- The cochain in the source group. -/
  cochain : G.affinePoints (CommAlgCat.of F M)
  /-- Kernel coefficients of the twisted source cocycle. -/
  correction : (M ≃ₐ[K] M) → GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M)
  correction_spec : ∀ σ : M ≃ₐ[K] M, hf.kernelPointInclusion M (correction σ) =
    cochain⁻¹ *
      relativeExtend F L M G (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)) *
      relativeConjugate F K M G σ cochain
  unit_eq : ∀ σ : M ≃ₐ[K] M, hf.kernelUnitMap (e.hom ≫ (mu.incl _ n).toMul) M (correction σ) =
    KummerCocycle.value radical σ

private theorem restricted_value_mul (ζ : Cocycle G (GaloisCocycle.cover F L))
    (σ τ : M ≃ₐ[K] M) :
    relativeExtend F L M G (GaloisCocycle.value ζ (((σ * τ).restrictScalars F).restrictNormal L)) =
      relativeExtend F L M G (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)) *
        relativeConjugate F K M G σ
          (relativeExtend F L M G (GaloisCocycle.value ζ ((τ.restrictScalars F).restrictNormal L))) := by
  let localCocycle := GaloisCocycle.scalarExtension (K := K) (M := M) ζ
  let pointEquiv := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) G
  have h := congrArg pointEquiv (GaloisCocycle.value_mul localCocycle σ τ)
  simpa only [pointEquiv, localCocycle, map_mul, GaloisCocycle.scalarExtensionPointsEquiv_conjugate,
    GaloisCocycle.value_scalarExtension] using h

set_option maxHeartbeats 600000 in
/-- Triviality of the projection produces a local Kummer correction on an algebraically
closed finite Galois coefficient field. -/
theorem nonempty_localKummerCorrection [IsAlgClosed M] [FiniteDimensional K M] [IsGalois K M]
    (n : ℕ) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)
    (ζ : Cocycle G (GaloisCocycle.cover F L))
    (h : ((ζ.map f).baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    Nonempty (hf.LocalKummerCorrection (K := K) (M := M) n e ζ) := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) (ζ.map f) h
  obtain ⟨x, hx⟩ := hf.exists_coeffPoint_lift_of_isAlgClosed y
  let A (σ : M ≃ₐ[K] M) := relativeExtend F L M G
    (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L))
  let g (σ : M ≃ₐ[K] M) := relativeConjugate F K M G σ
  let v (σ : M ≃ₐ[K] M) := x⁻¹ * A σ * g σ x
  let p := GroupScheme.affinePointsTarget G f (CommAlgCat.of F M)
  have hA (σ : M ≃ₐ[K] M) : p (A σ) = y * (relativeConjugate F K M H σ y)⁻¹ := by
    have hh := hy σ
    let a := GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L)
    change GaloisCocycle.coverMap F L M ≫ (a ≫ f.hom.hom) = _ at hh
    change (GaloisCocycle.coverMap F L M ≫ a) ≫ f.hom.hom = _
    rw [Category.assoc]
    exact hh
  have hg (σ : M ≃ₐ[K] M) : p (g σ x) = relativeConjugate F K M H σ y := by
    change (GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ x) ≫ f.hom.hom =
      GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ y
    rw [Category.assoc, hx]
  have hv (σ : M ≃ₐ[K] M) : p (v σ) = 1 := by
    change p (x⁻¹ * A σ * g σ x) = 1
    rw [map_mul, map_mul, map_inv, show p x = y from hx, hA, hg]
    group
  have hv_mul (σ τ : M ≃ₐ[K] M) : v (σ * τ) = v σ * g σ (v τ) := by
    change x⁻¹ * A (σ * τ) * g (σ * τ) x =
      (x⁻¹ * A σ * g σ x) * g σ (x⁻¹ * A τ * g τ x)
    rw [show A (σ * τ) = A σ * g σ (A τ) from restricted_value_mul ζ σ τ,
      show g (σ * τ) x = g σ (g τ x) from relativeConjugate_mul F K M G σ τ x]
    simp only [map_mul, map_inv]
    group
  have hker (σ : M ≃ₐ[K] M) :
      ∃ d, hf.kernelPointInclusion M d = v σ :=
    (mem_range_kernelι_iff f _).mpr (hv σ)
  choose d hd using hker
  let χ := e.hom ≫ (mu.incl (Spec (CommRingCat.of F)) n).toMul
  let c (σ : M ≃ₐ[K] M) := hf.kernelUnitMap χ M (d σ)
  have hd_mul (σ τ : M ≃ₐ[K] M) : d (σ * τ) = d σ *
      relativeConjugate F K M hf.commutativeKernel.toGrp σ (d τ) := by
    apply (cancel_mono (kernelι f).hom.hom).mp
    change hf.kernelPointInclusion M (d (σ * τ)) =
      hf.kernelPointInclusion M (d σ * relativeConjugate F K M hf.commutativeKernel.toGrp σ (d τ))
    have he : hf.kernelPointInclusion M (relativeConjugate F K M hf.commutativeKernel.toGrp σ (d τ)) =
        g σ (hf.kernelPointInclusion M (d τ)) :=
      Category.assoc (GaloisCocycle.arrow F M (σ.restrictScalars F)) (d τ) (kernelι f).hom.hom
    rw [map_mul, he, hd, hd, hd, hv_mul]
  have hc : IsMulCocycle₁ c := by
    intro σ τ
    have he : hf.kernelUnitMap χ M
        (relativeConjugate F K M hf.commutativeKernel.toGrp σ (d τ)) = σ • c τ :=
      hf.kernelUnitMap_naturality χ (σ.restrictScalars F).toAlgHom (d τ)
    change hf.kernelUnitMap χ M (d (σ * τ)) = σ • c τ * c σ
    rw [hd_mul, map_mul, he, mul_comm]
  have hp (σ : M ≃ₐ[K] M) : c σ ^ n = 1 := by
    apply (mem_rootsOfUnity n (c σ)).mp
    change hf.kernelUnitMap (e.hom ≫ (mu.incl _ n).toMul) M (d σ) ∈ rootsOfUnity n M
    rw [← hf.kernelRootsEquiv_val]
    exact (hf.kernelRootsEquiv n e M (d σ)).property
  obtain ⟨a, z, hz, hzc⟩ := KummerCocycle.exists_radical n c hc hp
  exact ⟨⟨a, z, hz, x, d, hd, fun σ => (hzc σ).symm⟩⟩

end Langlands.GroupScheme.IsCentralIsogeny
