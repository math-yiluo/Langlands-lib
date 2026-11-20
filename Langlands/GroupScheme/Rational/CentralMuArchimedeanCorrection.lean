import Langlands.GroupScheme.Rational.CentralMuLocalCorrection
import Langlands.GroupScheme.Rational.CentralMuKummerCocycle
import Langlands.GroupScheme.CentralIsogeny.CocycleCorrection
import Langlands.Global.Arithmetic.ArchimedeanPowerApproximation
import Langlands.Global.Arithmetic.ArchimedeanAlgebraicClosure

/-! # Simultaneous archimedean correction of a lift through a roots-of-unity kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Triviality on the pullback cover at each actual infinite completion. -/
def Cocycle.ArchimedeanTrivial {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    (ξ : Cocycle G U) : Prop :=
  ∀ v : InfinitePlace F, (ξ.baseChangePullback (Spec.algebraMap F v.Completion)).IsTrivial

namespace IsCentralIsogeny

open GaloisPoint

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)
  (n : ℕ) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)

local notation "χ" => (Iso.hom e ≫ Additive.toMul (mu.incl (Spec (CommRingCat.of F)) n))

section LocalComparison

variable {K E M : Type u} [Field K] [Field E] [Field M]
  [Algebra F K] [Algebra F E] [Algebra F M] [Algebra K M] [Algebra L M]
  [Algebra L E] [Algebra E M] [IsScalarTower F K M] [IsScalarTower F L M]
  [IsScalarTower F L E] [IsScalarTower F E M] [IsScalarTower L E M]
  [IsGalois F E] [FiniteDimensional F E] [IsGalois K M] [FiniteDimensional K M]

omit [FiniteDimensional F L] [FiniteDimensional F E] in
private theorem relativeExtend_refine_value (ζ : Cocycle G (GaloisCocycle.cover F L))
    (s : M ≃ₐ[F] M) :
    relativeExtend F E M G (GaloisCocycle.value
      (ζ.refine (GaloisCocycle.coverMap F L E)) (s.restrictNormal E)) =
      relativeExtend F L M G (GaloisCocycle.value ζ (s.restrictNormal L)) := by
  rw [GaloisCocycle.value_refine]
  have h := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L E s
  change s.restrictNormal L = (s.restrictNormal E).restrictNormal L at h
  rw [← h]
  change GaloisCocycle.coverMap F E M ≫ GaloisCocycle.coverMap F L E ≫
      GaloisCocycle.value ζ (s.restrictNormal L) = _
  rw [← Category.assoc]
  congr 1
  change (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)).op ≫
      (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L E)).op =
    (algSpec (CommRingCat.of F)).map
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L M)).op
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun i : L →ₐ[F] M => (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom i).op)
    (AlgHom.ext fun x => (IsScalarTower.algebraMap_apply L E M x).symm)

omit [FiniteDimensional F L] in
/-- Matching unit power classes give a trivialization after dividing by the global Kummer
cocycle on a common local coefficient field. -/
theorem LocalKummerCorrection.isTrivial_of_powerClass
    {ζ : Cocycle G (GaloisCocycle.cover F L)}
    (d : hf.LocalKummerCorrection (K := K) (M := M) n e ζ)
    (a : Fˣ) {z : Eˣ} (hz : z ^ n = Units.map (algebraMap F E) a)
    (q : Kˣ) (hq : Units.map (algebraMap F K) a = d.scalar * q ^ n) :
    (((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral
      (hf.kummerKernelCocycle n e a hz) (kernelι f) hf.isCentral_kernelι).baseChangePullback
        (Spec.algebraMap F K)).IsTrivial := by
  let α := hf.kummerKernelCocycle n e a hz
  let ζ' := ζ.refine (GaloisCocycle.coverMap F L E)
  let δ := ζ'.divCentral α (kernelι f) hf.isCentral_kernelι
  let ρ (σ : M ≃ₐ[K] M) := (σ.restrictScalars F).restrictNormal E
  let A (σ : M ≃ₐ[K] M) := relativeExtend F L M G
    (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L))
  let B (σ : M ≃ₐ[K] M) := relativeExtend F E M hf.commutativeKernel.toGrp
    (GaloisCocycle.value α (ρ σ))
  let j := hf.kernelPointInclusion M
  let u := hf.kernelUnitMap (χ) M
  let g (σ : M ≃ₐ[K] M) := relativeConjugate F K M G σ
  let z₀ : Mˣ := Units.map (algebraMap E M) z
  have hz₀ : z₀ ^ n = Units.map (algebraMap K M) (Units.map (algebraMap F K).toMonoidHom a) := by
    simp only [z₀, ← map_pow, hz]
    apply Units.ext
    change algebraMap E M (algebraMap F E (a : F)) = algebraMap K M (algebraMap F K (a : F))
    rw [← IsScalarTower.algebraMap_apply F E M, ← IsScalarTower.algebraMap_apply F K M]
  have hB (σ : M ≃ₐ[K] M) : u (B σ) = KummerCocycle.value z₀ σ := by
    change hf.kernelUnitMap (χ) M
      (GroupScheme.affinePointMap hf.commutativeKernel.toGrp
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)) (GaloisCocycle.value α (ρ σ))) = _
    rw [hf.kernelUnitMap_naturality (χ) (IsScalarTower.toAlgHom F E M),
      hf.kernelUnitMap_value_kummerKernelCocycle n e a hz]
    simp only [KummerCocycle.value, z₀, map_div]
    congr 1
    apply Units.ext
    exact ((σ.restrictScalars F).restrictNormal_commutes E (z : E))
  obtain ⟨t, ht⟩ := KummerCocycle.exists_root_compare n
    (Units.map (algebraMap F K) a) d.scalar q hz₀ d.radical_pow hq
  let t₀ := (hf.kernelRootsEquiv n e M).symm t
  have hu : u t₀ = (t : Mˣ) := hf.kernelUnitMap_kernelRootsEquiv_symm n e t
  have hdiv (σ : M ≃ₐ[K] M) : B σ / d.correction σ =
      relativeConjugate F K M hf.commutativeKernel.toGrp σ t₀ / t₀ := by
    apply hf.kernelUnitMap_mu_injective n e
    change u (B σ / d.correction σ) =
      u (relativeConjugate F K M hf.commutativeKernel.toGrp σ t₀ / t₀)
    have he : u (relativeConjugate F K M hf.commutativeKernel.toGrp σ t₀) = σ • u t₀ :=
      hf.kernelUnitMap_naturality (χ) (σ.restrictScalars F).toAlgHom t₀
    rw [map_div, map_div, hB, show u (d.correction σ) = _ from d.unit_eq σ, he, hu]
    exact ht σ
  have hdiv' (σ : M ≃ₐ[K] M) :
      j (d.correction σ) * (j (B σ))⁻¹ = j t₀ * (g σ (j t₀))⁻¹ := by
    have hv : j (relativeConjugate F K M hf.commutativeKernel.toGrp σ t₀) = g σ (j t₀) :=
      Category.assoc (GaloisCocycle.arrow F M (σ.restrictScalars F)) t₀ (kernelι f).hom.hom
    have h := congrArg j (hdiv σ)
    rw [map_div, map_div, hv] at h
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using congrArg Inv.inv h
  let w := d.cochain * j t₀
  have hA (σ : M ≃ₐ[K] M) : A σ = d.cochain * j (d.correction σ) * (g σ d.cochain)⁻¹ := by
    have h : j (d.correction σ) = d.cochain⁻¹ * A σ * g σ d.cochain := d.correction_spec σ
    rw [h]
    group
  have hCob (σ : M ≃ₐ[K] M) : A σ * (j (B σ))⁻¹ = w * (g σ w)⁻¹ := by
    have hc : Commute (j (B σ)) (g σ d.cochain) :=
      commute_of_mem_center (hf.isCentral_kernelι _ (B σ)) _
    rw [hA]
    calc
      _ = d.cochain * (j (d.correction σ) * (j (B σ))⁻¹) * (g σ d.cochain)⁻¹ := by
        rw [mul_assoc (d.cochain * j (d.correction σ)), ← hc.inv_left.inv_right.eq]
        group
      _ = _ := by
        rw [hdiv']
        simp only [w, map_mul, mul_inv_rev]
        group
  apply GaloisCocycle.isTrivial_baseChange_of_scalarExtension (M := M)
  let P := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) G
  let y := P.symm w
  refine ⟨y, ?_⟩
  apply GaloisCocycle.toFun_eq_of_value_eq _ (Cocycle.coboundary y)
  intro σ
  apply P.injective
  change P (GaloisCocycle.value (GaloisCocycle.scalarExtension (K := K) (M := M) δ) σ) =
    P (GaloisCocycle.value (Cocycle.coboundary y) σ)
  rw [GaloisCocycle.value_coboundary, map_mul, map_inv]
  change _ = P y * (P (GaloisPoint.conjugate K M _ σ y))⁻¹
  rw [show P (GaloisPoint.conjugate K M _ σ y) = g σ (P y) from
    GaloisCocycle.scalarExtensionPointsEquiv_conjugate y σ,
    show P y = w from P.apply_symm_apply w, ← hCob]
  change GaloisCocycle.scalarExtensionPointsEquiv G
      (GaloisCocycle.value (GaloisCocycle.scalarExtension (K := K) (M := M) δ) σ) = _
  rw [GaloisCocycle.value_scalarExtension]
  change relativeExtend F E M G (GaloisCocycle.value ζ' (ρ σ) *
    (GaloisCocycle.value α (ρ σ) ≫ (kernelι f).hom.hom)⁻¹) = _
  rw [map_mul, map_inv, relativeExtend_refine_value]
  congr 2

end LocalComparison

variable [NumberField F]

include e in
/-- A single global kernel cocycle corrects a lift at every infinite place, after one
finite Galois refinement. -/
theorem exists_corrected_archimedeanTrivial (hn : 0 < n)
    (ζ : Cocycle G (GaloisCocycle.cover F L)) (h : (ζ.map f).ArchimedeanTrivial) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E) (α : Cocycle (kernel f) (GaloisCocycle.cover F E)),
      ((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral α (kernelι f)
        hf.isCentral_kernelι).ArchimedeanTrivial := by
  let K (v : InfinitePlace F) := v.Completion
  let M (v : InfinitePlace F) := AlgebraicClosure (K v)
  let : ∀ v : InfinitePlace F, FiniteDimensional (K v) (M v) :=
    fun v => Global.finiteArchimedeanAlgebraicClosure F v
  let : ∀ v : InfinitePlace F, CharZero (K v) :=
    fun v => charZero_of_injective_algebraMap (algebraMap F (K v)).injective
  let : ∀ v : InfinitePlace F, IsGalois (K v) (M v) :=
    fun _ => isGalois_iff.mpr ⟨inferInstance, ⟨fun _ => IsAlgClosed.splits _⟩⟩
  let jL (v : InfinitePlace F) : L →ₐ[F] M v := IsAlgClosed.lift
  let : ∀ v : InfinitePlace F, Algebra L (M v) := fun v => (jL v).toRingHom.toAlgebra
  let : ∀ v : InfinitePlace F, IsScalarTower F L (M v) :=
    fun v => IsScalarTower.of_algebraMap_eq fun x => ((jL v).commutes x).symm
  let d (v : InfinitePlace F) :=
    Classical.choice (hf.nonempty_localKummerCorrection (K := K v) (M := M v) n e ζ (h v))
  obtain ⟨a, ha⟩ := Global.exists_representsArchimedeanUnitPowers F hn (fun v => (d v).scalar)
  obtain ⟨E, _, _, _, _, _, _, z, hz⟩ :=
    KummerCocycle.exists_unit_radical_in_finiteGalois_refinement (L := L) n hn a
  let : FiniteDimensional L E := FiniteDimensional.right F L E
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hf.kummerKernelCocycle n e a hz, ?_⟩
  intro v
  let jE : E →ₐ[L] M v := IsAlgClosed.lift
  let : Algebra E (M v) := jE.toRingHom.toAlgebra
  let : IsScalarTower L E (M v) := IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm
  let : IsScalarTower F E (M v) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F L E, ← IsScalarTower.algebraMap_apply L E (M v),
      IsScalarTower.algebraMap_apply F L (M v)]
  obtain ⟨q, hq⟩ := ha v
  exact LocalKummerCorrection.isTrivial_of_powerClass hf n e (d v) a hz q hq

end IsCentralIsogeny
end Langlands.GroupScheme
