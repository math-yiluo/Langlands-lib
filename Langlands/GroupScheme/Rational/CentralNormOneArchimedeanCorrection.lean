import Langlands.ClassField.Global.ArchimedeanNormPowerApproximationQuadratic
import Langlands.GroupScheme.Rational.CentralNormOneLocalCorrection
import Langlands.GroupScheme.Rational.CentralMuArchimedeanCorrection

/-! # Simultaneous archimedean correction through norm-one torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open GaloisPoint Langlands.Algebra Langlands.ClassField.Global.TensorUnitShapiro

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Comparison

variable {F K L E M : Type u} [Field F] [Field K] [Field L] [Field E] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra F M] [Algebra K M] [Algebra L M]
  [Algebra L E] [Algebra E M] [IsScalarTower F K M] [IsScalarTower F L M]
  [IsScalarTower F L E] [IsScalarTower F E M] [IsScalarTower L E M]
  [Normal F L] [IsGalois F E] [IsGalois K M] [FiniteDimensional K M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

omit [FiniteDimensional K M] [IsGalois K M]
  [Algebra F K] [Algebra K M] [IsScalarTower F K M] in
private theorem relativeExtend_refinement_value (ζ : Cocycle G (GaloisCocycle.cover F L))
    (σ : Gal(M/F)) :
    relativeExtend F E M G
      (GaloisCocycle.value (ζ.refine (GaloisCocycle.coverMap F L E)) (σ.restrictNormal E)) =
      relativeExtend F L M G (GaloisCocycle.value ζ (σ.restrictNormal L)) := by
  rw [GaloisCocycle.value_refine]
  have h := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L E σ
  change σ.restrictNormal L = (σ.restrictNormal E).restrictNormal L at h
  rw [← h]
  change GaloisCocycle.coverMap F E M ≫ GaloisCocycle.coverMap F L E ≫
      GaloisCocycle.value ζ (σ.restrictNormal L) = _
  rw [← Category.assoc]
  congr 1
  change (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)).op ≫
      (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L E)).op =
    (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L M)).op
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun i : L →ₐ[F] M => (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom i).op)
    (AlgHom.ext fun x => (IsScalarTower.algebraMap_apply L E M x).symm)

set_option maxHeartbeats 800000 in
/-- If the localized kernel cocycle differs from the local correction by a crossed
coboundary, the centrally corrected source cocycle is trivial on the full pullback. -/
theorem LocalCentralCorrection.isTrivial_of_coboundaryRatio
    {ζ : Cocycle G (GaloisCocycle.cover F L)}
    (d : hf.LocalCentralCorrection (K := K) (M := M) ζ)
    (α : Cocycle (kernel f) (GaloisCocycle.cover F E))
    (t : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M))
    (ht : ∀ σ : Gal(M/K), relativeExtend F E M hf.commutativeKernel.toGrp
        (GaloisCocycle.value α ((σ.restrictScalars F).restrictNormal E)) / d.correction σ =
      relativeConjugate F K M hf.commutativeKernel.toGrp σ t / t) :
    (((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral
      α (kernelι f) hf.isCentral_kernelι).baseChangePullback (Spec.algebraMap F K)).IsTrivial := by
  let ζ' := ζ.refine (GaloisCocycle.coverMap F L E)
  let δ := ζ'.divCentral α (kernelι f) hf.isCentral_kernelι
  let ρ (σ : Gal(M/K)) := (σ.restrictScalars F).restrictNormal E
  let A (σ : Gal(M/K)) := relativeExtend F L M G
    (GaloisCocycle.value ζ ((σ.restrictScalars F).restrictNormal L))
  let D (σ : Gal(M/K)) := relativeExtend F E M hf.commutativeKernel.toGrp (GaloisCocycle.value α (ρ σ))
  let j := hf.kernelPointInclusion M
  let g (σ : Gal(M/K)) := relativeConjugate F K M G σ
  have hdiv (σ : Gal(M/K)) :
      j (d.correction σ) * (j (D σ))⁻¹ = j t * (g σ (j t))⁻¹ := by
    have hv : j (relativeConjugate F K M hf.commutativeKernel.toGrp σ t) = g σ (j t) :=
      Category.assoc (GaloisCocycle.arrow F M (σ.restrictScalars F)) t (kernelι f).hom.hom
    have h := congrArg j (ht σ)
    rw [map_div, map_div, hv] at h
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using congrArg Inv.inv h
  let w := d.cochain * j t
  have hA (σ : Gal(M/K)) : A σ = d.cochain * j (d.correction σ) * (g σ d.cochain)⁻¹ := by
    have h : j (d.correction σ) = d.cochain⁻¹ * A σ * g σ d.cochain := d.correction_spec σ
    rw [h]
    group
  have hCob (σ : Gal(M/K)) : A σ * (j (D σ))⁻¹ = w * (g σ w)⁻¹ := by
    have hc : Commute (j (D σ)) (g σ d.cochain) :=
      commute_of_mem_center (hf.isCentral_kernelι _ (D σ)) _
    rw [hA]
    calc
      _ = d.cochain * (j (d.correction σ) * (j (D σ))⁻¹) * (g σ d.cochain)⁻¹ := by
        rw [mul_assoc (d.cochain * j (d.correction σ)), ← hc.inv_left.inv_right.eq]
        group
      _ = _ := by
        rw [hdiv]
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
  rw [map_mul, map_inv, relativeExtend_refinement_value]
  congr 2

end Comparison

section NormComparison

variable {F B L E : Type u} [Field F] [Field B] [Field L] [Field E] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
  [Normal F L] [FiniteDimensional F E] [IsGalois F E]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M]
  [Algebra F M] [Algebra L M] [Algebra E M] [IsScalarTower F v.Completion M]
  [IsScalarTower F L M] [IsScalarTower F E M] [IsScalarTower L E M]
  [FiniteDimensional v.Completion M] [IsGalois v.Completion M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f) (n : ℕ) (e : kernel f ≅ WeilGm.normOneTorsion F B n)

local notation "Kv" => InfinitePlace.Completion v

set_option maxHeartbeats 800000 in
/-- The local norm and power equations compare the global radical with a local
correction and give a trivialization on the actual pullback cover. -/
theorem LocalNormOneCorrection.isTrivial_of_normPowerPair
    {ζ : Cocycle G (GaloisCocycle.cover F L)}
    (d : hf.LocalNormOneCorrection v (M := M) n e ζ)
    {b : Bˣ} {s : Fˣ} (r : NormPowerTensorRadical E n b s)
    (q : (B ⊗[F] Kv)ˣ)
    (hq : leftTensorUnit b = d.radicand * q ^ n)
    (hqN : Units.map (algebraMap F Kv).toMonoidHom s = d.scalar * tensorNormUnits F B Kv q) :
    (((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral (normOneKummerKernelCocycle n e r)
      (kernelι f) hf.isCentral_kernelι).baseChangePullback (Spec.algebraMap F Kv)).IsTrivial := by
  let α := normOneKummerKernelCocycle n e r
  let z := extendTensorUnit M r.tensorUnit
  let q' := extendTensorUnit M q
  let t := z / (d.radical * q')
  have hpz : z ^ n = leftTensorUnit b := calc
    _ = extendTensorUnit M (r.tensorUnit ^ n) := (map_pow (extendTensorUnit M) _ _).symm
    _ = extendTensorUnit M (leftTensorUnit b) := congrArg (extendTensorUnit M) r.pow_eq
    _ = _ := extendTensorUnit_leftTensorUnit M b
  have hq' : leftTensorUnit (F := F) (L := M) b = extendTensorUnit M d.radicand * q' ^ n := by
    calc
      _ = extendTensorUnit M (leftTensorUnit (L := Kv) b) := (extendTensorUnit_leftTensorUnit M b).symm
      _ = extendTensorUnit M (d.radicand * q ^ n) := congrArg (extendTensorUnit M) hq
      _ = _ := by rw [map_mul, map_pow]
  have htp : t ^ n = 1 := by
    change (z / (d.radical * q')) ^ n = 1
    rw [div_pow, mul_pow, hpz, d.radical_pow, hq', div_self']
  let N := tensorNormUnits F B M
  let i := Units.map (algebraMap Kv M).toMonoidHom
  have hNz : N z = i (Units.map (algebraMap F Kv).toMonoidHom s) := calc
    _ = Units.map (algebraMap E M).toMonoidHom (tensorNormUnits F B E r.tensorUnit) :=
      tensorNormUnits_extend M r.tensorUnit
    _ = Units.map (algebraMap E M).toMonoidHom (Units.map (algebraMap F E).toMonoidHom s) :=
      congrArg (Units.map (algebraMap E M).toMonoidHom) r.norm_eq
    _ = _ := by
      apply Units.ext
      change algebraMap E M (algebraMap F E (s : F)) = algebraMap Kv M (algebraMap F Kv (s : F))
      rw [← IsScalarTower.algebraMap_apply F E M, ← IsScalarTower.algebraMap_apply F Kv M]
  have hNq : N q' = i (tensorNormUnits F B Kv q) := tensorNormUnits_extend M q
  have hNd : N d.radical = i d.scalar := d.radical_norm
  have htN : N t = 1 := by
    change N (z / (d.radical * q')) = 1
    rw [map_div, map_mul, hNz, hNd, hNq, ← map_mul, hqN, div_self']
  let t' : WeilGm.normOneTorsionUnits (B := B) n (CommAlgCat.of F M) :=
    ⟨t, (mem_rootsOfUnity n t).mpr htp, htN⟩
  let c := (kernelNormOneEquiv n e M).symm t'
  let k := kernelNormOneToWeil n e
  let j := kernelTensorUnitMap k M
  have hct : j c = t := kernelTensorUnitMap_kernelNormOneEquiv_symm n e t'
  apply LocalCentralCorrection.isTrivial_of_coboundaryRatio (K := Kv) (M := M) hf d.coeff α c
  intro σ
  let ρ := (σ.restrictScalars F).restrictNormal E
  let D := relativeExtend F E M (kernel f) (GaloisCocycle.value α ρ)
  let dσ : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F M) := d.coeff.correction σ
  have hD : j D = tensorCoboundary z (σ.restrictScalars F) := by
    change kernelTensorUnitMap k M
      (GroupScheme.affinePointMap (kernel f)
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)) (GaloisCocycle.value α ρ)) = _
    rw [kernelTensorUnitMap_naturality k (IsScalarTower.toAlgHom F E M),
      kernelTensorUnitMap_value_normOneKummerKernelCocycle n e]
    simp only [tensorCoboundary, z, map_div]
    rw [extendTensorUnit_action]
    rfl
  apply kernelTensorUnitMap_normOne_injective n e
  change j (D / dσ) = j (relativeConjugate F Kv M (kernel f) σ c / c)
  have hact : j (relativeConjugate F Kv M (kernel f) σ c) =
      tensorAction F B M (σ.restrictScalars F) (j c) :=
    kernelTensorUnitMap_naturality k (σ.restrictScalars F).toAlgHom c
  rw [map_div, map_div, hD, show j dσ = _ from d.unit_eq σ, hact, hct]
  let a := tensorAction F B M (σ.restrictScalars F)
  have hfix : a q' = q' := tensorAction_extendCompletion v σ q
  change (a z / z) / (a d.radical / d.radical) = a (z / (d.radical * q')) / (z / (d.radical * q'))
  rw [map_div, map_mul, hfix]
  conv_rhs => rw [div_div_div_comm, mul_div_mul_right_eq_div]

end NormComparison

section Simultaneous

variable {F B L : Type u} [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)

/-- A single central kernel cocycle on a refinement makes all infinite-place restrictions
of the source cocycle trivial. -/
def HasArchimedeanCentralCorrection (ζ : Cocycle G (GaloisCocycle.cover F L)) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
    (_ : Algebra L E) (_ : IsScalarTower F L E) (α : Cocycle (kernel f) (GaloisCocycle.cover F E)),
      ((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral α (kernelι f)
        hf.isCentral_kernelι).ArchimedeanTrivial

set_option maxHeartbeats 900000 in
/-- For norm-one torsion of quadratic or coprime degree, one global correction
makes the source lift trivial on all actual infinite pullback covers. -/
theorem hasArchimedeanCentralCorrection_of_normOneKernel
    (n : ℕ) (hn : 0 < n) (e : kernel f ≅ WeilGm.normOneTorsion F B n)
    (hB : Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n)
    (ζ : Cocycle G (GaloisCocycle.cover F L)) (h : (ζ.map f).ArchimedeanTrivial) :
    hf.HasArchimedeanCentralCorrection ζ := by
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
    Classical.choice (hf.nonempty_localNormOneCorrection v (M := M v) n e ζ (h v))
  obtain ⟨b, s, hs, hloc⟩ := archimedeanNormPowerApproximation hn hB
    (fun v => (d v).radicand) (fun v => (d v).scalar) (fun v => (d v).radicand_norm)
  obtain ⟨E, _, _, _, _, _, _, ⟨r⟩⟩ := exists_normPowerTensorRadical (L := L) n hn b s hs
  let : FiniteDimensional L E := FiniteDimensional.right F L E
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, normOneKummerKernelCocycle n e r, ?_⟩
  intro v
  let jE : E →ₐ[L] M v := IsAlgClosed.lift
  let : Algebra E (M v) := jE.toRingHom.toAlgebra
  let : IsScalarTower L E (M v) := IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm
  let : IsScalarTower F E (M v) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F L E, ← IsScalarTower.algebraMap_apply L E (M v),
      IsScalarTower.algebraMap_apply F L (M v)]
  obtain ⟨q, hq, hqN⟩ := hloc v
  exact LocalNormOneCorrection.isTrivial_of_normPowerPair v hf n e (d v) r q hq hqN

end Simultaneous

end Langlands.GroupScheme.IsCentralIsogeny
