import Langlands.AlgebraicGeometry.Picard.TwoAxisClassObstruction
import Langlands.Cohomology.ModuleComplex.ObstructionInjectivitySpread
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartFrames
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Murre's condition (F8) for the two-axis class presheaf

A class `ξ'` over `Λ ⧸ I` that lifts to no larger closed subscheme at the generic point keeps
this property over a nonempty basic open set `D(g₀)`. The proof uses Čech obstruction cocycles:
lifts along square-zero extensions with kernel `M` correspond to solutions of `d c + φ_* z = 0`
(`TwoAxisClassObstruction`), and injectivity of `φ ↦ [φ_* z]` spreads from the generic point
(`ObstructionInjectivity.exists_injVanishes_spread`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AbelianScheme

namespace GenericNonLifting

variable {Λ : Type u} [CommRing Λ]

/-- The generic point of an irreducible spectrum lies in every prime: its ideal is contained in
the nilradical. -/
theorem asIdeal_le_nilradical (t : PrimeSpectrum Λ) (ht : IsGenericPoint t Set.univ) :
    t.asIdeal ≤ nilradical Λ := by
  rw [nilradical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  have hsp : t ⤳ (⟨J, hJ⟩ : PrimeSpectrum Λ) :=
    (isGenericPoint_iff_specializes.mp ht _).mpr (Set.mem_univ _)
  exact (PrimeSpectrum.le_iff_specializes _ _).mpr hsp

/-- An ideal `I` with `𝔞 * I = ⊥` is killed by `𝔞`. -/
theorem isTorsionBySet_ideal {𝔞 I : Ideal Λ} (h : 𝔞 * I = ⊥) :
    Module.IsTorsionBySet Λ I 𝔞 := by
  intro x a
  apply Subtype.ext
  have hmem : (a : Λ) * (x : Λ) ∈ 𝔞 * I := Ideal.mul_mem_mul a.2 x.2
  rw [h, Ideal.mem_bot] at hmem
  exact hmem

/-- Over a quotient by an ideal killing the extension of `I`, the kernel of `B ⧸ J → B ⧸ IB` is
killed by `𝔞` when `𝔞 * I = ⊥`. -/
theorem isTorsionBySet_ker {B : Type u} [CommRing B] [Algebra Λ B] {𝔞 I : Ideal Λ}
    (h : 𝔞 * I = ⊥) {J : Ideal B} (hJ : J ≤ I.map (algebraMap Λ B)) :
    Module.IsTorsionBySet Λ (RingHom.ker (Ideal.Quotient.factorₐ Λ hJ).toRingHom) 𝔞 := by
  intro x a
  apply Subtype.ext
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : B ⧸ J)
  have hbI : b ∈ I.map (algebraMap Λ B) := by
    have hx := x.2
    rw [RingHom.mem_ker, ← hb] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hmem : algebraMap Λ B a * b ∈ (𝔞 * I).map (algebraMap Λ B) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ a.2) hbI
  rw [h, Ideal.map_bot, Ideal.mem_bot] at hmem
  change (a : Λ) • (x : B ⧸ J) = 0
  rw [← hb, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmem, map_zero]

/-- The kernel of `B ⧸ J → B ⧸ IB` has square zero when `I * I = ⊥`. -/
theorem mul_eq_zero_of_mem_ker {B : Type u} [CommRing B] [Algebra Λ B] {I : Ideal Λ}
    (hII : I * I = ⊥) {J : Ideal B} (hJ : J ≤ I.map (algebraMap Λ B))
    (m m' : RingHom.ker (Ideal.Quotient.factorₐ Λ hJ).toRingHom) :
    (m : B ⧸ J) * m' = 0 := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (m : B ⧸ J)
  obtain ⟨b', hb'⟩ := Ideal.Quotient.mk_surjective (m' : B ⧸ J)
  have hmem : ∀ (y : RingHom.ker (Ideal.Quotient.factorₐ Λ hJ).toRingHom) (c : B),
      Ideal.Quotient.mk J c = y → c ∈ I.map (algebraMap Λ B) := by
    intro y c hc
    have hy := y.2
    rw [RingHom.mem_ker, ← hc] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hprod : b * b' ∈ (I * I).map (algebraMap Λ B) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (hmem m b hb) (hmem m' b' hb')
  rw [hII, Ideal.map_bot, Ideal.mem_bot] at hprod
  rw [← hb, ← hb', ← map_mul, hprod, map_zero]

/-- **The hyperplane at the generic point.** A nonzero linear form `ψ : I → κ(p)` extends to a
surjection `Ψ : IΛ_p → κ(p)`; its kernel is an ideal `J < IΛ_p`, and `κ(p) ≅ IΛ_p / J` embeds into
`Λ_p ⧸ J` as the square-zero kernel of `Λ_p ⧸ J → Λ_p ⧸ IΛ_p`, with `x ∈ I` going to `ψ x`. -/
theorem exists_hyperplane (p : Ideal Λ) [p.IsPrime] {I : Ideal Λ} (hII : I * I = ⊥)
    (ψ : I →ₗ[Λ] p.ResidueField) (hψ : ψ ≠ 0) :
    ∃ (J : Ideal (Localization.AtPrime p))
      (hJ : J < I.map (algebraMap Λ (Localization.AtPrime p)))
      (jM : p.ResidueField →ₗ[Λ] Localization.AtPrime p ⧸ J),
      Function.Injective jM ∧
      (∀ a, a ∈ RingHom.ker (Ideal.Quotient.factorₐ Λ hJ.le).toRingHom ↔ ∃ m, jM m = a) ∧
      (∀ m m', jM m * jM m' = 0) ∧
      ∀ x : I, jM (ψ x) = algebraMap Λ (Localization.AtPrime p ⧸ J) (x : Λ) := by
  set Λp := Localization.AtPrime p
  set IΛ : Ideal Λp := I.map (algebraMap Λ Λp)
  have hbc : IsBaseChange Λp (Algebra.idealMap Λp I) :=
    IsLocalizedModule.isBaseChange p.primeCompl Λp _
  let Ψ : IΛ →ₗ[Λp] p.ResidueField := hbc.lift ψ
  have hΨ : ∀ x : I, Ψ (Algebra.idealMap Λp I x) = ψ x := hbc.lift_eq ψ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (LinearMap.ext h)
  have hsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (y * (ψ x₀)⁻¹)
    refine ⟨a • Algebra.idealMap Λp I x₀, ?_⟩
    rw [map_smul, hΨ, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, ha,
      mul_assoc, inv_mul_cancel₀ hx₀, mul_one]
  let J : Ideal Λp := (LinearMap.ker Ψ).map IΛ.subtype
  have hJle : J ≤ IΛ := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hJne : J ≠ IΛ := by
    intro hJ
    have hmem : (Algebra.idealMap Λp I x₀ : Λp) ∈ J := by
      rw [hJ]
      exact (Algebra.idealMap Λp I x₀).2
    obtain ⟨w, hw, hweq⟩ := hmem
    have hw' : w = Algebra.idealMap Λp I x₀ := Subtype.ext hweq
    have hw2 : Ψ w = 0 := hw
    rw [hw', hΨ] at hw2
    exact hx₀ hw2
  have hJ : J < IΛ := lt_of_le_of_ne hJle hJne
  let eq := Ψ.quotKerEquivOfSurjective hsurj
  let φ : (IΛ ⧸ LinearMap.ker Ψ) →ₗ[Λp] Λp ⧸ J :=
    (LinearMap.ker Ψ).mapQ J IΛ.subtype (Submodule.le_comap_map _ _)
  have hφ : ∀ w : IΛ, φ (Submodule.Quotient.mk w) = Ideal.Quotient.mk J (w : Λp) :=
    fun w => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ,
      Submodule.comap_map_eq_of_injective IΛ.injective_subtype, Submodule.mkQ_map_self]
  let jM : p.ResidueField →ₗ[Λ] Λp ⧸ J := (φ ∘ₗ eq.symm.toLinearMap).restrictScalars Λ
  have hjM : ∀ m, jM m = φ (eq.symm m) := fun m => rfl
  have hrep : ∀ m, ∃ w : IΛ, jM m = Ideal.Quotient.mk J (w : Λp) := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (eq.symm m)
    exact ⟨w, by rw [hjM, ← hw, hφ]⟩
  refine ⟨J, hJ, jM, ?_, ?_, ?_, ?_⟩
  · intro m m' h
    exact eq.symm.injective (hφinj h)
  · intro a
    constructor
    · intro ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hb : b ∈ IΛ := by
        rw [RingHom.mem_ker] at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      refine ⟨Ψ ⟨b, hb⟩, ?_⟩
      rw [hjM]
      have : eq.symm (Ψ ⟨b, hb⟩) = Submodule.Quotient.mk ⟨b, hb⟩ := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      rw [this, hφ]
    · rintro ⟨m, rfl⟩
      obtain ⟨w, hw⟩ := hrep m
      rw [hw, RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr w.2
  · intro m m'
    obtain ⟨w, hw⟩ := hrep m
    obtain ⟨w', hw'⟩ := hrep m'
    have hprod : (w : Λp) * w' ∈ (I * I).map (algebraMap Λ Λp) := by
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul w.2 w'.2
    rw [hII, Ideal.map_bot, Ideal.mem_bot] at hprod
    rw [hw, hw', ← map_mul, hprod, map_zero]
  · intro x
    rw [hjM]
    have : eq.symm (ψ x) = Submodule.Quotient.mk (Algebra.idealMap Λp I x) := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hΨ x).symm
    rw [this, hφ, Algebra.idealMap_apply_coe, Ideal.Quotient.mk_algebraMap]

end GenericNonLifting

namespace TwoAxisRigidifiedLineBundle

open TwoAxisFamily UnramifiedFunctor OpennessOfVersality RelativeAffineSections
open Langlands.Cohomology.ModuleComplex.ObstructionInjectivity GenericNonLifting

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)
variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

section Steps

variable {I : Ideal Λ} [Module (Λ ⧸ I) I] [IsScalarTower Λ (Λ ⧸ I) I]
  (K : (relSpace (productStructure A f) Λ).OrderedAffineCover)
  (g : ∀ i j : K.ι, (Γ(relSpace (productStructure A f) Λ, K.U i ⊓ K.U j))ˣ)
  (hjQ : ∀ a : Λ, a ∈ RingHom.ker (algebraMap Λ (Λ ⧸ I)) ↔ ∃ x, I.subtype x = a)
  (hg : ∀ s : K.Idx 2, defect (productStructure A f) K g s ∈
    (RingHom.ker (algebraMap Λ (Λ ⧸ I))).map
      (structureHom (productStructure A f) Λ (K.inter s)).hom)
  (L' : relative A (algebraOver f (Λ ⧸ I)))
  (e : ∀ i, Γ((toRel A f (Λ ⧸ I) (carrierBundle A L')).obj,
    (testCover (productStructure A f) K (Λ ⧸ I)).U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover (productStructure A f) K (Λ ⧸ I)).U i))
  (hge : CocycleGluing.IsTransition e (pushUnits (productStructure A f) K
    (relMap (productStructure A f) (IsScalarTower.toAlgHom Λ Λ (Λ ⧸ I)))
    (testCover (productStructure A f) K (Λ ⧸ I)).U (fun _ _ => le_rfl) g))

include he hge in
/-- **The generic step.** If the class of `L'` lifts to no larger subscheme of `Spec Λ_p`, the
obstruction map is injective with coefficients in the residue field `κ(p)`. -/
theorem injVanishes_residueField (hII : I * I = ⊥) (p : Ideal Λ) [p.IsPrime]
    [Module (Λ ⧸ I) p.ResidueField] [IsScalarTower Λ (Λ ⧸ I) p.ResidueField]
    (hNL : NoLargerLift (F := classPresheaf A) (f := f) (Localization.AtPrime p)
      (Quotient.mk _ L' : Classes A (algebraOver f (Λ ⧸ I)))) :
    InjVanishes (fun i => cplx (productStructure A f) K (Λ ⧸ I) i)
      (fun i => dif (productStructure A f) K (Λ ⧸ I) i)
      (zObs (productStructure A f) K I.subtype hjQ g hg) p.ResidueField := by
  intro c ψ hc
  by_contra hψ
  have hψΛ : ψ.restrictScalars Λ ≠ 0 := fun h => hψ (LinearMap.ext fun x => LinearMap.congr_fun h x)
  obtain ⟨J, hJ, jM, hjMinj, hjMr, hjMsq, hjMψ⟩ := exists_hyperplane p hII _ hψΛ
  have hπ : Function.Surjective (algebraMap Λ (Λ ⧸ I)) := Ideal.Quotient.mk_surjective
  let χ : Λ ⧸ I →ₐ[Λ] Localization.AtPrime p ⧸ I.map (algebraMap Λ (Localization.AtPrime p)) :=
    Ideal.quotientMapₐ (I.map (algebraMap Λ (Localization.AtPrime p)))
      (Algebra.ofId Λ (Localization.AtPrime p)) (fun _ hx => Ideal.mem_map_of_mem _ hx)
  let q := Ideal.Quotient.factorₐ Λ hJ.le
  have hphi : phiQ χ q (toAlgHom_comp_eq χ q) hπ I.subtype (hjQ0_of I.subtype hjQ) jM hjMinj
      hjMr = ψ := by
    ext x
    apply hjMinj
    rw [jM_phiQ]
    exact (hjMψ x).symm
  obtain ⟨η, hη⟩ := exists_classLift_of_cocycle A f K g hπ I.subtype hjQ hg L' e he hge χ q
    (Ideal.Quotient.factor_surjective hJ.le) jM hjMinj hjMr hjMsq c (by rw [hphi]; exact hc)
  exact hNL J hJ η hη

include he hge in
/-- **The open step.** Suppose the reduced injectivity condition holds for every module killed
by `p` on which `g₀` acts bijectively, and `g₀` is a unit in `B`. Then the class of `L'` lifts to
no larger subscheme of `Spec B`. -/
theorem noLargerLift_of_injVanishesRed (hII : I * I = ⊥) (p : Ideal Λ) (hpI : p * I = ⊥)
    (B : Type u) [CommRing B] [Algebra Λ B] (g₀ : Λ) (hu : IsUnit (algebraMap Λ B g₀))
    (hP : ∀ (M : Type u) [AddCommGroup M] [Module Λ M], Module.IsTorsionBySet Λ M p →
      Function.Bijective (fun m : M => g₀ • m) →
      InjVanishesRed
        (fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).cochain K i)
        (fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).d K i)
        (red (Λ ⧸ I) _ I (zObs (productStructure A f) K I.subtype hjQ g hg)) M) :
    NoLargerLift (F := classPresheaf A) (f := f) B
      (Quotient.mk _ L' : Classes A (algebraOver f (Λ ⧸ I))) := by
  intro J hJ η hη
  have hπ : Function.Surjective (algebraMap Λ (Λ ⧸ I)) := Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.factorₐ Λ hJ.le
  let χ : Λ ⧸ I →ₐ[Λ] B ⧸ I.map (algebraMap Λ B) :=
    Ideal.quotientMapₐ (I.map (algebraMap Λ B)) (Algebra.ofId Λ B)
      (fun _ hx => Ideal.mem_map_of_mem _ hx)
  let M := RingHom.ker q.toRingHom
  let : Module (Λ ⧸ I) M := (isTorsionBySet_ker hII hJ.le).module
  have : IsScalarTower Λ (Λ ⧸ I) M := (isTorsionBySet_ker hII hJ.le).isScalarTower
  let jM : M →ₗ[Λ] B ⧸ J := M.subtype.restrictScalars Λ
  have hjMinj : Function.Injective jM := Subtype.val_injective
  have hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a :=
    fun a => ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, fun ⟨m, hm⟩ => hm ▸ m.2⟩
  have hjMsq : ∀ m m', jM m * jM m' = 0 := mul_eq_zero_of_mem_ker hII hJ.le
  have hn : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    rw [Ideal.mem_bot]
    exact mul_eq_zero_of_mem_ker hII hJ.le ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_cocycle_of_classLift A f K g hπ I.subtype hjQ hg L' e he hge χ q
    (Ideal.Quotient.factor_surjective hJ.le) jM hjMinj hjMr hjMsq hn η hη
  -- `g₀` acts bijectively on `M`
  obtain ⟨u, hu'⟩ := hu.map (Ideal.Quotient.mk J)
  have hsmul : ∀ m : M, g₀ • m = (u : B ⧸ J) • m := by
    intro m
    apply Subtype.ext
    change g₀ • (m : B ⧸ J) = (u : B ⧸ J) * m
    rw [hu', Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
  have hbij : Function.Bijective (fun m : M => g₀ • m) := by
    refine ⟨fun m m' h => ?_, fun m => ⟨(↑u⁻¹ : B ⧸ J) • m, ?_⟩⟩
    · have h' : (u : B ⧸ J) • m = (u : B ⧸ J) • m' := by
        rw [← hsmul, ← hsmul]
        exact h
      have := congrArg (fun x : M => (↑u⁻¹ : B ⧸ J) • x) h'
      simpa only [smul_smul, Units.inv_mul, one_smul] using this
    · change g₀ • ((↑u⁻¹ : B ⧸ J) • m) = m
      rw [hsmul, smul_smul, Units.mul_inv, one_smul]
  have hRed := hP M (isTorsionBySet_ker hpI hJ.le) hbij
  have hinj := (injVanishes_baseChange_iff
    (fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).cochain K i)
    (fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).d K i) hπ
    (zObs (productStructure A f) K I.subtype hjQ g hg) M).mpr hRed
  have h0 := hinj c _ hc
  apply hJ.ne (le_antisymm hJ.le ?_)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have h1 := jM_phiQ χ q (toAlgHom_comp_eq χ q) hπ I.subtype (hjQ0_of I.subtype hjQ) jM hjMinj
    hjMr ⟨x, hx⟩
  rw [h0, LinearMap.zero_apply, map_zero] at h1
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
  exact h1.symm

end Steps

/-- **Murre's condition (F8)** for the two-axis class presheaf over any base. -/
theorem classPresheaf_genericNonLifting : GenericNonLifting (classPresheaf A) := by
  intro Λ _ _ t ht I hI hIN f ξ' hNL
  set p := t.asIdeal with hp
  have hpN : p ≤ nilradical Λ := asIdeal_le_nilradical t ht
  have hIle : I ≤ nilradical Λ := by
    intro x hx
    obtain ⟨n, hn⟩ := hI
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hII : I * I = ⊥ := le_bot_iff.mp ((Ideal.mul_mono_right hIle).trans hIN.le)
  have hpI : p * I = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_left hpN).trans (by rw [mul_comm, hIN]))
  have hIp : I ≤ p := hIle.trans (nilradical_le_prime p)
  induction ξ' using Quotient.inductionOn with
  | h L' =>
  have : CompactSpace (relSpace (productStructure A f) Λ) := by
    have := isProper_relProj (productStructure A f) Λ
    exact QuasiCompact.compactSpace_of_compactSpace (relProj (productStructure A f) Λ)
  have hπ : Function.Surjective (algebraMap Λ (Λ ⧸ I)) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap Λ (Λ ⧸ I)) = I := Ideal.mk_ker
  have hn : IsNilpotent (RingHom.ker (algebraMap Λ (Λ ⧸ I))) := by rw [hker]; exact hI
  obtain ⟨K, e, he, g, hge, hg⟩ := exists_chartFrames (productStructure A f) hπ hn
    (toRel A f (Λ ⧸ I) (carrierBundle A L'))
  -- module structures on `Q = I`
  let : Module (Λ ⧸ I) I := (isTorsionBySet_ideal hII).module
  have : IsScalarTower Λ (Λ ⧸ I) I := (isTorsionBySet_ideal hII).isScalarTower
  let : Module (Λ ⧸ p) I := (isTorsionBySet_ideal hpI).module
  have : IsScalarTower Λ (Λ ⧸ p) I := (isTorsionBySet_ideal hpI).isScalarTower
  have hjQ : ∀ a : Λ, a ∈ RingHom.ker (algebraMap Λ (Λ ⧸ I)) ↔ ∃ x, I.subtype x = a := by
    intro a
    rw [hker]
    exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩
  set C := fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).cochain K i
    with hC
  set d := fun i => (OModulePresheaf.unit (relProj (productStructure A f) Λ)).d K i with hd
  set z := zObs (productStructure A f) K I.subtype hjQ g hg with hz
  set z₁ : ((Λ ⧸ p) ⊗[Λ] C 2) ⊗[Λ ⧸ p] I := (red (Λ ⧸ p) (C 2) I).symm (red (Λ ⧸ I) (C 2) I z)
    with hz₁
  have hred : red (Λ ⧸ I) (C 2) I z = red (Λ ⧸ p) (C 2) I z₁ := by
    rw [hz₁, LinearEquiv.apply_symm_apply]
  have hπp : Function.Surjective (algebraMap Λ (Λ ⧸ p)) := Ideal.Quotient.mk_surjective
  -- the generic step, at the residue field `κ(p)`
  have hkI : Module.IsTorsionBySet Λ p.ResidueField I := by
    intro x a
    rw [Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr (hIp a.2), zero_mul]
  let : Module (Λ ⧸ I) p.ResidueField := hkI.module
  have : IsScalarTower Λ (Λ ⧸ I) p.ResidueField := hkI.isScalarTower
  have hk0 := injVanishes_residueField A f K g hjQ hg L' e he hge hII p hNL
  have hkRed := (injVanishes_baseChange_iff C d hπ z p.ResidueField).mp hk0
  rw [hred] at hkRed
  have hk := (injVanishes_baseChange_iff C d hπp z₁ p.ResidueField).mpr hkRed
  -- the cocycle over `Λ ⧸ p`
  have hzc : (dif (productStructure A f) K (Λ ⧸ I) 2).rTensor I z = 0 :=
    dif_zObs (productStructure A f) K I.subtype Subtype.val_injective hjQ
      (fun x y => by
        have hmem : (x : Λ) * y ∈ I * I := Ideal.mul_mem_mul x.2 y.2
        rwa [hII, Ideal.mem_bot] at hmem) g hg
  have hz₁c : (dif (productStructure A f) K (Λ ⧸ p) 2).rTensor I z₁ = 0 :=
    rTensor_baseChange_eq_zero_of_red (d 2) z z₁ hred hzc
  have : Module.Flat (Λ ⧸ p) p.ResidueField :=
    IsLocalization.flat p.ResidueField (nonZeroDivisors (Λ ⧸ p))
  have : Module.Finite Λ I := Module.IsNoetherian.finite Λ I
  have : Module.Finite (Λ ⧸ p) I := Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ p) I
  obtain ⟨g₀', hg₀', hspread⟩ := exists_injVanishes_spread
    (fun i => cplx (productStructure A f) K (Λ ⧸ p) i)
    (fun i => dif (productStructure A f) K (Λ ⧸ p) i)
    (fun i => dif_comp_dif (productStructure A f) K (Λ ⧸ p) i) (Fintype.card K.ι)
    (fun _ hi => subsingleton_cplx (productStructure A f) K (Λ ⧸ p) hi)
    (finiteCohomology_dif (productStructure A f) K (Λ ⧸ p)).1
    (finiteCohomology_dif (productStructure A f) K (Λ ⧸ p)).2 z₁ hz₁c p.ResidueField hk
  obtain ⟨g₀, rfl⟩ := Ideal.Quotient.mk_surjective g₀'
  have hg₀p : g₀ ∉ p := by
    intro hmem
    apply hg₀'
    rw [Ideal.algebraMap_quotient_residueField_mk]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
  refine ⟨g₀, ⟨t, hg₀p⟩, fun g' hg' => ?_⟩
  have hu : IsUnit (algebraMap Λ (Localization.Away g') g₀) :=
    (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit).mp hg'
  refine noLargerLift_of_injVanishesRed A f K g hjQ hg L' e he hge hII p hpI _ g₀ hu ?_
  intro M _ _ hMp hbij
  let : Module (Λ ⧸ p) M := hMp.module
  have : IsScalarTower Λ (Λ ⧸ p) M := hMp.isScalarTower
  have hbij' : Function.Bijective (fun m : M => (Ideal.Quotient.mk p g₀) • m) := hbij
  have hM := hspread M hbij'
  have hMRed := (injVanishes_baseChange_iff C d hπp z₁ M).mp hM
  rw [← hred] at hMRed
  exact hMRed

end TwoAxisRigidifiedLineBundle

/-- Murre's condition (F8) holds for the two-axis class presheaf of every abelian scheme over
the spectrum of a noetherian ring. -/
theorem noetherianTwoAxisClassGenericNonLifting :
    NoetherianTwoAxisClassGenericNonLiftingStatement.{u} :=
  fun _ _ _ A ↦ TwoAxisRigidifiedLineBundle.classPresheaf_genericNonLifting A

end Langlands.AlgebraicGeometry.Picard
