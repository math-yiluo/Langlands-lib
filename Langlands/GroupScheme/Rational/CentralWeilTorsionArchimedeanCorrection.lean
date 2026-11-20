import Langlands.ClassField.Global.ArchimedeanNormPowerApproximation
import Langlands.GroupScheme.Rational.CentralNormOneArchimedeanCorrection
import Langlands.GroupScheme.Rational.CentralWeilTorsionCocycleLift

/-! # Simultaneous archimedean correction through Weil torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct CategoryTheory.MonObj NumberField.LiesOver

namespace Langlands.ClassField.Global.TensorUnitShapiro

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

variable {F B : Type u} [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M] [Algebra F M]
  [IsScalarTower F v.Completion M] [FiniteDimensional v.Completion M] [IsGalois v.Completion M]
  [IsAlgClosed M]

local notation "Kv" => InfinitePlace.Completion v

/-- A tensor-unit cocycle killed by `n` has a radical with descended `n`-th power. -/
theorem exists_archimedeanTensorRadical (n : ℕ) (c : Gal(M/Kv) → (B ⊗[F] M)ˣ)
    (hc : ∀ σ τ, c (σ * τ) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ)
    (hp : ∀ σ, c σ ^ n = 1) :
    ∃ (x : (B ⊗[F] M)ˣ) (b : (B ⊗[F] Kv)ˣ), x ^ n = extendTensorUnit M b ∧
      ∀ σ : Gal(M/Kv), tensorCoboundary x (σ.restrictScalars F) = c σ := by
  obtain ⟨x, hx⟩ := exists_archimedeanTensorCoboundary v c hc
  have hpow (σ : Gal(M/Kv)) : tensorAction F B M (σ.restrictScalars F) (x ^ n) = x ^ n := by
    apply div_eq_one.mp
    rw [map_pow, ← div_pow, hx, hp]
  let : CharZero Kv := charZero_of_injective_algebraMap (algebraMap F Kv).injective
  let e := archimedeanTensorUnitsEquiv (B := B) (M := M) v
  have hcoord (w : InfinitePlacesAbove B v) :
      ∃ y : w.1.Completionˣ, leftTensorUnit y = e (x ^ n) w := by
    apply exists_leftTensorUnit_of_fixed
    intro σ
    rw [← archimedeanTensorUnitsEquiv_action, hpow]
  choose y hy using hcoord
  let p := archimedeanCompletionUnitsEquiv (B := B) v
  refine ⟨x, p.symm y, e.injective ?_, hx⟩
  funext w
  change e (x ^ n) w = archimedeanTensorUnitsEquiv v (extendTensorUnit M (p.symm y)) w
  rw [archimedeanTensorUnitsEquiv_extend, show p (p.symm y) = y from p.apply_symm_apply y, hy]

end Langlands.ClassField.Global.TensorUnitShapiro

namespace Langlands.GroupScheme.IsCentralIsogeny

open GaloisPoint Langlands.ClassField.Global.TensorUnitShapiro

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Global

variable {F B E : Type u} [Field F] [Field B] [Field E] [Algebra F B] [Algebra F E]
  [FiniteDimensional F B] [FiniteDimensional F E] [IsGalois F E]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (n : ℕ) (e : kernel f ≅ WeilGm.weilTorsion F B n)

/-- A tensor radical of a left-factor unit gives a natural Weil torsion kernel cocycle. -/
def weilTorsionKummerKernelCocycle (b : Bˣ) {z : (B ⊗[F] E)ˣ} (hz : z ^ n = leftTensorUnit b) :
    Cocycle (kernel f) (GaloisCocycle.cover F E) := by
  let d (σ : Gal(E/F)) : GaloisCocycle.cover F E ⟶ (kernel f).X :=
    (kernelWeilTorsionEquiv n e E).symm ⟨tensorCoboundary z σ, (mem_rootsOfUnity n _).mpr (by
      rw [tensorCoboundary, div_pow, ← map_pow, hz, tensorAction_leftTensorUnit, div_self'])⟩
  let k := kernelWeilTorsionToWeil n e
  let j := kernelTensorUnitMap k E
  have hd (σ : Gal(E/F)) : j (d σ) = tensorCoboundary z σ :=
    kernelTensorUnitMap_weilTorsion_symm n e E _
  refine GaloisCocycle.ofValues d (fun σ τ => ?_)
  apply kernelTensorUnitMap_weilTorsion_injective n e
  change j (d (σ * τ)) = j (d σ * GaloisPoint.conjugate F E (kernel f) σ (d τ))
  have hσ : j (GaloisPoint.conjugate F E (kernel f) σ (d τ)) =
      tensorAction F B E σ (j (d τ)) := kernelTensorUnitMap_naturality k σ.toAlgHom (d τ)
  rw [map_mul, hσ, hd, hd, hd, mul_comm]
  exact tensorCoboundary_mul z σ τ

theorem kernelTensorUnitMap_value_weilTorsionKummerKernelCocycle
    (b : Bˣ) {z : (B ⊗[F] E)ˣ} (hz : z ^ n = leftTensorUnit b) (σ : Gal(E/F)) :
    kernelTensorUnitMap (kernelWeilTorsionToWeil n e) E
      (GaloisCocycle.value (weilTorsionKummerKernelCocycle n e b hz) σ) = tensorCoboundary z σ := by
  unfold weilTorsionKummerKernelCocycle
  rw [GaloisCocycle.value_ofValues]
  exact kernelTensorUnitMap_weilTorsion_symm n e E _

end Global

section Local

variable {F B L : Type u} [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [Normal F L]
  (v : InfinitePlace F) {M : Type u} [Field M] [Algebra v.Completion M]
  [Algebra F M] [Algebra L M] [IsScalarTower F v.Completion M] [IsScalarTower F L M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f) (n : ℕ) (e : kernel f ≅ WeilGm.weilTorsion F B n)

local notation "Kv" => InfinitePlace.Completion v

/-- The local radical and its completed power for a Weil torsion correction. -/
structure LocalWeilTorsionCorrection (ζ : Cocycle G (GaloisCocycle.cover F L)) where
  coeff : hf.LocalCentralCorrection (K := Kv) (M := M) ζ
  radicand : (B ⊗[F] Kv)ˣ
  radical : (B ⊗[F] M)ˣ
  radical_pow : radical ^ n = extendTensorUnit M radicand
  unit_eq : ∀ σ : Gal(M/Kv),
    kernelTensorUnitMap (kernelWeilTorsionToWeil n e) M (coeff.correction σ) =
      tensorCoboundary radical (σ.restrictScalars F)

theorem nonempty_localWeilTorsionCorrection [IsAlgClosed M] [FiniteDimensional v.Completion M]
    [IsGalois v.Completion M] (ζ : Cocycle G (GaloisCocycle.cover F L))
    (h : ((ζ.map f).baseChangePullback (Spec.algebraMap F Kv)).IsTrivial) :
    Nonempty (hf.LocalWeilTorsionCorrection v (M := M) n e ζ) := by
  obtain ⟨d⟩ := hf.nonempty_localCentralCorrection (K := Kv) (M := M) ζ h
  let k := kernelWeilTorsionToWeil n e
  let j := kernelTensorUnitMap k M
  let c (σ : Gal(M/Kv)) := j (d.correction σ)
  have hc (σ τ : Gal(M/Kv)) : c (σ * τ) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ := by
    change j (d.correction (σ * τ)) = tensorAction F B M (σ.restrictScalars F) (c τ) * c σ
    rw [d.correction_mul, map_mul]
    have hσ : j (relativeConjugate F Kv M hf.commutativeKernel.toGrp σ (d.correction τ)) =
        tensorAction F B M (σ.restrictScalars F) (c τ) :=
      kernelTensorUnitMap_naturality k (σ.restrictScalars F).toAlgHom (d.correction τ)
    rw [hσ, mul_comm]
  have hp (σ : Gal(M/Kv)) : c σ ^ n = 1 := kernelTensorUnitMap_weilTorsion_pow_eq_one n e M (d.correction σ)
  obtain ⟨z, b, hb, hz⟩ := exists_archimedeanTensorRadical v n c hc hp
  exact ⟨⟨d, b, z, hb, fun σ => (hz σ).symm⟩⟩

variable {E : Type u} [Field E] [Algebra F E] [Algebra L E] [Algebra E M]
  [IsScalarTower F L E] [IsScalarTower F E M] [IsScalarTower L E M]
  [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional v.Completion M] [IsGalois v.Completion M]

set_option maxHeartbeats 750000 in
/-- The power ratio in the completed tensor provides a comparison point in the kernel. -/
theorem LocalWeilTorsionCorrection.isTrivial_of_powerClass
    {ζ : Cocycle G (GaloisCocycle.cover F L)}
    (d : hf.LocalWeilTorsionCorrection v (M := M) n e ζ)
    (b : Bˣ) {x : (B ⊗[F] E)ˣ} (hx : x ^ n = leftTensorUnit b)
    (q : (B ⊗[F] Kv)ˣ) (hq : leftTensorUnit b = d.radicand * q ^ n) :
    (((ζ.refine (GaloisCocycle.coverMap F L E)).divCentral (weilTorsionKummerKernelCocycle n e b hx)
      (kernelι f) hf.isCentral_kernelι).baseChangePullback (Spec.algebraMap F Kv)).IsTrivial := by
  let α := weilTorsionKummerKernelCocycle n e b hx
  let z := extendTensorUnit M x
  let q' := extendTensorUnit M q
  let t := z / (d.radical * q')
  have hpz : z ^ n = leftTensorUnit b := calc
    _ = extendTensorUnit M (x ^ n) := (map_pow (extendTensorUnit M) _ _).symm
    _ = extendTensorUnit M (leftTensorUnit b) := congrArg (extendTensorUnit M) hx
    _ = _ := extendTensorUnit_leftTensorUnit M b
  have hq' : leftTensorUnit (F := F) (L := M) b = extendTensorUnit M d.radicand * q' ^ n := by
    calc
      _ = extendTensorUnit M (leftTensorUnit (L := Kv) b) := (extendTensorUnit_leftTensorUnit M b).symm
      _ = extendTensorUnit M (d.radicand * q ^ n) := congrArg (extendTensorUnit M) hq
      _ = _ := by rw [map_mul, map_pow]
  have htp : t ^ n = 1 := by
    change (z / (d.radical * q')) ^ n = 1
    rw [div_pow, mul_pow, hpz, d.radical_pow, hq', div_self']
  let t' : rootsOfUnity n (B ⊗[F] M) := ⟨t, (mem_rootsOfUnity n t).mpr htp⟩
  let c := (kernelWeilTorsionEquiv n e M).symm t'
  let k := kernelWeilTorsionToWeil n e
  let j := kernelTensorUnitMap k M
  have hct : j c = t := kernelTensorUnitMap_weilTorsion_symm n e M t'
  apply LocalCentralCorrection.isTrivial_of_coboundaryRatio (K := Kv) (M := M) hf d.coeff α c
  intro σ
  let ρ := (σ.restrictScalars F).restrictNormal E
  let D := relativeExtend F E M (kernel f) (GaloisCocycle.value α ρ)
  let dσ : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F M) := d.coeff.correction σ
  have hD : j D = tensorCoboundary z (σ.restrictScalars F) := by
    change kernelTensorUnitMap k M (GroupScheme.affinePointMap (kernel f)
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom F E M)) (GaloisCocycle.value α ρ)) = _
    rw [kernelTensorUnitMap_naturality k (IsScalarTower.toAlgHom F E M),
      kernelTensorUnitMap_value_weilTorsionKummerKernelCocycle n e]
    simp only [tensorCoboundary, z, map_div]
    rw [extendTensorUnit_action]
    rfl
  apply kernelTensorUnitMap_weilTorsion_injective n e
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

end Local

variable {F B L : Type u} [Field F] [Field B] [Field L] [NumberField F] [NumberField B]
  [Algebra F B] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f) (n : ℕ) (e : kernel f ≅ WeilGm.weilTorsion F B n)

include e in
set_option maxHeartbeats 900000 in
/-- One global Weil torsion kernel cocycle makes all infinite pullbacks trivial on
a finite Galois refinement of a lift whose projection is archimedean trivial. -/
theorem hasArchimedeanCentralCorrection_of_weilTorsionKernel
    (hn : 0 < n) (ζ : Cocycle G (GaloisCocycle.cover F L)) (h : (ζ.map f).ArchimedeanTrivial) :
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
    Classical.choice (hf.nonempty_localWeilTorsionCorrection v (M := M v) n e ζ (h v))
  obtain ⟨b, hb⟩ := exists_approximateCompletionTensorUnits hn (fun v => (d v).radicand)
  obtain ⟨D, _, _, _, _, _, _, _, _⟩ := exists_finiteGalois_refinement_with_algebra F B L
  obtain ⟨E, _, _, _, _, _, _, z, hz⟩ :=
    exists_tensorUnit_root n hn.ne' (leftTensorUnit (F := F) (L := D) b)
  let : Algebra L E := Algebra.compHom E (algebraMap L D)
  let : IsScalarTower L D E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F D E, IsScalarTower.algebraMap_apply L D E,
      ← IsScalarTower.algebraMap_apply F L D]
  let : FiniteDimensional L E := FiniteDimensional.right F L E
  have hz' : z ^ n = leftTensorUnit b := hz.trans (extendTensorUnit_leftTensorUnit E b)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, weilTorsionKummerKernelCocycle n e b hz', ?_⟩
  intro v
  let jE : E →ₐ[L] M v := IsAlgClosed.lift
  let : Algebra E (M v) := jE.toRingHom.toAlgebra
  let : IsScalarTower L E (M v) := IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm
  let : IsScalarTower F E (M v) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F L E, ← IsScalarTower.algebraMap_apply L E (M v),
      IsScalarTower.algebraMap_apply F L (M v)]
  obtain ⟨q, hq⟩ := hb v
  exact LocalWeilTorsionCorrection.isTrivial_of_powerClass v hf n e (d v) b hz' q hq

end Langlands.GroupScheme.IsCentralIsogeny
