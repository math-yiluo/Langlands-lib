import Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingClassStatement
import Langlands.Algebra.CentralSimple.NumberFieldUnitarySymmetricCofinite
import Langlands.Algebra.CentralSimple.UnitaryEmbeddingFixedField
import Langlands.Algebra.CentralSimple.UnitaryEmbeddingTwist
import Langlands.Algebra.CentralSimple.UnitaryEmbeddingNormObstruction
import Langlands.ClassFieldTheory.Global.PrescribedTensorNormClasses

/-! # Global fixed-field twists with everywhere local unitary solutions -/

noncomputable section

open scoped TensorProduct
open Filter

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Global.TensorUnitShapiro
open Langlands.Global (Place FinitePlace placeCompletion)

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem quadratic_isAbelianGalois (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] : IsAbelianGalois F E := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card (p := 2) (by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E])
  exact IsAbelianGalois.of_isCyclic F E

section Transfer

variable {F P : Type u} [Field F] [Field P] [Algebra F P]
  (σ : FirstKindInvolution F P)

private def fixedFieldAut : P ≃ₐ[unitaryEmbeddingFixedField σ] P where
  toFun := σ
  invFun := σ
  left_inv := σ.apply_apply
  right_inv := σ.apply_apply
  map_mul' a b := (σ.map_mul a b).trans (mul_comm _ _)
  map_add' := σ.map_add
  commutes' k := (mem_unitaryEmbeddingFixedField σ _).mp k.2

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem exists_norm_factor {K : Type u} [Field K] [Algebra F K] [Algebra K P]
    [IsScalarTower F K P] [Algebra.IsQuadraticExtension K P] [Algebra.IsSeparable K P]
    (hconj : ∀ y : P, conjugation K P y = σ y)
    (R : Type u) [CommRing R] [Algebra F R] (x : K) (a : (R ⊗[F] K)ˣ)
    (z : ((K ⊗[F] R) ⊗[K] P)ˣ)
    (hz : x ⊗ₜ[F] (1 : R) = Algebra.TensorProduct.comm F R K (a : R ⊗[F] K) *
      Algebra.norm (K ⊗[F] R) (z : (K ⊗[F] R) ⊗[K] P)) :
    ∃ p : (R ⊗[F] P)ˣ, (1 : R) ⊗ₜ[F] algebraMap K P x =
      Algebra.TensorProduct.map (AlgHom.id R R) (IsScalarTower.toAlgHom F K P) a *
      ((p : R ⊗[F] P) * σ.baseChange R p) := by
  let S := K ⊗[F] R
  let T := S ⊗[K] P
  let e := UnitaryPoints.tensorEquiv F K P R
  let j : S →ₐ[S] T := Algebra.TensorProduct.includeLeft
  let c := tensorConjugation K P S
  let i : R ⊗[F] K →ₐ[R] R ⊗[F] P :=
    Algebra.TensorProduct.map (AlgHom.id R R) (IsScalarTower.toAlgHom F K P)
  let p := Units.map e.symm.toMonoidHom z
  have hbar (y : R ⊗[F] P) : e (σ.baseChange R y) = c (e y) := by
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      change ((1 : K) ⊗ₜ[F] r) ⊗ₜ[K] σ y = ((1 : K) ⊗ₜ[F] r) ⊗ₜ[K] conjugation K P y
      rw [hconj]
    | add y t hy ht => simp only [map_add, hy, ht]
  have hcoef (y : R ⊗[F] K) : e (i y) = j (Algebra.TensorProduct.comm F R K y) := by
    induction y using TensorProduct.inductionOn with
    | tmul r k =>
      change ((1 : K) ⊗ₜ[F] r) ⊗ₜ[K] algebraMap K P k = (k ⊗ₜ[F] r) ⊗ₜ[K] (1 : P)
      rw [Algebra.algebraMap_eq_smul_one (R := K) (A := P), ← TensorProduct.smul_tmul]
      congr 1
      simp [TensorProduct.smul_tmul', smul_eq_mul]
    | add y t hy ht => simp only [map_add, hy, ht]
  have hn : j (Algebra.norm S (z : T)) = (z : T) * c z := by
    let s := Algebra.TensorProduct.comm K S P
    let w := s (z : T)
    have hn' := includeRight_tensorNorm_quadratic w
    have hw : s.symm w = (z : T) := s.symm_apply_apply z
    have hq : s.symm (quadraticTensorConjugation w) = c z := by
      change s.symm (s (c (s.symm w))) = _
      rw [s.symm_apply_apply, hw]
    have hr := congrArg s.symm hn'
    change s.symm ((1 : P) ⊗ₜ[K] Algebra.norm S (s.symm w)) =
      s.symm (w * quadraticTensorConjugation w) at hr
    rw [map_mul, hw, hq] at hr
    exact hr
  refine ⟨p, e.injective ?_⟩
  change e (i ((1 : R) ⊗ₜ[F] x)) = e (i (a : R ⊗[F] K) * ((p : R ⊗[F] P) * σ.baseChange R p))
  simp only [map_mul, hbar, hcoef, Algebra.TensorProduct.comm_tmul]
  have hp : e (p : R ⊗[F] P) = (z : T) := e.apply_symm_apply _
  rw [hp, ← hn, ← map_mul, hz]

end Transfer

/-- Realize the local unitary twist equations by one global fixed-field element. -/
theorem numberFieldUnitaryEmbeddingClass : NumberFieldUnitaryEmbeddingClassStatement.{u} := by
  classical
  intro F E B P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ σ hτ hσ hdim ε g hg hε hlocal
  let K := unitaryEmbeddingFixedField σ
  let : FiniteDimensional F E := .of_finrank_pos (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]
    decide)
  let : FiniteDimensional F P := Module.Finite.trans E P
  let : NumberField E := NumberField.of_module_finite F E
  let : NumberField P := NumberField.of_module_finite F P
  let : NumberField K := NumberField.of_module_finite F K
  have hne : ∃ y : P, σ y ≠ y := by
    by_contra! h
    apply conjugation_ne_one F E
    ext e
    exact (algebraMap E P).injective ((hσ e).symm.trans (h _))
  let : Algebra.IsQuadraticExtension K P := ⟨unitaryEmbeddingFixedField_finrank σ hne⟩
  let : IsAbelianGalois F E := quadratic_isAbelianGalois F E
  let : IsAbelianGalois K P := quadratic_isAbelianGalois K P
  let e := unitaryEmbeddingFixedFieldTensorEquiv σ hσ
  have he (k : K) : e ((1 : E) ⊗ₜ[F] k) = K.val k := by
    rw [unitaryEmbeddingFixedFieldTensorEquiv_tmul, map_one, one_mul]
    rfl
  let ρ : (P ≃ₐ[K] P) →* (E ≃ₐ[F] E) :=
    (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)
  have hρ : ρ (fixedFieldAut σ) = conjugation F E := by
    ext e
    apply (algebraMap E P).injective
    exact (AlgEquiv.restrictNormal_commutes ((fixedFieldAut σ).restrictScalars F) E e).trans (hσ e)
  have hσ₁ : fixedFieldAut σ ≠ 1 := by
    intro h
    exact conjugation_ne_one F E (hρ.symm.trans (by rw [h, map_one]))
  have hconj : conjugation K P = fixedFieldAut σ := (conjugation_unique K P _ hσ₁).symm
  have hρinj : Function.Injective ρ := (injective_iff_map_eq_one ρ).mpr (by
    intro s hs
    by_contra hs₁
    rw [conjugation_unique K P s hs₁, hconj, hρ] at hs
    exact conjugation_ne_one F E hs)
  let R (v : Place F) := placeCompletion F v
  let εv (v : Place F) : R v ⊗[F] P →ₐ[R v] R v ⊗[F] B :=
    Algebra.TensorProduct.map (AlgHom.id (R v) (R v)) (ε.restrictScalars F)
  let g₁ (v : Place F) : (R v ⊗[F] B)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] R v ⊗[F] B).toMonoidHom g
  let U (v : Place F) (a : (R v ⊗[F] K)ˣ) := ∃ h : (R v ⊗[F] B)ˣ,
    (g₁ v : R v ⊗[F] B) * εv v (unitaryEmbeddingFixedInclusion σ (R v) a) =
      (h : R v ⊗[F] B) * τ.baseChange (R v) h
  have hsol (v : Place F) : ∃ a, U v a ∧ (U v 1 → a = 1) := by
    by_cases h : U v 1
    · exact ⟨1, h, fun _ => rfl⟩
    · obtain ⟨av, hav, w, hw⟩ := hlocal v
      obtain ⟨a, ha⟩ := exists_unitaryEmbeddingFixedInclusion_unit σ (R v) av hav
      refine ⟨a, ⟨w, ?_⟩, fun un => (h un).elim⟩
      change (g₁ v : R v ⊗[F] B) * εv v
        (↑(Units.map (unitaryEmbeddingFixedInclusion σ (R v)).toMonoidHom a) : R v ⊗[F] P) = _
      rw [ha]
      exact hw
  choose a hU hOne using hsol
  have ha : ∀ᶠ v : FinitePlace F in cofinite, a (.inr v) = 1 := by
    filter_upwards [numberFieldUnitarySymmetricCofinite F E B τ hτ g hg] with v hv
    apply hOne (.inr v)
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, ?_⟩
    let f := (εv (.inr v)).comp (unitaryEmbeddingFixedInclusion σ (R (.inr v)))
    change (g₁ (.inr v) : R (.inr v) ⊗[F] B) * f 1 = _
    exact (congrArg ((g₁ (.inr v) : R (.inr v) ⊗[F] B) * ·) f.map_one).trans
      ((mul_one _).trans hw)
  have hcomp (v : Place F) (b : R v ⊗[F] K) :
      εv v (unitaryEmbeddingFixedInclusion σ (R v) b) =
      Algebra.TensorProduct.map (AlgHom.id (R v) (R v)) ((ε.restrictScalars F).comp K.val) b := by
    induction b using TensorProduct.inductionOn with
    | tmul r k => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨d, _, hd⟩ := unitaryEmbeddingNormObstruction F E B K P τ hτ hdim ε e K.val he g hg
  have hnorm (v : Place F) : ∃ b : (R v ⊗[F] E)ˣ,
      Algebra.norm (R v) (b : R v ⊗[F] E) =
        algebraMap F (R v) (d : F) * Algebra.norm (R v) (a v : R v ⊗[F] K) := by
    obtain ⟨w, hw⟩ := hU v
    rw [hcomp] at hw
    obtain ⟨b, hb⟩ := hd (R v) (a v) w hw
    exact ⟨Units.map (Algebra.TensorProduct.comm F E (R v)).toMonoidHom b, hb⟩
  obtain ⟨x, hx⟩ := prescribedTensorNormClasses F E K P hρinj d a ha hnorm
  refine ⟨(x : K), (algebraMap K P).injective.ne (Units.ne_zero x),
    (mem_unitaryEmbeddingFixedField σ _).mp (x : K).2, ?_⟩
  intro v
  obtain ⟨z, hz⟩ := hx v
  obtain ⟨q, hq⟩ := exists_norm_factor (K := K) σ (fun y => DFunLike.congr_fun hconj y)
    (R v) (x : K) (a v) z hz
  change (1 : R v) ⊗ₜ[F] ((x : K) : P) = unitaryEmbeddingFixedInclusion σ (R v) (a v) *
    ((q : R v ⊗[F] P) * σ.baseChange (R v) q) at hq
  obtain ⟨w, hw⟩ := hU v
  have htw := unitaryEmbeddingTwist_baseChange (R := R v) σ τ (ε.restrictScalars F) g hε
  obtain ⟨h, hh⟩ := exists_unitarySolution_mul_norm (σ.baseChange (R v))
    (τ.baseChange (R v)) (εv v) (g₁ v) htw hw q
  refine ⟨h, ?_⟩
  rw [← hh, ← hq]
  change _ = ((1 : R v) ⊗ₜ[F] (g : B)) *
    Algebra.TensorProduct.map (AlgHom.id (R v) (R v)) (ε.restrictScalars F)
      ((1 : R v) ⊗ₜ[F] ((x : K) : P))
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

end Langlands.CentralSimple
