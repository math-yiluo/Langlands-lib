import Langlands.BaseChange.NormNeighbourhoodStatement
import Langlands.BaseChange.NormPolynomialPerturbation
import Langlands.BaseChange.RegularMatrixSlice
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedDegree
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Norm neighbourhoods in the general linear group

The power map near the identity, regular elliptic accumulation from a finite unramified
extension, and a local conjugation argument prove `NormNeighbourhoodStatement`.
-/

noncomputable section

open Filter Matrix Polynomial Set Topology
open scoped Matrix.Norms.Operator Topology RightActions IntermediateField Ring

namespace Langlands.BaseChange

universe u v

private theorem hasStrictFDerivAt_pow_one {F R : Type*} [NontriviallyNormedField F]
    [NormedRing R] [NormedAlgebra F R] (l : ℕ) :
    HasStrictFDerivAt (fun r : R => r ^ l)
      ((l : F) • ContinuousLinearMap.id F R) 1 := by
  have h := hasStrictFDerivAt_pow' (𝕜 := F) (𝔸 := R) l (x := 1)
  simp only [one_pow, one_smul, Finset.sum_const, Finset.card_range] at h
  convert h using 1
  ext x
  simp [Nat.cast_smul_eq_nsmul]

private theorem eventually_isPow {F R : Type*} [NontriviallyNormedField F] [CharZero F]
    [NormedRing R] [NormedAlgebra F R] [CompleteSpace R] {l : ℕ} (hl : 0 < l) :
    ∀ᶠ g : Rˣ in 𝓝 1, ∃ r : Rˣ, r ^ l = g := by
  have hmap := (hasStrictFDerivAt_pow_one (F := F) (R := R) l).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr (fun y => ⟨(l : F)⁻¹ • y, by
      have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      simp [smul_smul, hl']⟩))
  rw [one_pow] at hmap
  have hu : {r : R | IsUnit r} ∈ 𝓝 1 := Units.isOpen.mem_nhds isUnit_one
  have h : (fun r : R => r ^ l) '' {r : R | IsUnit r} ∈
      map (fun r : R => r ^ l) (𝓝 1) := image_mem_map hu
  rw [hmap] at h
  have hval : Tendsto (Units.val : Rˣ → R) (𝓝 1) (𝓝 1) := Units.continuous_val.continuousAt
  filter_upwards [hval.eventually h] with g hg
  obtain ⟨r, hr, heq⟩ := hg
  exact ⟨hr.unit, Units.ext (by simpa only [Units.val_pow_eq_pow_val, hr.unit_spec] using heq)⟩

private theorem hasStrictFDerivAt_conj_mul_pow {F R P : Type*} [NontriviallyNormedField F]
    [NormedRing R] [NormedAlgebra F R] [HasSummableGeomSeries R]
    [NormedAddCommGroup P] [NormedSpace F P] (A : R) (l : ℕ)
    (G C : P →L[F] R) (x₀ : P) (hG₀ : G x₀ = 1) (hS₀ : 1 + C x₀ = 1) :
    HasStrictFDerivAt (fun x => G x * A * (1 + C x) ^ l * Ring.inverse (G x))
      ((G <• A) - A • G + A • ((l : F) • C)) x₀ := by
  have hpow : HasStrictFDerivAt (fun x => (1 + C x) ^ l) ((l : F) • C) x₀ := by
    have houter : HasStrictFDerivAt (fun r : R => r ^ l)
        ((l : F) • ContinuousLinearMap.id F R) (1 + C x₀) := by
      rw [hS₀]
      exact hasStrictFDerivAt_pow_one l
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp] using
      houter.comp x₀ (C.hasStrictFDerivAt.const_add (c := (1 : R)))
  have hinv : HasStrictFDerivAt (fun x => Ring.inverse (G x)) (-G) x₀ := by
    have houter : HasStrictFDerivAt (Ring.inverse : R → R) (-ContinuousLinearMap.id F R)
        (G x₀) := by
      rw [hG₀]
      convert hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ) using 1
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.mulLeftRight_apply]
    simpa only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.id_comp] using
      houter.comp x₀ G.hasStrictFDerivAt
  convert ((G.hasStrictFDerivAt.mul_const' A).mul' hpow).mul' hinv using 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [Pi.mul_apply, hG₀, hS₀, one_mul, one_pow, Ring.inverse_one, _root_.smul_apply,
    _root_.add_apply, _root_.sub_apply, _root_.neg_apply, smul_eq_mul, op_smul_eq_mul, mul_one]
  noncomm_ring

private theorem eventually_conj_mul_pow {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] {n l : ℕ} (hl : 0 < l) (γ₀ : GeneralLinear n F)
    (hγ₀ : JacquetLanglands.IsRegularSemisimple γ₀) :
    ∀ᶠ γ in 𝓝 γ₀, ∃ (g s : GeneralLinear n F) (c : Fin n → F),
      s.val = 1 + ∑ i : Fin n, c i • γ₀.val ^ (i : ℕ) ∧
      γ = g * γ₀ * s ^ l * g⁻¹ := by
  let M := Matrix (Fin n) (Fin n) F
  let P := M × (Fin n → F)
  have : CompleteSpace M := inferInstanceAs (CompleteSpace (Fin n → Fin n → F))
  let A : M := γ₀.val
  let x₀ : P := (1, 0)
  let L : (Fin n → F) →L[F] M :=
    ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (A ^ (i : ℕ))
  have hL (c : Fin n → F) : L c = ∑ i : Fin n, c i • A ^ (i : ℕ) := by
    simp [L]
  let G : P →L[F] M := ContinuousLinearMap.fst F M (Fin n → F)
  let C : P →L[F] M := L.comp (ContinuousLinearMap.snd F M (Fin n → F))
  have hG₀ : G x₀ = 1 := rfl
  have hS₀ : 1 + C x₀ = 1 := by
    change (1 : M) + L 0 = 1
    simp
  let f : P → M := fun x => G x * A * (1 + C x) ^ l * Ring.inverse (G x)
  let D : P →L[F] M := (G <• A) - A • G + A • ((l : F) • C)
  have hD (x : P) :
      D x = x.1 * A - A * x.1 + A * ((l : F) • ∑ i : Fin n, x.2 i • A ^ (i : ℕ)) := by
    change x.1 * A - A * x.1 + A * ((l : F) • L x.2) = _
    rw [hL]
  have hf : HasStrictFDerivAt f D x₀ := hasStrictFDerivAt_conj_mul_pow A l G C x₀ hG₀ hS₀
  have hsurj : D.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro Y
    obtain ⟨Z, c, hZ⟩ := exists_commutator_add_powers A hγ₀ ((γ₀⁻¹ : GeneralLinear n F).val * Y)
    refine ⟨(A * Z, fun i => (l : F)⁻¹ • c i), ?_⟩
    have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    have hcoeff :
        (l : F) • (∑ i : Fin n, ((l : F)⁻¹ • c i) • A ^ (i : ℕ)) =
          ∑ i : Fin n, c i • A ^ (i : ℕ) := by
      rw [Finset.smul_sum]
      simp [smul_smul, hl']
    have hAinv : A * (γ₀⁻¹ : GeneralLinear n F).val = 1 :=
      congrArg Units.val (mul_inv_cancel γ₀)
    change D (A * Z, fun i => (l : F)⁻¹ • c i) = Y
    rw [hD, hcoeff, mul_assoc A Z A, ← mul_sub, ← mul_add, hZ, ← mul_assoc, hAinv, one_mul]
  let W : Set P := {x | IsUnit (G x) ∧ IsUnit (1 + C x)}
  have hWopen : IsOpen W := (Units.isOpen.preimage G.continuous).inter
    (Units.isOpen.preimage (continuous_const.add C.continuous))
  have hW : W ∈ 𝓝 x₀ := hWopen.mem_nhds (by
    change IsUnit (G x₀) ∧ IsUnit (1 + C x₀)
    rw [hG₀, hS₀]
    exact ⟨isUnit_one, isUnit_one⟩)
  have hfx₀ : f x₀ = A := by simp [f, hG₀, hS₀, Ring.inverse_one]
  have hmap : map f (𝓝 x₀) = 𝓝 (f x₀) := hf.map_nhds_eq_of_surj hsurj
  have himage : f '' W ∈ map f (𝓝 x₀) := image_mem_map hW
  rw [hmap, hfx₀] at himage
  have hval : Tendsto (Units.val : GeneralLinear n F → M) (𝓝 γ₀) (𝓝 A) :=
    Units.continuous_val.continuousAt
  filter_upwards [hval.eventually himage] with γ hγ
  obtain ⟨⟨m, c⟩, ⟨hg, hs⟩, he⟩ := hγ
  refine ⟨hg.unit, hs.unit, c, ?_, ?_⟩
  · change hs.unit.val = 1 + ∑ i : Fin n, c i • A ^ (i : ℕ)
    rw [← hL]
    exact hs.unit_spec
  · apply Units.ext
    change γ.val = hg.unit.val * A * hs.unit.val ^ l * (hg.unit⁻¹ : Mˣ).val
    rw [← Ring.inverse_unit hg.unit, hg.unit_spec, hs.unit_spec]
    exact he.symm

private theorem isOpen_regularSemisimple {F : Type*} [Field F] [CharZero F]
    [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] (n : ℕ) :
    IsOpen {g : GeneralLinear n F | JacquetLanglands.IsRegularSemisimple g} := by
  let p := Matrix.charpoly.univ F (Fin n)
  let D := p.resultant p.derivative n (n - 1)
  let m : GeneralLinear n F → Fin n × Fin n → F := fun g ij => g ij.1 ij.2
  have hm : Continuous m := continuous_pi fun ij => (GeneralLinear.entry ij.1 ij.2).continuous
  have hD (g : GeneralLinear n F) :
      MvPolynomial.eval (m g) D = (g.val.charpoly).resultant g.val.charpoly.derivative := by
    let ev := MvPolynomial.eval₂Hom (RingHom.id F) (m g)
    have hp : p.map ev = g.val.charpoly := by
      exact Matrix.charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id F) (m g)
    change ev (p.resultant p.derivative n (n - 1)) = _
    rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map, hp]
    simp [Polynomial.natDegree_derivative, Matrix.charpoly_natDegree_eq_dim]
  have heq : {g : GeneralLinear n F | JacquetLanglands.IsRegularSemisimple g} =
      (fun g => MvPolynomial.eval (m g) D) ⁻¹' {0}ᶜ := by
    ext g
    change g.val.charpoly.Separable ↔ MvPolynomial.eval (m g) D ≠ 0
    rw [hD, ← isUnit_iff_ne_zero, Polynomial.isUnit_resultant_iff_isCoprime g.val.charpoly_monic]
    rfl
  rw [heq]
  exact isClosed_singleton.isOpen_compl.preimage (D.continuous_eval.comp hm)

private theorem exists_regularElliptic_mem {F L : Type*} [NontriviallyNormedField F]
    [CompleteSpace F] [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {n : ℕ} (hdim : Module.finrank F L = n)
    {U : Set (GeneralLinear n F)} (hU : U ∈ 𝓝 1) :
    ∃ g ∈ U, JacquetLanglands.IsRegularElliptic g := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F L
  let b := Module.finBasisOfFinrankEq F L hdim
  let ρ := Algebra.leftMulMatrix b
  let f : F → Matrix (Fin n) (Fin n) F := fun t => 1 + t • ρ α
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hU' : (Units.val : GeneralLinear n F → _) '' U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) F) := by
    have : CompleteSpace (Matrix (Fin n) (Fin n) F) :=
      inferInstanceAs (CompleteSpace (Fin n → Fin n → F))
    have hval : IsOpenEmbedding (Units.val : GeneralLinear n F → _) := Units.isOpenEmbedding_val
    change _ ∈ 𝓝 (1 : GeneralLinear n F).val
    rw [← hval.map_nhds_eq (1 : GeneralLinear n F)]
    exact image_mem_map hU
  have hf' : Tendsto f (𝓝[≠] 0) (𝓝 1) := by
    simpa [f] using hf.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : F) ≤ 𝓝 0)
  have hnonzero : ∀ᶠ t : F in 𝓝[≠] 0, t ≠ 0 :=
    eventually_mem_nhdsWithin (s := {0}ᶜ)
  obtain ⟨t, ht, g, hg, hgt⟩ := (hnonzero.and (hf'.eventually hU')).exists
  let a : L := 1 + t • α
  have ha : F⟮a⟯ = ⊤ := by
    change F⟮1 + t • α⟯ = ⊤
    rw [add_comm 1, Algebra.smul_def, mul_comm (algebraMap F L t), ← map_one (algebraMap F L),
      IntermediateField.adjoin_simple_add_algebraMap,
      IntermediateField.adjoin_simple_mul_algebraMap _ _ ht]
    exact hα
  have hgρ : g.val = ρ a := by simpa [f, a, map_add, map_smul] using hgt
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  have hdeg : (minpoly F a).natDegree = n := by
    rw [← IntermediateField.adjoin.finrank hint, ha, IntermediateField.finrank_top', hdim]
  have hdiv : minpoly F a ∣ g.val.charpoly := by
    apply minpoly.dvd
    apply Algebra.leftMulMatrix_injective b
    rw [map_zero, ← Polynomial.aeval_algHom_apply, ← hgρ, Matrix.aeval_self_charpoly]
  have hchar : g.val.charpoly = minpoly F a := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) g.val.charpoly_monic hdiv
    simp [hdeg, Matrix.charpoly_natDegree_eq_dim]
  refine ⟨g, hg, ?_⟩
  change g.val.charpoly.Separable ∧ Irreducible g.val.charpoly
  rw [hchar]
  exact ⟨Algebra.IsSeparable.isSeparable F a, minpoly.irreducible hint⟩

/-- The norm neighbourhood, regular elliptic accumulation, and openness assertions of
`NormNeighbourhoodStatement`. -/
theorem normNeighbourhood : NormNeighbourhoodStatement.{u, v} := by
  intro F _ _ _ _ _ n
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  have : CompleteSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → F))
  refine ⟨?_, ?_⟩
  · intro hn U hU
    exact exists_regularElliptic_mem
      (ClassFieldTheory.Local.finiteUnramifiedFieldOfDegree_finrank F n hn) hU
  · intro E _ _ _ _ _ σ l hcyc
    refine ⟨?_, ?_⟩
    · let V : Set (GeneralLinear n F) := {γ | ∃ r : GeneralLinear n F, r ^ l = γ}
      have hV : V ∈ 𝓝 1 := eventually_isPow (F := F) hcyc.pos
      refine ⟨V, hV, ?_⟩
      rintro γ ⟨r, rfl⟩
      exact isNorm_pow σ l r
    · rw [isOpen_iff_mem_nhds]
      intro γ₀ hγ₀
      have hregular : ∀ᶠ γ in 𝓝 γ₀, JacquetLanglands.IsRegularSemisimple γ :=
        (isOpen_regularSemisimple (F := F) n).mem_nhds hγ₀.1
      have hconj := eventually_conj_mul_pow hcyc.pos γ₀ hγ₀.1
      change ∀ᶠ γ in 𝓝 γ₀, JacquetLanglands.IsRegularSemisimple γ ∧ IsNorm σ l γ
      filter_upwards [hregular, hconj] with γ hreg hγ
      obtain ⟨g, s, c, hs, rfl⟩ := hγ
      exact ⟨hreg, IsNorm.conj_mul_pow_of_polynomial hγ₀.2 hcyc.pow_eq_one g s c hs⟩

end Langlands.BaseChange
