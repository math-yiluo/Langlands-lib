import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus

/-! # Generic smoothness of geometrically integral fibres

Let `S` be a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every field
`K` over `R`. Then every prime `p` of `R` is the image of a point of the smooth locus of `S`: the
generic point of the fibre over `p`. -/

universe u

open TensorProduct IsLocalRing

namespace Langlands.CommutativeAlgebra

section Field

/-- Let `k` be a field of characteristic `p` and `T` a `k`-algebra such that
`AlgebraicClosure k ⊗[k] T` is reduced. Then `p`-th powers of `k`-linearly independent elements
of `T` are `k`-linearly independent. -/
theorem linearIndependent_pow_of_isReduced_tensor {k T : Type*} [Field k] [CommRing T]
    [Algebra k T] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    [IsReduced (AlgebraicClosure k ⊗[k] T)] {ι : Type*} [Fintype ι] {t : ι → T}
    (ht : LinearIndependent k t) : LinearIndependent k (fun i ↦ t i ^ p) := by
  classical
  set K := AlgebraicClosure k
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun j ↦ IsAlgClosed.exists_pow_nat_eq (algebraMap k K (g j)) hp.out.pos
  have hx : ∑ j, b j ⊗ₜ[k] t j = 0 := by
    rcases subsingleton_or_nontrivial (K ⊗[k] T) with _ | _
    · exact Subsingleton.elim _ _
    have : CharP (K ⊗[k] T) p := charP_of_injective_algebraMap (algebraMap k _).injective p
    have : ExpChar (K ⊗[k] T) p := ExpChar.prime hp.out
    refine IsReduced.eq_zero _ ⟨p, ?_⟩
    rw [sum_pow_char]
    simp_rw [Algebra.TensorProduct.tmul_pow, hb, Algebra.algebraMap_eq_smul_one, smul_tmul,
      ← tmul_sum, hg, tmul_zero]
  have hlin := Module.Flat.linearIndependent_one_tmul (S := K) ht
  rw [Fintype.linearIndependent_iff] at hlin
  have hbi : b i = 0 := hlin b (by simpa [smul_tmul', smul_eq_mul] using hx) i
  have := hb i
  rw [hbi, zero_pow hp.out.ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap k K).injective] at this
  exact this

/-- Let `T` be a finite type domain over a field `k` such that `AlgebraicClosure k ⊗[k] T` is
reduced. Then the fraction field of `T` is formally smooth over `k`. -/
theorem formallySmooth_of_isFractionRing {k T L : Type*} [Field k] [CommRing T] [IsDomain T]
    [Algebra k T] [Algebra.FiniteType k T] [Field L] [Algebra T L] [IsFractionRing T L]
    [Algebra k L] [IsScalarTower k T L] [IsReduced (AlgebraicClosure k ⊗[k] T)] :
    Algebra.FormallySmooth k L := by
  have : Algebra.EssFiniteType T L := .of_isLocalization L (nonZeroDivisors T)
  have : Algebra.EssFiniteType k L := .comp k T L
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · infer_instance
  have : ExpChar k p := .prime hp.out
  -- Clear denominators and use `linearIndependent_pow_of_isReduced_tensor` in `T`.
  have H (s : Finset L) (hs : LinearIndepOn k id (s : Set L)) :
      LinearIndepOn k (· ^ p) (s : Set L) := by
    obtain ⟨⟨d, hd⟩, hdint⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T) s
    choose t ht using fun a : s ↦ hdint a a.2
    have hd₀ : algebraMap T L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    let f := IsScalarTower.toAlgHom k T L
    have hf : Function.Injective f := IsFractionRing.injective T L
    have hft : ∀ a, f (t a) = algebraMap T L d * a := fun a ↦ by
      simp [f, ht, Algebra.smul_def]
    have hmul : ∀ c : L, c ≠ 0 → LinearMap.ker (LinearMap.mulLeft k c) = ⊥ := fun c hc ↦
      LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hc)
    have h₁ : LinearIndependent k t := by
      apply LinearIndependent.of_comp f.toLinearMap
      convert! (hs : LinearIndependent k fun a : s ↦ (a : L)).map' _
        (hmul _ hd₀) using 1
      ext a
      simp [hft]
    have h₂ := linearIndependent_pow_of_isReduced_tensor p h₁
    change LinearIndependent k fun a : s ↦ (a : L) ^ p
    apply LinearIndependent.of_comp (LinearMap.mulLeft k (algebraMap T L d ^ p))
    convert! h₂.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr hf) using 1
    ext a
    simp [hft, mul_pow]
  obtain ⟨s, hs, H'⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := k) (K := L) p hp.out H
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → L))) L := by
    convert! H' <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1

end Field

section Fibre

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

local notation "𝓀[" R "]" => ResidueField R

set_option backward.isDefEq.respectTransparency false in
/-- Let `S` be a flat finitely presented `R`-algebra, `p` a prime of `R` and `Q` a prime of the
fibre `p.Fiber S = κ(p) ⊗[R] S`. If the localization of the fibre at `Q` is formally smooth over
`κ(p)`, then `S` is smooth over `R` at the prime of `S` below `Q`. -/
theorem isSmoothAt_of_formallySmooth_localization_fiber [Module.Flat R S]
    [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S))
    [Q.IsPrime] [Algebra.FormallySmooth p.ResidueField (Localization.AtPrime Q)] :
    Algebra.IsSmoothAt R (Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)) := by
  set q := Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Algebra.FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) := by
    let e₁ : Localization.AtPrime Q ≃ₐ[Rp] Sq ⧸ p.map (algebraMap R Sq) :=
      Ideal.Fiber.localizationAlgEquivQuotient p Q
    let e₂ : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Rp]
        Sq ⧸ (maximalIdeal Rp).map (algebraMap Rp Sq) :=
      Ideal.quotientEquivAlgOfEq Rp <| by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq]
    let e₃ : (Sq ⧸ (maximalIdeal Rp).map (algebraMap Rp Sq)) ≃ₐ[Rp] 𝓀[Rp] ⊗[Rp] Sq :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sq
        (maximalIdeal Rp)).restrictScalars Rp).trans (Algebra.TensorProduct.comm _ _ _)
    let e : Localization.AtPrime Q ≃ₐ[𝓀[Rp]] 𝓀[Rp] ⊗[Rp] Sq :=
      AlgEquiv.extendScalarsOfSurjective residue_surjective ((e₁.trans e₂).trans e₃)
    exact Algebra.FormallySmooth.of_equiv (A := Localization.AtPrime Q) e
  have := Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

end Fibre

/-- **Generic smoothness.** Let `S` be a flat finitely presented `R`-algebra such that
`K ⊗[R] S` is a domain for every field `K` over `R`. Then every prime of `R` is the image of a
point of the smooth locus of `S` (the generic point of its fibre). -/
theorem exists_mem_smoothLocus_comap_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hS : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] S)) (p : PrimeSpectrum R) :
    ∃ q ∈ Algebra.smoothLocus R S, PrimeSpectrum.comap (algebraMap R S) q = p := by
  let k := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber S
  have : IsDomain T := hS k
  let Q : Ideal T := ⊥
  have : Q.IsPrime := Ideal.isPrime_bot
  have : IsFractionRing T (Localization.AtPrime Q) := by
    simpa [Q, Ideal.primeCompl_bot] using Localization.isLocalization (M := Q.primeCompl)
  let : Field (Localization.AtPrime Q) := IsFractionRing.toField T
  have : IsReduced (AlgebraicClosure k ⊗[k] T) := by
    have := hS (AlgebraicClosure k)
    exact isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange R k (AlgebraicClosure k) (AlgebraicClosure k) S)
      (AlgEquiv.injective _)
  have : Algebra.FormallySmooth k (Localization.AtPrime Q) :=
    formallySmooth_of_isFractionRing (T := T)
  refine ⟨⟨Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T), inferInstance⟩,
    isSmoothAt_of_formallySmooth_localization_fiber p.asIdeal Q, ?_⟩
  ext1
  exact (Ideal.LiesOver.over (P := Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T))
    (p := p.asIdeal)).symm

end Langlands.CommutativeAlgebra
