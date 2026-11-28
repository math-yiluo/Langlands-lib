import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.ClassFieldProof
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinUnramified
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceAssembly
import Langlands.GaloisCohomology.Global.BrauerSequence.CyclicLayers
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # A cyclic cubic field with full degree at prescribed finite places -/

noncomputable section

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Global.Artin
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global

set_option maxHeartbeats 1400000

variable {F : Type u} [Field F] [NumberField F]

private def valuationCharacter (v : FinitePlace F) (ζ : ℂˣ) :
    (FiniteCompletion F v)ˣ →ₜ* ℂˣ :=
  ⟨(zpowersHom ℂˣ ζ).comp (topologicalData v).orderHom,
    (continuous_of_discreteTopology (f := zpowersHom ℂˣ ζ)).comp
      (Langlands.LocalClassField.WeilReciprocityExistence.orderHom_continuous_isCompact_ker
        (padicField v) (topologicalData v)).1⟩

private theorem valuationCharacter_apply (v : FinitePlace F) (ζ : ℂˣ)
    (x : (FiniteCompletion F v)ˣ) (k : ℤ)
    (hx : Valued.v (x : FiniteCompletion F v) = WithZero.exp k) :
    valuationCharacter v ζ x = ζ ^ (-k) := by
  change ζ ^ (-WithZero.log ((topologicalData v).discreteValuation (x : FiniteCompletion F v))) = _
  rw [FiniteExtension.topologicalData_discreteValuation, hx, WithZero.log_exp]

private theorem one_isArithFrobAt_of_inertiaDeg_one
    {L : Type u} [Field L] [NumberField L] [Algebra F L]
    (v : FinitePlace F) (w : FinitePlace L) [h : w.asIdeal.LiesOver v.asIdeal]
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) :
    (RingOfIntegers.mapAlgHom (1 : L ≃ₐ[F] L)).IsArithFrobAt w.asIdeal := by
  classical
  let p := v.asIdeal
  let q := w.asIdeal
  have : p.IsMaximal := v.isMaximal
  have : q.IsMaximal := w.isMaximal
  let : Field (𝓞 L ⧸ q) := Ideal.Quotient.field q
  let : Fintype (𝓞 L ⧸ q) := Fintype.ofFinite _
  have hc : Nat.card (𝓞 F ⧸ q.under (𝓞 F)) = Fintype.card (𝓞 L ⧸ q) := by
    have hh := Ideal.cardQuot_pow_inertiaDeg p q
    rw [show q.inertiaDeg (𝓞 F) = 1 from hf, pow_one] at hh
    rw [show q.under (𝓞 F) = p from h.over.symm, ← Nat.card_eq_fintype_card]
    exact hh
  intro x
  change x - x ^ Nat.card (𝓞 F ⧸ q.under (𝓞 F)) ∈ q
  rw [← Ideal.Quotient.eq, map_pow, hc, FiniteField.pow_card]

/-- A prescribed finite set of finite places of a number field has full local
degree in some cyclic Galois extension of degree three. -/
def CyclicCubicPrescribedLocalDegreeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F)),
    ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E),
      IsGalois F E ∧ Module.finrank F E = 3 ∧
        letI := NumberField.of_module_finite F E
        ∀ v ∈ S, ∀ (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal],
          Module.finrank (FiniteCompletion F v) (FiniteCompletion E w) = 3

theorem cyclicCubicPrescribedLocalDegree : CyclicCubicPrescribedLocalDegreeStatement.{u} := by
  classical
  intro F _ _ S
  let v₀ := (placeAbove (K := ℚ) F (Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩)).val
  let T := insert v₀ S
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hz : IsPrimitiveRoot z 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  let ζ := Units.mk0 z (hz.ne_zero (by decide))
  have hζ : ζ ^ 3 = 1 := Units.ext hz.pow_eq_one
  have hζne : ζ ≠ 1 := fun h => hz.ne_one (by decide) (congrArg Units.val h)
  let η (v : T) := valuationCharacter v.val ζ
  have hη (v : T) : η v ^ 3 = 1 := by
    apply DFunLike.ext
    intro x
    rw [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun]
    change (ζ ^ (topologicalData v.val).ord x) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  have hInf : (1 : (InfiniteAdeles F)ˣ →ₜ* ℂˣ) ^ 3 = 1 := by
    apply DFunLike.ext
    intro x
    simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, one_pow]
  obtain ⟨χ, hχ, hχv, _⟩ :=
    finiteOrderCharacterPrescription_proof F T 3 (by decide) η 1 hη hInf
  let ψ := χ ^ 4
  have hψ : ψ ^ 3 = 1 := by
    change (χ ^ 4) ^ 3 = 1
    rw [← pow_mul, show 4 * 3 = (2 * 3) * 2 by decide, pow_mul, hχ]
    apply DFunLike.ext
    intro x
    simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, one_pow]
  have hψv (v : T) (a : (FiniteCompletion F v.val)ˣ) :
      ψ (finiteClassInclusion F v.val a) = η v a := by
    have hv := DFunLike.congr_fun (hχv v) a
    change χ (finiteClassInclusion F v.val a) = η v a at hv
    have hv3 : η v a ^ 3 = 1 := by
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
        DFunLike.congr_fun (hη v) a
    change (χ ^ 4) (finiteClassInclusion F v.val a) = _
    rw [ContinuousMonoidHom.pow_apply, hv, show (4 : ℕ) = 3 + 1 by decide,
      pow_succ, hv3, one_mul]
  obtain ⟨L, hfin, hgal, hcomm, hdata⟩ :=
    finiteOrderHeckeArtinRealization F ψ ⟨3, by decide, hψ⟩
  let : NumberField L := NumberField.of_module_finite F L
  let : TopologicalSpace (L ≃ₐ[F] L) := ⊥
  obtain ⟨ρ, θ, hρ, hθ, hNorm, hθρ⟩ := hdata
  have hθcube (σ : L ≃ₐ[F] L) : θ σ ^ 3 = 1 := by
    obtain ⟨x, rfl⟩ := hρ σ
    rw [hθρ]
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply] using
      DFunLike.congr_fun hψ x
  let toRoots : (L ≃ₐ[F] L) →* rootsOfUnity 3 ℂ :=
    θ.toMonoidHom.codRestrict _ fun σ => (mem_rootsOfUnity 3 _).mpr (hθcube σ)
  have hinj : Function.Injective toRoots := fun a b h => hθ (congrArg Subtype.val h)
  have hρπ (v : T) (π : (FiniteCompletion F v.val)ˣ)
      (hπ : Valued.v (π : FiniteCompletion F v.val) = WithZero.exp (-1 : ℤ)) :
      ρ (finiteClassInclusion F v.val π) ≠ 1 := by
    intro h
    have hv : ψ (finiteClassInclusion F v.val π) = 1 := by rw [← hθρ, h, map_one]
    rw [hψv v π, valuationCharacter_apply v.val ζ π (-1) hπ, neg_neg, zpow_one] at hv
    exact hζne hv
  have hdegree : Module.finrank F L = 3 := by
    have hdiv := Subgroup.card_dvd_of_injective toRoots hinj
    rw [Complex.card_rootsOfUnity, IsGalois.card_aut_eq_finrank] at hdiv
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · have hsub : Subsingleton (L ≃ₐ[F] L) :=
        (Nat.card_eq_one_iff_unique.mp ((IsGalois.card_aut_eq_finrank F L).trans h)).1
      let v : T := ⟨v₀, Finset.mem_insert_self _ _⟩
      obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one v.val
      exact (hρπ v π (by rw [valued_units, hπ]) (hsub.elim _ _)).elim
    · exact h
  have hunram (v : T) (w : FinitePlace L) (hw : w.asIdeal.LiesOver v.val.asIdeal) :
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
    have : IsAbelianGalois F L := { toIsMulCommutative := IsMulCommutative.of_comm hcomm }
    have hρeq := eq_of_hasArithmeticArtinNormalization ρ (arithmeticFiniteArtinBot F L)
      hNorm arithmeticFiniteArtin_hasArithmeticArtinNormalization
    apply isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one v.val _ w hw
    intro a ha
    change arithmeticFiniteArtinBot F L (finiteClassInclusion F v.val a) = 1
    rw [← hρeq]
    apply hθ
    rw [hθρ, hψv v a, map_one]
    have hv : Valued.v (a : FiniteCompletion F v.val) = WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero]
      exact adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
    rw [valuationCharacter_apply v.val ζ a 0 hv, neg_zero, zpow_zero]
  have hloc (v : FinitePlace F) (hv : v ∈ S) (w : FinitePlace L) [w.asIdeal.LiesOver v.asIdeal] :
      Module.finrank (FiniteCompletion F v) (FiniteCompletion L w) = 3 := by
    have hd := localDegree_dvd v w
    rw [hdegree] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · have h' := h
      rw [localDegree_eq] at h'
      have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.dvd_one.mp (h' ▸ dvd_mul_left _ _)
      let v' : T := ⟨v, Finset.mem_insert_of_mem hv⟩
      have hu := hunram v' w inferInstance
      obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one v
      have hval : Valued.v (π : FiniteCompletion F v) = WithZero.exp (-1 : ℤ) := by
        rw [valued_units, hπ]
      have hFrob := hNorm v w inferInstance hu π hval
      exact (hρπ v' π hval
        (eq_of_isArithFrobAt_mapAlgHom w hu hFrob (one_isArithFrobAt_of_inertiaDeg_one v w hf))).elim
    · exact h
  let g : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let E := g.fieldRange
  let e : L ≃ₐ[F] E := AlgEquiv.ofInjectiveField g
  let : FiniteDimensional F E := e.toLinearEquiv.finiteDimensional
  refine ⟨E, inferInstance, IsGalois.of_algEquiv e, e.toLinearEquiv.finrank_eq.symm.trans hdegree, ?_⟩
  -- The completion degrees are invariant under the chosen field transport.
  intro v hv w hw
  let : NumberField E := NumberField.of_module_finite F E
  have hloc' : Langlands.GaloisCohomology.LocalDegreesDvd F L S 3 :=
    fun v hv w _ => dvd_of_eq (hloc v hv w).symm
  have hd := Langlands.GaloisCohomology.localDegreesDvd_of_algEquiv e hloc' v hv w
  let : IsGalois F E := IsGalois.of_algEquiv e
  have hd' := localDegree_dvd v w
  rw [e.toLinearEquiv.finrank_eq.symm.trans hdegree] at hd'
  exact Nat.dvd_antisymm hd' hd

end Langlands.Global
