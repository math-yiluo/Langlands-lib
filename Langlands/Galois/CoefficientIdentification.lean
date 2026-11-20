import Langlands.Galois.CompatibleFamily
import Langlands.Global.Arithmetic.GaloisModelRealization
import Langlands.Global.CompletionPadic
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.SetTheory.Cardinal.Rat
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Coefficient identifications for p-adic Galois representations -/

noncomputable section

universe u

namespace Langlands.GaloisRepresentation

open Langlands.Global Cardinal Filter Set
open scoped Cardinal NumberField Topology Valued

variable {E : Type u} [Field E] [NumberField E]
variable (p : ℕ) [Fact p.Prime]

private theorem cardinal_padic : #ℚ_[p] = 𝔠 := by
  apply le_antisymm _ (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])
  have hseq (x : ℚ_[p]) : ∃ a : ℕ → ℚ, Tendsto (fun n => (a n : ℚ_[p])) atTop (𝓝 x) := by
    obtain ⟨b, hb, hx⟩ := mem_closure_iff_seq_limit.mp (Padic.denseRange_ratCast p x)
    choose a ha using hb
    exact ⟨a, (funext ha).symm ▸ hx⟩
  choose a ha using hseq
  have hinj : Function.Injective a := fun x y h => tendsto_nhds_unique (ha x) (h ▸ ha y)
  exact (Cardinal.mk_le_of_injective hinj).trans_eq
    (by rw [Cardinal.mk_arrow, Cardinal.mkRat, Cardinal.mk_nat, Cardinal.lift_aleph0,
      Cardinal.aleph0_power_aleph0])

private theorem cardinal_padicAlgCl : #(PadicAlgCl p) = 𝔠 := by
  let e : {x : PadicAlgCl p // IsAlgebraic ℚ_[p] x} ≃ PadicAlgCl p :=
    Equiv.subtypeUnivEquiv (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]))
  rw [← Cardinal.mk_congr e, Algebraic.cardinalMk_of_infinite, cardinal_padic]

/-- An algebraic identification of the p-adic algebraic closure with the
    complex field. The two fields have their respective topologies. -/
def padicAlgClComplexEquiv : PadicAlgCl p ≃+* ℂ :=
  Classical.choice (IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinal_padicAlgCl p]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp ((cardinal_padicAlgCl p).trans Cardinal.mk_complex.symm)))

/-- A p-adic and a complex embedding of the same number field can be
    matched by an algebraic identification of the two algebraically closed fields. -/
theorem exists_padicAlgClComplexEquiv_extending (j : E →+* PadicAlgCl p) (ι : E →+* ℂ) :
    ∃ e : PadicAlgCl p ≃+* ℂ, ∀ x : E, e (j x) = ι x := by
  let : Algebra E (PadicAlgCl p) := j.toAlgebra
  let : Algebra E ℂ := ι.toAlgebra
  let : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hE : #E ≤ ℵ₀ := Cardinal.mk_le_aleph0
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis E (PadicAlgCl p)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis E ℂ
  let v : s → PadicAlgCl p := Subtype.val
  let w : t → ℂ := Subtype.val
  have hsc : #s = 𝔠 := by
    have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v hs hE
      (by rw [cardinal_padicAlgCl p]; exact Cardinal.aleph0_lt_continuum)
    simpa only [Cardinal.lift_id, cardinal_padicAlgCl p] using h.symm
  have htc : #t = 𝔠 := by
    have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt w ht hE
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    simpa only [Cardinal.lift_id, Cardinal.mk_complex] using h.symm
  obtain ⟨e⟩ := Cardinal.eq.mp (hsc.trans htc.symm)
  let B := Algebra.adjoin E (Set.range v)
  let C := Algebra.adjoin E (Set.range w)
  let : IsAlgClosure B (PadicAlgCl p) := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let : IsAlgClosure C ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis w ht
  let rename : MvPolynomial s E ≃ₐ[E] MvPolynomial t E :=
    AlgEquiv.ofAlgHom (MvPolynomial.rename e) (MvPolynomial.rename e.symm)
      (by ext; simp) (by ext; simp)
  let f : B ≃ₐ[E] C := (hs.1.aevalEquiv.symm.trans rename).trans ht.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv (PadicAlgCl p) ℂ f.toRingEquiv, fun x => ?_⟩
  change IsAlgClosure.equivOfEquiv _ _ f.toRingEquiv
    (algebraMap E (PadicAlgCl p) x) = algebraMap E ℂ x
  rw [IsScalarTower.algebraMap_apply E B (PadicAlgCl p), IsAlgClosure.equivOfEquiv_algebraMap]
  change algebraMap C ℂ (f (algebraMap E B x)) = _
  rw [AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply E C ℂ x).symm

/-- A p-adic embedding of a number field extends continuously from a finite
    completion of that field of the matching residue characteristic. -/
theorem exists_coefficientCompletionEmbedding (j : E →+* PadicAlgCl p) :
    ∃ (lam : FinitePlace E) (f : FiniteCompletion E lam →+* PadicAlgCl p),
      residueCharacteristic lam = p ∧ Continuous f ∧
        ∀ x : E, f (NumberField.FinitePlace.embedding lam x) = j x := by
  let b := Module.finBasis ℚ E
  let F := IntermediateField.adjoin ℚ_[p] (Set.range (j ∘ b))
  let : FiniteDimensional ℚ_[p] F := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let : NontriviallyNormedField F :=
    { (inferInstance : NormedField F) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[p])
        refine ⟨algebraMap ℚ_[p] F x, ?_⟩
        change 1 < ‖(x : PadicAlgCl p)‖
        rwa [PadicAlgCl.norm_extends] }
  let : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  let : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  let jF : E →+* F := j.codRestrict F.toSubfield fun x => by
    rw [← b.sum_repr x, map_sum]
    apply F.sum_mem
    intro i _
    rw [Algebra.smul_def, _root_.map_mul]
    change j (((b.repr x) i : ℚ) : E) * j (b i) ∈ F
    rw [map_ratCast]
    refine F.mul_mem ?_ (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact F.algebraMap_mem _
  have hgen : Algebra.adjoin ℚ_[p] (Set.range jF) = ⊤ := by
    let B := Algebra.adjoin ℚ_[p] (Set.range jF)
    have hF : F.toSubalgebra ≤ B.map F.val := by
      change (IntermediateField.adjoin ℚ_[p] (Set.range (j ∘ b))).toSubalgebra ≤ _
      rw [IntermediateField.adjoin_toSubalgebra]
      exact Algebra.adjoin_le fun _ ⟨i, hi⟩ => hi ▸
        ⟨jF (b i), Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
    apply top_unique
    intro y _
    obtain ⟨x, hx, heq⟩ := hF y.property
    exact F.val.injective heq ▸ hx
  have hdense := FieldRealization.denseRange_of_adjoin_eq_top p jF hgen
  obtain ⟨lam, e, hlam, he, _, hj⟩ :=
    FieldRealization.exists_adicCompletion_ringEquiv (F := F) jF hdense
  have hsub : Continuous (F.val : F → PadicAlgCl p) := continuous_subtype_val
  refine ⟨lam, F.val.toRingHom.comp e.toRingHom, ?_, hsub.comp he, fun x => ?_⟩
  · have hp : (p : 𝓞 E) ∈ lam.asIdeal := (hlam _).mpr (by
      rw [show jF (p : 𝓞 E) = (p : F) by push_cast; exact map_natCast jF p]
      change ‖((p : F) : PadicAlgCl p)‖ < 1
      rw [show ((p : F) : PadicAlgCl p) = (p : PadicAlgCl p) from map_natCast F.val p,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
        PadicAlgCl.norm_extends, Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt))
    have hp0 : (p : 𝓞 E ⧸ lam.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hp
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.prime_ringChar (𝓞 E ⧸ lam.asIdeal)) (Fact.out : p.Prime)).mp
      ((CharP.cast_eq_zero_iff (𝓞 E ⧸ lam.asIdeal) (residueCharacteristic lam) p).mp hp0)
  · change F.val (e (algebraMap E _ x)) = j x
    rw [hj]
    rfl

/-- Realize a fixed complex coefficient embedding at a finite completion
    using a chosen p-adic to complex field identification. -/
theorem exists_compatibleCoefficientCompletionEmbedding
    (e : PadicAlgCl p ≃+* ℂ) (ι : E →+* ℂ) :
    ∃ (lam : FinitePlace E) (f : FiniteCompletion E lam →+* PadicAlgCl p),
      residueCharacteristic lam = p ∧ Continuous f ∧
        ∀ x : E, e (f (NumberField.FinitePlace.embedding lam x)) = ι x := by
  obtain ⟨lam, f, hp, hf, hι⟩ := exists_coefficientCompletionEmbedding p (e.symm.toRingHom.comp ι)
  refine ⟨lam, f, hp, hf, fun x => ?_⟩
  rw [hι]
  exact e.apply_symm_apply (ι x)

/-- Embed a fixed coefficient completion into the algebraic closure of the
    p-adic field at its residue prime, using its p-adic algebra structure. -/
def coefficientCompletionEmbedding (lam : FinitePlace E) :
    FiniteCompletion E lam →+* PadicAlgCl (CompletionPadic.residuePrime lam) := by
  letI := CompletionPadic.padicAlgebra lam
  letI := CompletionPadic.padicFinite lam
  exact (IsAlgClosed.lift :
    FiniteCompletion E lam →ₐ[ℚ_[CompletionPadic.residuePrime lam]]
      PadicAlgCl (CompletionPadic.residuePrime lam)).toRingHom

theorem continuous_coefficientCompletionEmbedding (lam : FinitePlace E) :
    Continuous (coefficientCompletionEmbedding lam) := by
  let := CompletionPadic.padicAlgebra lam
  let := CompletionPadic.padicFinite lam
  let := CompletionPadic.completion_isModuleTopology lam
  exact IsModuleTopology.continuous_of_linearMap (IsAlgClosed.lift :
    FiniteCompletion E lam →ₐ[ℚ_[CompletionPadic.residuePrime lam]]
      PadicAlgCl (CompletionPadic.residuePrime lam)).toLinearMap

end Langlands.GaloisRepresentation
