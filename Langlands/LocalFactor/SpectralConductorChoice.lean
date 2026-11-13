import Langlands.LocalFactor.SpectralConductorInduction
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.LocalFactor.NonabelianUniquenessStatement

/-!
# Finite Galois subfields presenting finitely many characters

Every open neighbourhood of the identity in Weil inertia contains the kernel of
restriction to some finite Galois subfield. Hence a continuous character of
`W_L` is presented at every sufficiently large finite Galois subfield: on a small
open set its values are close to `1`, and so are the values of all powers of an
element acting trivially on that subfield, which forces the value `1`.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Ramification.Padic CommonClosure Weil.Local

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every open neighbourhood of `1` in Weil inertia contains the kernel of the
restriction to some finite Galois subfield. -/
theorem exists_finiteGalois_of_isOpen (S : Set (localInertia F)) (hS : IsOpen S)
    (h1 : (1 : localInertia F) ∈ S) :
    ∃ E : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
      ∀ w : localInertia F, weilInertiaRestriction F E w = 1 → w ∈ S := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  set e := localInertiaEquiv F
  have hN : (e.symm ⁻¹' S) ∈ nhds (1 : F.absoluteInertia F.canonicalTopologicalData) :=
    (hS.preimage e.symm.continuous).mem_nhds (by simpa using h1)
  rw [nhds_subtype, Filter.mem_comap] at hN
  obtain ⟨V, hV, hVN⟩ := hN
  have hV' : V ∈ nhds (1 : Gal(AlgebraicClosure F.Carrier/F.Carrier)) := hV
  obtain ⟨E, hEfd, hEn, hEV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F.Carrier (AlgebraicClosure F.Carrier) V).mp hV'
  let L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    { toIntermediateField := E
      finiteDimensional := hEfd
      isGalois := { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable F.Carrier E
                      (AlgebraicClosure F.Carrier)
                    to_normal := hEn } }
  refine ⟨L, fun w hw => ?_⟩
  have hw1 : absoluteFiniteRestriction F L (localProjection F w) = 1 := by
    have := congrArg Subtype.val hw
    rwa [weilInertiaRestriction_coe] at this
  have hfix : localProjection F w ∈ E.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff (localProjection F w) L).mpr hw1
  have hmem : e w ∈ ((↑) : F.absoluteInertia F.canonicalTopologicalData →
      Field.absoluteGaloisGroup F.Carrier) ⁻¹' V := hEV hfix
  have := hVN hmem
  simpa using this

/-- The Galois closure of an intermediate field, as a finite Galois subfield. -/
def galoisClosure (L : Extension F) :
    FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  haveI : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  haveI : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  haveI : FiniteDimensional F.Carrier L.field := L.2
  { toIntermediateField :=
      IntermediateField.normalClosure F.Carrier L.field (AlgebraicClosure F.Carrier)
    finiteDimensional := inferInstance
    isGalois := inferInstance }

theorem le_galoisClosure (L : Extension F) :
    L.field ≤ (galoisClosure F L).toIntermediateField :=
  IntermediateField.le_normalClosure _

/-- A continuous character of `W_L` is presented at every finite Galois subfield
containing a suitable one. -/
theorem exists_isPresentedAt (L : Extension F) (χ : weilSubgroup F L →ₜ* ℂˣ) :
    ∃ E : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
      ∀ M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
        E ≤ M → IsPresentedAt F M L χ := by
  let U : Set (weilSubgroup F L) := {s | ‖(χ s : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hU : IsOpen U :=
    isOpen_lt ((Units.continuous_val.comp χ.continuous).sub continuous_const).norm
      continuous_const
  let T : Set (localWeilGroup F) := Subtype.val '' U
  have hT : IsOpen T := (weilSubgroup_open F L).isOpenMap_subtype_val U hU
  let S : Set (localInertia F) := Subtype.val ⁻¹' T
  have hS : IsOpen S := hT.preimage continuous_subtype_val
  have h1 : (1 : localInertia F) ∈ S := ⟨1, by simp [U], rfl⟩
  obtain ⟨E, hE⟩ := exists_finiteGalois_of_isOpen F S hS h1
  refine ⟨E, fun M hEM s hs hres => ?_⟩
  apply Units.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hsn : ((s : localWeilGroup F) ^ n) ∈ localInertia F := (localInertia F).pow_mem hs n
  have hker : weilInertiaRestriction F E ⟨(s : localWeilGroup F) ^ n, hsn⟩ = 1 := by
    have hM : weilInertiaRestriction F M ⟨(s : localWeilGroup F) ^ n, hsn⟩ = 1 := by
      apply Subtype.ext
      change restrictionM F M ((s : localWeilGroup F) ^ n) = 1
      rw [map_pow, hres, one_pow]
    exact weilInertiaRestriction_ker_le F hEM hM
  obtain ⟨t, ht, htn⟩ := hE _ hker
  have hts : t = s ^ n := Subtype.ext htn
  rw [hts] at ht
  simpa [U] using ht

variable {F} in
theorem restrictionM_eq_one_of_le
    {M₁ M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)} (hle : M₁ ≤ M)
    (w : localWeilGroup F) (hw : restrictionM F M w = 1) : restrictionM F M₁ w = 1 := by
  ext x
  rw [restrictionM_apply]
  have h := restrictionM_apply F M w ⟨(x : AlgebraicClosure F.Carrier), hle x.2⟩
  rw [hw] at h
  exact h.symm

variable {F} in
theorem IsPresentedAt.mono
    {M₁ M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)} (hle : M₁ ≤ M)
    {L : Extension F} {χ : weilSubgroup F L →ₜ* ℂˣ} (hχ : IsPresentedAt F M₁ L χ) :
    IsPresentedAt F M L χ :=
  fun s hs hres => hχ s hs (restrictionM_eq_one_of_le hle _ hres)

open VirtualRepresentation ConductorExponent in
/-- For finitely many induced character differences and any finite Galois
subfield `M₀`, some finite Galois `M ⊇ M₀` contains every inducing field and
presents every character. -/
theorem exists_presentingField (S₀ : Finset (Virtual.{uF, uV} F (base F)))
    (hS₀ : (S₀ : Set (Virtual.{uF, uV} F (base F))) ⊆
      characterDifferenceInductionGenerators.{uF, uV} F (base F))
    (M₀ : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    ∃ M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier), M₀ ≤ M ∧
      ∀ y ∈ S₀, ∃ (L : Extension F) (h : (base F).field ≤ L.field)
        (χ χ' : weilSubgroup F L →ₜ* ℂˣ) (_hLM : L.field ≤ M.toIntermediateField),
        y = induce F (base F) L h (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ') ∧
        IsPresentedAt F M L χ ∧ IsPresentedAt F M L χ' := by
  classical
  induction S₀ using Finset.induction_on with
  | empty => exact ⟨M₀, le_rfl, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  | insert y S hyS ih =>
    obtain ⟨M₁, hM₀₁, hS⟩ := ih (fun z hz => hS₀ (Finset.mem_insert_of_mem hz))
    obtain ⟨L, h, χ, χ', rfl⟩ := hS₀ (Finset.mem_insert_self _ _)
    obtain ⟨E, hE⟩ := exists_isPresentedAt F L χ
    obtain ⟨E', hE'⟩ := exists_isPresentedAt F L χ'
    refine ⟨M₁ ⊔ galoisClosure F L ⊔ E ⊔ E', ?_, ?_⟩
    · exact hM₀₁.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · have h1 : M₁ ≤ M₁ ⊔ galoisClosure F L ⊔ E ⊔ E' :=
        le_sup_left.trans (le_sup_left.trans le_sup_left)
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · refine ⟨L, h, χ, χ', ?_, rfl, hE _ ?_, hE' _ le_sup_right⟩
        · exact (le_galoisClosure F L).trans
            ((le_sup_right.trans (le_sup_left.trans le_sup_left) :
              galoisClosure F L ≤ M₁ ⊔ galoisClosure F L ⊔ E ⊔ E'))
        · exact le_sup_right.trans le_sup_left
      · obtain ⟨L₁, h₁, χ₁, χ₁', hLM₁, hz₁, hχ₁, hχ₁'⟩ := hS z hz
        exact ⟨L₁, h₁, χ₁, χ₁', hLM₁.trans h1, hz₁, hχ₁.mono h1, hχ₁'.mono h1⟩

end Langlands.LocalFactor.SpectralConductor
