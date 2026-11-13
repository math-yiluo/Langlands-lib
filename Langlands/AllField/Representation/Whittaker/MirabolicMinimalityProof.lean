import Langlands.Representation.Whittaker.MirabolicMinimalityProof
import Langlands.AllField.Representation.Derivative.MirabolicCharacter
import Langlands.AllField.Representation.Derivative.MirabolicLatticeBox
import Langlands.AllField.Representation.Whittaker.MirabolicMinimalityStatement
/-!
# Proof of compact minimality in the actual mirabolic smooth induction

The proof is by induction on the rank. For a nonzero subrepresentation `W` of the
smooth induction on `P_(m+2)`, restriction along `successor : P_(m+1) → P_(m+2)` gives
a nonzero subrepresentation of the smaller induction, which contains the compact
functions by induction. Finite character sums over the radical cut members of `W`
down to the points whose last row lies in a lattice box, and right translation by the
Levi moves such boxes around. A compactness argument then writes every compactly
supported function as a finite sum of such cut functions. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.Whittaker.MirabolicMinimality
open Langlands.Whittaker.MirabolicMinimality hiding compactMinimality exists_cut_of_one exists_cut_one mem_of_forall_cut realized_cut topologicalRing
open Langlands.AllField.Whittaker.MirabolicMinimality
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement mirabolicCompactMinimality
open Langlands.AllField.Whittaker

open Topology
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox exists_latticeBox_subset exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isOpen_latticeBox latticeBox latticeBox_mono mem_latticeBox mem_latticeBox_of_forall_character_eq_one
open Langlands.AllField.Derivative.Mirabolic
open Langlands.Whittaker.MirabolicWhittaker (rowOf)
open scoped Matrix

universe uF

section Generic

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable (ψ : UnitaryAdditiveCharacter K)

/-! ### Functions realized by members of a subrepresentation -/

variable {ψ}

/-! ### The last row and the radical -/

/-! ### Restriction along the successor embedding -/

variable (ψ)

end Generic

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

theorem topologicalRing : @IsTopologicalRing F T.topology _ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Cutting a realized function by a lattice box of last rows keeps it realized. -/
theorem realized_cut :
    letI := T.topology
    letI : IsTopologicalRing F := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1)))
      {h : mirabolic (m + 1) F → ℂ}, Realized ψ W h →
      ∀ (v : Fin (m + 1) → F) (N : ℤ), Realized ψ W (cut (latticeBox T (m + 1) N) v h) := by
  intro ψ m W h hh v N
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  obtain ⟨g, hgW, hgh⟩ := hh
  obtain ⟨Lg, hLg⟩ := exists_fix ψ g
  -- A box of radical coordinates fixing `g`.
  have hrad0 : {c : Fin (m + 1) → F |
      ((radicalElement c : radical (m + 1) F) : mirabolic (m + 1) F) ∈ Lg} ∈
        𝓝 (0 : Fin (m + 1) → F) := by
    apply (Lg.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact Lg.one_mem
  obtain ⟨l₁, hl₁⟩ := exists_latticeBox_subset T hrad0
  -- A box on which `c ↦ ψ(v ⬝ c)` is trivial.
  have hv0 : {c : Fin (m + 1) → F |
      v ⬝ᵥ c ∈ T.additiveLattice (T.additiveConductor ψ)} ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    apply ((T.isOpen_additiveLattice _).preimage
      (continuous_const.dotProduct continuous_id)).mem_nhds
    simp only [Set.mem_preimage, id_eq, dotProduct_zero, SetLike.mem_coe]
    exact (T.additiveLattice _).zero_mem
  obtain ⟨l₂, hl₂⟩ := exists_latticeBox_subset T hv0
  -- The finite quotient of boxes.
  let M : ℤ := T.additiveConductor ψ - N
  let l : ℤ := min (min l₁ l₂) M
  let B := latticeBox T (m + 1) M
  let L := (latticeBox T (m + 1) l).addSubgroupOf B
  have : Finite (B ⧸ L) := finite_latticeBox_quotient T (m + 1) M l
  let : Fintype (B ⧸ L) := Fintype.ofFinite _
  have hl₁' : latticeBox T (m + 1) l ≤ latticeBox T (m + 1) l₁ := latticeBox_mono T (by omega)
  have hl₂' : latticeBox T (m + 1) l ≤ latticeBox T (m + 1) l₂ := latticeBox_mono T (by omega)
  -- The averaged member.
  let g' : MirabolicSmoothFunctions ψ (m + 1) := ((Fintype.card (B ⧸ L) : ℂ)⁻¹) •
    ∑ c : B ⧸ L, ψ.complex (-(v ⬝ᵥ ((c.out : B) : Fin (m + 1) → F))) •
      mirabolicSmoothInduced ψ (m + 1)
        (radicalElement ((c.out : B) : Fin (m + 1) → F)).val g
  refine ⟨g', ?_, fun x => ?_⟩
  · exact W.toSubmodule.smul_mem _ (W.toSubmodule.sum_mem fun c _ =>
      W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule _ hgW))
  have heval : mirabolicEval ψ (m + 1) g' x = (Fintype.card (B ⧸ L) : ℂ)⁻¹ *
      ∑ c : B ⧸ L, ψ.complex ((rowOf x - v) ⬝ᵥ ((c.out : B) : Fin (m + 1) → F)) *
        mirabolicEval ψ (m + 1) g x := by
    rw [← evalLinear_apply]
    simp only [g', map_smul, map_sum, smul_eq_mul, evalLinear_apply]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mirabolicEval_translate, eval_mul_radicalElement, ← mul_assoc,
      ← AddChar.map_add_eq_mul, sub_dotProduct, neg_add_eq_sub]
  by_cases hgx : mirabolicEval ψ (m + 1) g x = 0
  · rw [heval, hgx]
    simp only [mul_zero, Finset.sum_const_zero]
    rw [cut, ← hgh x, hgx, ite_self]
  -- Characters trivial on the small box.
  have hψrow : ∀ c ∈ latticeBox T (m + 1) l₁, ψ.complex (rowOf x ⬝ᵥ c) = 1 := by
    intro c hc
    have h1 := hLg _ (hl₁ hc) x
    rw [eval_mul_radicalElement] at h1
    exact (mul_eq_right₀ hgx).mp h1
  have hψv : ∀ c ∈ latticeBox T (m + 1) l₂, ψ.complex (v ⬝ᵥ c) = 1 := by
    intro c hc
    have h1 : ψ (v ⬝ᵥ c) = 1 := by
      apply (T.additiveConductor_spec ψ).1
      exact hl₂ hc
    rw [UnitaryAdditiveCharacter.complex_apply, h1, Circle.coe_one]
  let χ : AddChar B ℂ := ψ.complex.compAddMonoidHom
    ((AddMonoidHom.mk' (fun c : Fin (m + 1) → F => (rowOf x - v) ⬝ᵥ c)
      (fun a b => dotProduct_add _ a b)).comp B.subtype)
  have hχ : ∀ c : B, χ c = ψ.complex ((rowOf x - v) ⬝ᵥ (c : Fin (m + 1) → F)) :=
    fun _ => rfl
  have hsum_eq : ∑ c : B ⧸ L, ψ.complex ((rowOf x - v) ⬝ᵥ ((c.out : B) : Fin (m + 1) → F)) =
      ∑ c : B ⧸ L, χ c.out := rfl
  by_cases hin : rowOf x - v ∈ latticeBox T (m + 1) N
  · have hall : ∀ c : B, χ c = 1 := by
      intro c
      rw [hχ]
      have hmem : rowOf x - v ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M) := by
        simpa [M] using hin
      have h1 := character_dotProduct_eq_one T ψ hmem c.property
      rw [UnitaryAdditiveCharacter.complex_apply, h1, Circle.coe_one]
    rw [heval, cut, ite_eq_left hin, ← hgh x, ← Finset.sum_mul, hsum_eq]
    simp only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  · have hex : ∃ c : B, χ c ≠ 1 := by
      by_contra hne
      push Not at hne
      apply hin
      have hmem := mem_latticeBox_of_forall_character_eq_one T ψ (A := M) (c := rowOf x - v)
        (fun y hy => by
          have h1 := hne ⟨y, hy⟩
          rw [hχ, dotProduct_comm, UnitaryAdditiveCharacter.complex_apply] at h1
          exact Circle.ext (by simpa using h1))
      simpa [M] using hmem
    obtain ⟨c₁, hc₁⟩ := hex
    have hsum : ∑ c : B ⧸ L, χ c.out = 0 := by
      refine sum_out_eq_zero L χ (fun c hc => ?_) hc₁
      have hcl : (c : Fin (m + 1) → F) ∈ latticeBox T (m + 1) l := hc
      rw [hχ, sub_dotProduct, AddChar.map_sub_eq_div, hψrow _ (hl₁' hcl), hψv _ (hl₂' hcl),
        div_one]
    rw [heval, cut, ite_eq_right hin, ← Finset.sum_mul, hsum_eq, hsum, zero_mul, mul_zero]

/-- Core step: near the standard last row, a compact function is cut into `W`. -/
theorem exists_cut_one :
    letI := T.topology
    letI : IsTopologicalRing F := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F) {m : ℕ},
      (∀ W' : Subrepresentation (mirabolicSmoothInduced ψ m), W' ≠ ⊥ →
        mirabolicCompactSubrepresentation ψ m ≤ W') →
      ∀ (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))), W ≠ ⊥ →
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
        ∃ N : ℤ, Realized ψ W (cut (latticeBox T (m + 1) N)
          (lastRow (1 : Langlands.GeneralLinear (m + 1) F)) (mirabolicEval ψ (m + 1) φ)) := by
  intro ψ m ih W hW φ hφ
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : LocallyCompactSpace (Langlands.GeneralLinear (m + 1 + 1) F) :=
    T.generalLinearLocallyCompactSpace (m + 1 + 1)
  have hres := res_mem_compact ψ φ hφ
  obtain ⟨f, hfW, hfφ⟩ := ih (resRep ψ W) (resRep_ne_bot ψ hW) hres
  obtain ⟨Lf, hLf⟩ := exists_fix ψ f
  obtain ⟨Lφ, hLφ⟩ := exists_fix ψ φ
  let J : Subgroup (Langlands.GeneralLinear (m + 1) F) :=
    Lf.toSubgroup.comap levi ⊓ Lφ.toSubgroup.comap levi
  have hJopen : IsOpen (J : Set (Langlands.GeneralLinear (m + 1) F)) :=
    (Lf.isOpen.preimage continuous_levi).inter (Lφ.isOpen.preimage continuous_levi)
  have hagree : ∀ x, rowOf x ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F)) →
      mirabolicEval ψ (m + 1) f x = mirabolicEval ψ (m + 1) φ x :=
    eval_eq_of_res_eq ψ f φ (fun p => congrArg (fun F => mirabolicEval ψ m F p) hfφ) J
      (fun j hj x => hLf _ hj.1 x) (fun j hj x => hLφ _ hj.2 x)
  have hnhds : lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F)) ∈
      𝓝 (lastRow (1 : Langlands.GeneralLinear (m + 1) F)) :=
    lastRow_image_mem_nhds hJopen J.one_mem
  have hnhds0 : {d : Fin (m + 1) → F |
      lastRow (1 : Langlands.GeneralLinear (m + 1) F) + d ∈
        lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F))} ∈
      𝓝 (0 : Fin (m + 1) → F) :=
    (continuous_const.add continuous_id).tendsto' (0 : Fin (m + 1) → F) _
      (add_zero _) hnhds
  obtain ⟨N, hN⟩ := exists_latticeBox_subset T hnhds0
  refine ⟨N, realized_congr (realized_cut T ψ W (realized_of_mem hfW)
    (lastRow (1 : Langlands.GeneralLinear (m + 1) F)) N) fun x => ?_⟩
  by_cases hx : rowOf x - lastRow (1 : Langlands.GeneralLinear (m + 1) F) ∈
      latticeBox T (m + 1) N
  · have hrow : rowOf x ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F)) := by
      have h1 := hN hx
      simpa using h1
    rw [cut, cut, ite_eq_left hx, ite_eq_left hx, hagree x hrow]
  · rw [cut, cut, ite_eq_right hx, ite_eq_right hx]

/-- Translation by the Levi moves the core step to every last row. -/
theorem exists_cut_of_one :
    letI := T.topology
    letI : IsTopologicalRing F := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))),
      (∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
        ∃ N : ℤ, Realized ψ W (cut (latticeBox T (m + 1) N)
          (lastRow (1 : Langlands.GeneralLinear (m + 1) F)) (mirabolicEval ψ (m + 1) φ))) →
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
      ∀ x₀ : mirabolic (m + 1) F,
        ∃ N : ℤ, Realized ψ W (cut (latticeBox T (m + 1) N) (rowOf x₀) (mirabolicEval ψ (m + 1) φ)) := by
  intro ψ m W hcore φ hφ x₀
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hφ' : mirabolicSmoothInduced ψ (m + 1) (levi (projection x₀)) φ ∈
      (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule :=
    (mirabolicCompactSubrepresentation ψ (m + 1)).apply_mem_toSubmodule _ hφ
  obtain ⟨N, hN⟩ := hcore _ hφ'
  have h1 := realized_translate hN (levi (projection x₀))⁻¹
  have hnhds : {d : Fin (m + 1) → F |
      d ᵥ* ((projection x₀)⁻¹ : Langlands.GeneralLinear (m + 1) F).val ∈
        latticeBox T (m + 1) N} ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    apply ((isOpen_latticeBox T (m + 1) N).preimage
      (continuous_id.matrix_vecMul continuous_const)).mem_nhds
    simp only [Set.mem_preimage, id_eq, Matrix.zero_vecMul, SetLike.mem_coe]
    exact (latticeBox T (m + 1) N).zero_mem
  obtain ⟨N', hN'⟩ := exists_latticeBox_subset T hnhds
  refine ⟨N', realized_congr (realized_cut T ψ W h1 (rowOf x₀) N') fun x => ?_⟩
  by_cases hx : rowOf x - rowOf x₀ ∈ latticeBox T (m + 1) N'
  · have hrow : rowOf (x * (levi (projection x₀))⁻¹) -
        lastRow (1 : Langlands.GeneralLinear (m + 1) F) =
        (rowOf x - rowOf x₀) ᵥ* ((projection x₀)⁻¹ : Langlands.GeneralLinear (m + 1) F).val := by
      rw [row_mul, map_inv, projection_levi, Matrix.sub_vecMul]
      congr 1
      rw [rowOf, ← lastRow_mul_eq_vecMul, mul_inv_cancel]
    have hin : rowOf (x * (levi (projection x₀))⁻¹) -
        lastRow (1 : Langlands.GeneralLinear (m + 1) F) ∈ latticeBox T (m + 1) N := by
      rw [hrow]
      exact hN' hx
    rw [cut, cut, ite_eq_left hx, ite_eq_left hin, cut, ite_eq_left hx, mirabolicEval_translate,
      inv_mul_cancel_right]
  · rw [cut, cut, ite_eq_right hx, cut, ite_eq_right hx]

/-- Compactness: local cuts at every last row assemble the whole compact function. -/
theorem mem_of_forall_cut :
    letI := T.topology
    letI : IsTopologicalRing F := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))),
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
      (∀ x₀ : mirabolic (m + 1) F, ∃ N : ℤ,
        Realized ψ W (cut (latticeBox T (m + 1) N) (rowOf x₀) (mirabolicEval ψ (m + 1) φ))) →
      φ ∈ W.toSubmodule := by
  intro ψ m W φ hφ hloc
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  classical
  have : LocallyCompactSpace (Langlands.GeneralLinear (m + 1 + 1) F) :=
    T.generalLinearLocallyCompactSpace (m + 1 + 1)
  have : LocallyCompactSpace (mirabolic (m + 1) F) := Mirabolic.locallyCompactSpace
  have hφc : IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent (m + 1) F)
      (mirabolicEval ψ (m + 1) φ)) := hφ
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (m + 1) F) Mirabolic.upperUnipotent_isClosed hφc
  choose N hN using hloc
  have hrowc : Continuous (rowOf : mirabolic (m + 1) F → Fin (m + 1) → F) :=
    continuous_lastRow.comp continuous_projection
  have hnhds : ∀ (k : ℤ) (x₀ : mirabolic (m + 1) F),
      rowOf ⁻¹' {w | w - rowOf x₀ ∈ latticeBox T (m + 1) k} ∈ 𝓝 x₀ := by
    intro k x₀
    apply IsOpen.mem_nhds
    · exact ((isOpen_latticeBox T (m + 1) k).preimage
        (continuous_id.sub continuous_const)).preimage hrowc
    · simp only [Set.mem_preimage, Set.mem_ofPred_eq, sub_self]
      exact zero_mem _
  -- A uniform level.
  obtain ⟨t, -, hcover⟩ := hC.elim_nhds_subcover (fun x₀ => rowOf ⁻¹'
    {w | w - rowOf x₀ ∈ latticeBox T (m + 1) (N x₀)}) (fun x₀ _ => hnhds (N x₀) x₀)
  let L : ℤ := -∑ x₀ ∈ t, |N x₀|
  have hL : ∀ x₀ ∈ t, L ≤ N x₀ := by
    intro x₀ hx₀
    have h1 := Finset.single_le_sum (f := fun x => |N x|) (fun j _ => abs_nonneg (N j)) hx₀
    have h2 := neg_abs_le (N x₀)
    change -∑ x ∈ t, |N x| ≤ N x₀
    linarith
  have hC' : ∀ x₁ ∈ C, Realized ψ W
      (cut (latticeBox T (m + 1) L) (rowOf x₁) (mirabolicEval ψ (m + 1) φ)) := by
    intro x₁ hx₁
    obtain ⟨x₀, hx₀t, hx₁x₀⟩ := Set.mem_iUnion₂.mp (hcover hx₁)
    have hx₁x₀' : rowOf x₁ - rowOf x₀ ∈ latticeBox T (m + 1) (N x₀) := hx₁x₀
    refine realized_congr (realized_cut T ψ W (hN x₀) (rowOf x₁) L) fun x => ?_
    by_cases hx : rowOf x - rowOf x₁ ∈ latticeBox T (m + 1) L
    · have hx0 : rowOf x - rowOf x₀ ∈ latticeBox T (m + 1) (N x₀) := by
        have h := add_mem (latticeBox_mono T (hL x₀ hx₀t) hx) hx₁x₀'
        rwa [sub_add_sub_cancel] at h
      rw [cut, cut, ite_eq_left hx, ite_eq_left hx0, cut, ite_eq_left hx]
    · rw [cut, cut, ite_eq_right hx, cut, ite_eq_right hx]
  -- Finitely many classes modulo the uniform box.
  obtain ⟨t₂, ht₂C, hcover₂⟩ := hC.elim_nhds_subcover (fun x₁ => rowOf ⁻¹'
    {w | w - rowOf x₁ ∈ latticeBox T (m + 1) L}) (fun x₁ _ => hnhds L x₁)
  let Q := (Fin (m + 1) → F) ⧸ latticeBox T (m + 1) L
  let S : Finset Q := t₂.image fun x₁ => (QuotientAddGroup.mk (rowOf x₁) : Q)
  have hsupp : ∀ x, mirabolicEval ψ (m + 1) φ x ≠ 0 →
      (QuotientAddGroup.mk (rowOf x) : Q) ∈ S := by
    intro x hx
    have hmem : Induction.quotientMap _ x ∈ Induction.quotientSupport
        (Mirabolic.upperUnipotent (m + 1) F) (mirabolicEval ψ (m + 1) φ) :=
      ⟨x, hx, rfl⟩
    rw [← hCimg] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    have hu : x * c⁻¹ ∈ Mirabolic.upperUnipotent (m + 1) F := by
      have h' : QuotientGroup.rightRel _ c x := Quotient.exact hcx
      rwa [QuotientGroup.rightRel_apply] at h'
    have hrx : rowOf x = rowOf c := by
      have h := MirabolicWhittaker.rowOf_upperUnipotent_mul ⟨_, hu⟩ c
      rwa [inv_mul_cancel_right] at h
    obtain ⟨x₁, hx₁t, hcx₁⟩ := Set.mem_iUnion₂.mp (hcover₂ hc)
    have hcx₁' : rowOf c - rowOf x₁ ∈ latticeBox T (m + 1) L := hcx₁
    refine Finset.mem_image.mpr ⟨x₁, hx₁t, ?_⟩
    rw [hrx, mk_eq_mk_iff, ← neg_mem_iff, neg_sub]
    exact hcx₁'
  have hterm : ∀ γ ∈ S, Realized ψ W
      (fun x => if (QuotientAddGroup.mk (rowOf x) : Q) = γ then mirabolicEval ψ (m + 1) φ x
        else 0) := by
    intro γ hγ
    obtain ⟨x₁, hx₁t, rfl⟩ := Finset.mem_image.mp hγ
    refine realized_congr (hC' x₁ (ht₂C x₁ hx₁t)) fun x => ?_
    rw [cut]
    simp only [mk_eq_mk_iff]
  apply mem_of_realized
  refine realized_congr (realized_sum S hterm) fun x => ?_
  rw [Finset.sum_ite_eq]
  by_cases hx : mirabolicEval ψ (m + 1) φ x = 0
  · rw [hx]
    simp
  · rw [ite_eq_left (hsupp x hx)]

/-- Compact minimality for every rank, for the supplied local-field data `T`. -/
theorem compactMinimality :
    letI := T.topology
    letI : IsTopologicalRing F := topologicalRing T
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
      (W : Subrepresentation (mirabolicSmoothInduced ψ n)),
      W ≠ ⊥ → mirabolicCompactSubrepresentation ψ n ≤ W := by
  intro n ψ
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  induction n with
  | zero =>
    intro W hW φ _
    obtain ⟨g, hg, x, hx⟩ := exists_eval_ne_zero ψ hW
    have hφg : φ = (mirabolicEval ψ 0 φ x / mirabolicEval ψ 0 g x) • g := by
      refine ext_eval ψ fun y => ?_
      rw [Subsingleton.elim y x]
      change _ = mirabolicEval ψ 0 φ x / mirabolicEval ψ 0 g x * mirabolicEval ψ 0 g x
      rw [div_mul_cancel₀ _ hx]
    rw [hφg]
    exact W.toSubmodule.smul_mem _ hg
  | succ m ih =>
    intro W hW φ hφ
    exact mem_of_forall_cut T ψ W φ hφ
      (exists_cut_of_one T ψ W (exists_cut_one T ψ ih W hW) φ hφ)

end Padic

end MirabolicMinimality
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement mirabolicCompactMinimality
open Langlands.AllField.Whittaker

open Langlands.Whittaker.MirabolicMinimality hiding compactMinimality exists_cut_of_one exists_cut_one mem_of_forall_cut realized_cut topologicalRing in
open Langlands.AllField.Whittaker.MirabolicMinimality in
/-- Bernstein–Zelevinsky (1976), Proposition 5.15(c), for the actual mirabolic smooth
induction over every nonarchimedean local field `F`, with the topology of every
supplied `T : LocalFieldData F`. -/
theorem mirabolicCompactMinimality : MirabolicCompactMinimalityStatement.{uF} := by
  intro F _ T
  exact compactMinimality T

end Langlands.AllField.Whittaker
