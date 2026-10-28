import Langlands.Representation.Whittaker.MirabolicMinimalityStatement
import Langlands.Representation.Whittaker.MirabolicCompactWhittakerUniqueness
import Langlands.Representation.Derivative.MirabolicLatticeBox
import Langlands.Representation.Derivative.MirabolicCharacter
import Langlands.Group.GL.MirabolicProjection
import Langlands.Group.GL.Padic
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientTopology

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

namespace Langlands.Whittaker.MirabolicMinimality

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology
open Langlands.Derivative.Mirabolic
open MirabolicWhittaker (rowOf)
open scoped Matrix

universe uF

section Generic

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
variable (ψ : UnitaryAdditiveCharacter K)

omit [IsTopologicalRing K] in
/-- Members of the smooth induction are determined by their values. -/
theorem ext_eval {n : ℕ} {f g : MirabolicSmoothFunctions ψ n}
    (h : ∀ x, mirabolicEval ψ n f x = mirabolicEval ψ n g x) : f = g :=
  Subtype.ext (Subtype.ext (funext h))

/-- Evaluation at one point, as a linear functional. -/
def evalLinear {n : ℕ} (x : mirabolic n K) : MirabolicSmoothFunctions ψ n →ₗ[ℂ] ℂ where
  toFun f := mirabolicEval ψ n f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalRing K] in
@[simp] theorem evalLinear_apply {n : ℕ} (x : mirabolic n K) (f : MirabolicSmoothFunctions ψ n) :
    evalLinear ψ x f = mirabolicEval ψ n f x := rfl

/-- Every member is fixed by right translation by some open subgroup. -/
theorem exists_fix {n : ℕ} (f : MirabolicSmoothFunctions ψ n) :
    ∃ L : OpenSubgroup (mirabolic n K), ∀ k ∈ L, ∀ x,
      mirabolicEval ψ n f (x * k) = mirabolicEval ψ n f x := by
  obtain ⟨L, hL⟩ := mirabolicSmoothInduced_smooth ψ n f
  refine ⟨L, fun k hk x => ?_⟩
  have h : mirabolicSmoothInduced ψ n k f = f :=
    (Representation.mem_invariants _ f).mp hL ⟨k, hk⟩
  rw [← mirabolicEval_translate, h]

/-- A nonzero subrepresentation has a member with a nonzero value. -/
theorem exists_eval_ne_zero {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    (hW : W ≠ ⊥) : ∃ g ∈ W.toSubmodule, ∃ x, mirabolicEval ψ n g x ≠ 0 := by
  have hW' : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.ext h)
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
  refine ⟨g, hg, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hg0 (ext_eval ψ fun x => hcon x)

/-! ### Functions realized by members of a subrepresentation -/

/-- `h` is the evaluation of some member of `W`. -/
def Realized {n : ℕ} (W : Subrepresentation (mirabolicSmoothInduced ψ n))
    (h : mirabolic n K → ℂ) : Prop :=
  ∃ g ∈ W.toSubmodule, ∀ x, mirabolicEval ψ n g x = h x

variable {ψ}

theorem realized_of_mem {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {g : MirabolicSmoothFunctions ψ n} (hg : g ∈ W.toSubmodule) :
    Realized ψ W (mirabolicEval ψ n g) :=
  ⟨g, hg, fun _ => rfl⟩

theorem mem_of_realized {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {g : MirabolicSmoothFunctions ψ n} (h : Realized ψ W (mirabolicEval ψ n g)) :
    g ∈ W.toSubmodule := by
  obtain ⟨g', hg', hgg'⟩ := h
  rwa [← ext_eval ψ hgg']

theorem realized_congr {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {h h' : mirabolic n K → ℂ} (H : Realized ψ W h) (e : ∀ x, h x = h' x) :
    Realized ψ W h' := by
  obtain ⟨g, hg, hgh⟩ := H
  exact ⟨g, hg, fun x => (hgh x).trans (e x)⟩

theorem realized_zero {n : ℕ} (W : Subrepresentation (mirabolicSmoothInduced ψ n)) :
    Realized ψ W (fun _ => 0) :=
  ⟨0, W.toSubmodule.zero_mem, fun _ => rfl⟩

theorem realized_add {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {h₁ h₂ : mirabolic n K → ℂ} (H₁ : Realized ψ W h₁) (H₂ : Realized ψ W h₂) :
    Realized ψ W (fun x => h₁ x + h₂ x) := by
  obtain ⟨g₁, hg₁, e₁⟩ := H₁
  obtain ⟨g₂, hg₂, e₂⟩ := H₂
  exact ⟨g₁ + g₂, W.toSubmodule.add_mem hg₁ hg₂, fun x => by
    show mirabolicEval ψ n (g₁ + g₂) x = h₁ x + h₂ x
    rw [← e₁, ← e₂]
    rfl⟩

theorem realized_sum {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {ι : Type*} (s : Finset ι) {h : ι → mirabolic n K → ℂ}
    (H : ∀ i ∈ s, Realized ψ W (h i)) : Realized ψ W (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact realized_congr (realized_zero W) fun x => by simp
  | insert a s ha ih =>
    refine realized_congr (realized_add (H a (Finset.mem_insert_self a s))
      (ih fun i hi => H i (Finset.mem_insert_of_mem hi))) fun x => ?_
    rw [Finset.sum_insert ha]

theorem realized_translate {n : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ n)}
    {h : mirabolic n K → ℂ} (H : Realized ψ W h) (s : mirabolic n K) :
    Realized ψ W (fun x => h (x * s)) := by
  obtain ⟨g, hg, e⟩ := H
  exact ⟨mirabolicSmoothInduced ψ n s g, W.apply_mem_toSubmodule s hg, fun x => by
    rw [mirabolicEval_translate, e]⟩

/-! ### The last row and the radical -/

open Classical in
/-- Multiply `h` by the indicator of `{x | rowOf x - v ∈ B}`. -/
def cut {m : ℕ} (B : AddSubgroup (Fin (m + 1) → K)) (v : Fin (m + 1) → K)
    (h : mirabolic (m + 1) K → ℂ) (x : mirabolic (m + 1) K) : ℂ :=
  if rowOf x - v ∈ B then h x else 0

omit [TopologicalSpace K] [IsTopologicalRing K] in
theorem row_mul {m : ℕ} (x y : mirabolic (m + 1) K) :
    rowOf (x * y) = rowOf x ᵥ* (projection y).val := by
  rw [rowOf, map_mul, lastRow_mul_eq_vecMul]
  rfl

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- The upper-left block of an upper unipotent matrix is upper unipotent. -/
theorem projection_mem_upperUnipotent {m : ℕ} (u : Mirabolic.upperUnipotent m K) :
    projection u.val ∈ GeneralLinear.upperUnipotent m K := by
  have hu : u.val.val ∈ GeneralLinear.upperUnipotent (m + 1) K := u.property
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact hu.1 (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · exact hu.2 i.castSucc

omit [IsTopologicalRing K] in
theorem eval_radicalElement_mul {m : ℕ} (f : MirabolicSmoothFunctions ψ (m + 1))
    (w : Fin (m + 1) → K) (y : mirabolic (m + 1) K) :
    mirabolicEval ψ (m + 1) f ((radicalElement w).val * y) =
      ψ.complex (w (Fin.last m)) * mirabolicEval ψ (m + 1) f y := by
  refine (mirabolicEval_covariance ψ (m + 1) f
    ⟨(radicalElement w).val, radical_le_upperUnipotent (radicalElement w).property⟩ y).trans ?_
  rw [MirabolicWhittaker.mirabolicCharacter_radicalElement]

omit [IsTopologicalRing K] in
/-- Right translation by the radical multiplies by `ψ(rowOf x ⬝ c)`. -/
theorem eval_mul_radicalElement {m : ℕ} (f : MirabolicSmoothFunctions ψ (m + 1))
    (x : mirabolic (m + 1) K) (c : Fin (m + 1) → K) :
    mirabolicEval ψ (m + 1) f (x * (radicalElement c).val) =
      ψ.complex (rowOf x ⬝ᵥ c) * mirabolicEval ψ (m + 1) f x := by
  have hx := eq_radicalElement_mul_levi x
  have hmul : x * (radicalElement c).val =
      (radicalElement ((projection x).val *ᵥ c)).val * x := by
    calc x * (radicalElement c).val
        = (radicalElement (lastColumn x)).val *
            (levi (projection x) * (radicalElement c).val) := by
          rw [← mul_assoc, ← hx]
      _ = (radicalElement (lastColumn x)).val *
            (radicalElement ((projection x).val *ᵥ c)).val * levi (projection x) := by
          rw [levi_mul_radicalElement, mul_assoc]
      _ = (radicalElement ((projection x).val *ᵥ c)).val *
            ((radicalElement (lastColumn x)).val * levi (projection x)) := by
          rw [← Subgroup.coe_mul, ← radicalElement_add, add_comm (lastColumn x),
            radicalElement_add, Subgroup.coe_mul, mul_assoc]
      _ = (radicalElement ((projection x).val *ᵥ c)).val * x := by rw [← hx]
  rw [hmul, eval_radicalElement_mul]
  rfl

/-! ### Restriction along the successor embedding -/

variable (ψ)

/-- Restriction along `successor : P_(m+1) → P_(m+2)`. -/
def res {m : ℕ} (f : MirabolicSmoothFunctions ψ (m + 1)) : MirabolicSmoothFunctions ψ m :=
  Induction.smoothFunctionOf _ _ (fun p => mirabolicEval ψ (m + 1) f (successor p))
    (fun u p => by
      change mirabolicEval ψ (m + 1) f (successor (u.val * p)) =
        (mirabolicCharacter ψ m u : ℂ) * mirabolicEval ψ (m + 1) f (successor p)
      rw [map_mul, ← MirabolicWhittaker.mirabolicCharacter_successor ψ u]
      exact mirabolicEval_covariance ψ (m + 1) f
        ⟨successor u.val, MirabolicWhittaker.successor_mem_upperUnipotent u.property⟩ _)
    ((Classical.choose (exists_fix ψ f)).comap successor continuous_successor)
    (fun k p => by
      change mirabolicEval ψ (m + 1) f (successor (p * k.val)) =
        mirabolicEval ψ (m + 1) f (successor p)
      rw [map_mul]
      exact Classical.choose_spec (exists_fix ψ f) _ k.property _)

@[simp] theorem res_eval {m : ℕ} (f : MirabolicSmoothFunctions ψ (m + 1)) (p : mirabolic m K) :
    mirabolicEval ψ m (res ψ f) p = mirabolicEval ψ (m + 1) f (successor p) := rfl

/-- Restriction as a linear map. -/
def resLinear (m : ℕ) : MirabolicSmoothFunctions ψ (m + 1) →ₗ[ℂ] MirabolicSmoothFunctions ψ m where
  toFun := res ψ
  map_add' _ _ := ext_eval ψ fun _ => rfl
  map_smul' _ _ := ext_eval ψ fun _ => rfl

theorem res_translate {m : ℕ} (h : mirabolic m K) (f : MirabolicSmoothFunctions ψ (m + 1)) :
    res ψ (mirabolicSmoothInduced ψ (m + 1) (successor h) f) =
      mirabolicSmoothInduced ψ m h (res ψ f) :=
  ext_eval ψ fun p => by
    rw [res_eval, mirabolicEval_translate, mirabolicEval_translate, res_eval, map_mul]

/-- The restriction of a subrepresentation, as a subrepresentation of the smaller rank. -/
def resRep {m : ℕ} (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))) :
    Subrepresentation (mirabolicSmoothInduced ψ m) where
  toSubmodule := W.toSubmodule.map (resLinear ψ m)
  apply_mem_toSubmodule h v hv := by
    obtain ⟨f, hf, rfl⟩ := hv
    exact ⟨_, W.apply_mem_toSubmodule (successor h) hf, res_translate ψ h f⟩

theorem resRep_ne_bot {m : ℕ} {W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))}
    (hW : W ≠ ⊥) : resRep ψ W ≠ ⊥ := by
  obtain ⟨g, hg, x, hx⟩ := exists_eval_ne_zero ψ hW
  intro hbot
  have hmem : res ψ (mirabolicSmoothInduced ψ (m + 1) x g) ∈ (resRep ψ W).toSubmodule :=
    ⟨_, W.apply_mem_toSubmodule x hg, rfl⟩
  rw [hbot] at hmem
  have h0 : res ψ (mirabolicSmoothInduced ψ (m + 1) x g) = 0 := (Submodule.mem_bot ℂ).mp hmem
  have h1 := congrArg (fun F => mirabolicEval ψ m F 1) h0
  simp only [res_eval, mirabolicEval_translate, map_one, one_mul] at h1
  exact hx h1

/-- Restriction preserves compact support modulo the unipotent subgroup. -/
theorem res_mem_compact [T2Space K] {m : ℕ}
    [LocallyCompactSpace (Langlands.GeneralLinear (m + 1 + 1) K)]
    (φ : MirabolicSmoothFunctions ψ (m + 1))
    (hφ : φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule) :
    res ψ φ ∈ (mirabolicCompactSubrepresentation ψ m).toSubmodule := by
  have : LocallyCompactSpace (mirabolic (m + 1) K) := Mirabolic.locallyCompactSpace
  have hφc : IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent (m + 1) K)
      (mirabolicEval ψ (m + 1) φ)) := hφ
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (m + 1) K) Mirabolic.upperUnipotent_isClosed hφc
  let D : Set (mirabolic m K) := Subtype.val ⁻¹' (projection '' C)
  have hD : IsCompact D :=
    (Mirabolic.isClosed (F := K) (n := m)).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hC.image continuous_projection)
  have hQ : Continuous (Induction.quotientMap (Mirabolic.upperUnipotent m K)) :=
    continuous_quot_mk
  apply (hD.image hQ).of_isClosed_subset
    (Induction.isClosed_quotientSupport _ _ (res ψ φ))
  rintro _ ⟨p, hp, rfl⟩
  have hmem : Induction.quotientMap _ (successor p) ∈
      Induction.quotientSupport (Mirabolic.upperUnipotent (m + 1) K)
        (mirabolicEval ψ (m + 1) φ) := ⟨successor p, hp, rfl⟩
  rw [← hCimg] at hmem
  obtain ⟨c, hc, hcp⟩ := hmem
  have hu : successor p * c⁻¹ ∈ Mirabolic.upperUnipotent (m + 1) K := by
    have h' : QuotientGroup.rightRel _ c (successor p) := Quotient.exact hcp
    rwa [QuotientGroup.rightRel_apply] at h'
  let u : Mirabolic.upperUnipotent (m + 1) K := ⟨_, hu⟩
  have hpu : projection u.val = p.val * (projection c)⁻¹ := by
    change projection (successor p * c⁻¹) = _
    rw [map_mul, map_inv, projection_successor]
  have hcproj : projection c ∈ mirabolic m K := by
    have he : projection c = (projection u.val)⁻¹ * p.val := by
      rw [hpu]
      group
    rw [he]
    exact (mirabolic m K).mul_mem
      ((mirabolic m K).inv_mem (upperUnipotent_le_mirabolic (projection_mem_upperUnipotent u)))
      p.property
  refine ⟨⟨projection c, hcproj⟩, ⟨c, hc, rfl⟩, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel _ _ _
  rw [QuotientGroup.rightRel_apply]
  change (p * ⟨projection c, hcproj⟩⁻¹ : mirabolic m K).val ∈
    GeneralLinear.upperUnipotent (m + 1) K
  have he : (p * ⟨projection c, hcproj⟩⁻¹ : mirabolic m K).val = projection u.val := by
    rw [hpu]
    rfl
  rw [he]
  exact projection_mem_upperUnipotent u

omit [IsTopologicalRing K] in
/-- Two members with the same restriction agree wherever the last row comes from a Levi
subgroup fixing both. -/
theorem eval_eq_of_res_eq {m : ℕ} (f φ : MirabolicSmoothFunctions ψ (m + 1))
    (hres : ∀ p, mirabolicEval ψ (m + 1) f (successor p) =
      mirabolicEval ψ (m + 1) φ (successor p))
    (J : Subgroup (Langlands.GeneralLinear (m + 1) K))
    (hfJ : ∀ j ∈ J, ∀ x, mirabolicEval ψ (m + 1) f (x * levi j) = mirabolicEval ψ (m + 1) f x)
    (hφJ : ∀ j ∈ J, ∀ x, mirabolicEval ψ (m + 1) φ (x * levi j) = mirabolicEval ψ (m + 1) φ x)
    (x : mirabolic (m + 1) K) (hx : rowOf x ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) K))) :
    mirabolicEval ψ (m + 1) f x = mirabolicEval ψ (m + 1) φ x := by
  obtain ⟨a, j, hj⟩ := (lastRow_mem_image_iff J (projection x)).mp hx
  have hx' : x = (radicalElement (lastColumn x)).val * successor a * levi j.val := by
    conv_lhs => rw [eq_radicalElement_mul_levi x]
    rw [hj, map_mul, ← mul_assoc]
    rfl
  rw [hx', hfJ _ j.property, hφJ _ j.property, eval_radicalElement_mul, eval_radicalElement_mul,
    hres]

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem topologicalRing : @IsTopologicalRing F.Carrier T.topology _ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Cutting a realized function by a lattice box of last rows keeps it realized. -/
theorem realized_cut :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1)))
      {h : mirabolic (m + 1) F.Carrier → ℂ}, Realized ψ W h →
      ∀ (v : Fin (m + 1) → F.Carrier) (N : ℤ), Realized ψ W (cut (latticeBox T (m + 1) N) v h) := by
  intro ψ m W h hh v N
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  obtain ⟨g, hgW, hgh⟩ := hh
  obtain ⟨Lg, hLg⟩ := exists_fix ψ g
  -- A box of radical coordinates fixing `g`.
  have hrad0 : {c : Fin (m + 1) → F.Carrier |
      ((radicalElement c : radical (m + 1) F.Carrier) : mirabolic (m + 1) F.Carrier) ∈ Lg} ∈
        𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (Lg.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact Lg.one_mem
  obtain ⟨l₁, hl₁⟩ := exists_latticeBox_subset T hrad0
  -- A box on which `c ↦ ψ(v ⬝ c)` is trivial.
  have hv0 : {c : Fin (m + 1) → F.Carrier |
      v ⬝ᵥ c ∈ T.additiveLattice (T.additiveConductor ψ)} ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
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
    ∑ c : B ⧸ L, ψ.complex (-(v ⬝ᵥ ((c.out : B) : Fin (m + 1) → F.Carrier))) •
      mirabolicSmoothInduced ψ (m + 1)
        (radicalElement ((c.out : B) : Fin (m + 1) → F.Carrier)).val g
  refine ⟨g', ?_, fun x => ?_⟩
  · exact W.toSubmodule.smul_mem _ (W.toSubmodule.sum_mem fun c _ =>
      W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule _ hgW))
  have heval : mirabolicEval ψ (m + 1) g' x = (Fintype.card (B ⧸ L) : ℂ)⁻¹ *
      ∑ c : B ⧸ L, ψ.complex ((rowOf x - v) ⬝ᵥ ((c.out : B) : Fin (m + 1) → F.Carrier)) *
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
    ((AddMonoidHom.mk' (fun c : Fin (m + 1) → F.Carrier => (rowOf x - v) ⬝ᵥ c)
      (fun a b => dotProduct_add _ a b)).comp B.subtype)
  have hχ : ∀ c : B, χ c = ψ.complex ((rowOf x - v) ⬝ᵥ (c : Fin (m + 1) → F.Carrier)) :=
    fun _ => rfl
  have hsum_eq : ∑ c : B ⧸ L, ψ.complex ((rowOf x - v) ⬝ᵥ ((c.out : B) : Fin (m + 1) → F.Carrier)) =
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
      have hcl : (c : Fin (m + 1) → F.Carrier) ∈ latticeBox T (m + 1) l := hc
      rw [hχ, sub_dotProduct, AddChar.map_sub_eq_div, hψrow _ (hl₁' hcl), hψv _ (hl₂' hcl),
        div_one]
    rw [heval, cut, ite_eq_right hin, ← Finset.sum_mul, hsum_eq, hsum, zero_mul, mul_zero]

/-- Core step: near the standard last row, a compact function is cut into `W`. -/
theorem exists_cut_one :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ},
      (∀ W' : Subrepresentation (mirabolicSmoothInduced ψ m), W' ≠ ⊥ →
        mirabolicCompactSubrepresentation ψ m ≤ W') →
      ∀ (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))), W ≠ ⊥ →
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
        ∃ N : ℤ, Realized ψ W (cut (latticeBox T (m + 1) N)
          (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier)) (mirabolicEval ψ (m + 1) φ)) := by
  intro ψ m ih W hW φ hφ
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : LocallyCompactSpace (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (m + 1 + 1)
  have hres := res_mem_compact ψ φ hφ
  obtain ⟨f, hfW, hfφ⟩ := ih (resRep ψ W) (resRep_ne_bot ψ hW) hres
  obtain ⟨Lf, hLf⟩ := exists_fix ψ f
  obtain ⟨Lφ, hLφ⟩ := exists_fix ψ φ
  let J : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier) :=
    Lf.toSubgroup.comap levi ⊓ Lφ.toSubgroup.comap levi
  have hJopen : IsOpen (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    (Lf.isOpen.preimage continuous_levi).inter (Lφ.isOpen.preimage continuous_levi)
  have hagree : ∀ x, rowOf x ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) →
      mirabolicEval ψ (m + 1) f x = mirabolicEval ψ (m + 1) φ x :=
    eval_eq_of_res_eq ψ f φ (fun p => congrArg (fun F => mirabolicEval ψ m F p) hfφ) J
      (fun j hj x => hLf _ hj.1 x) (fun j hj x => hLφ _ hj.2 x)
  have hnhds : lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) ∈
      𝓝 (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    lastRow_image_mem_nhds hJopen J.one_mem
  have hnhds0 : {d : Fin (m + 1) → F.Carrier |
      lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) + d ∈
        lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier))} ∈
      𝓝 (0 : Fin (m + 1) → F.Carrier) :=
    (continuous_const.add continuous_id).tendsto' (0 : Fin (m + 1) → F.Carrier) _
      (add_zero _) hnhds
  obtain ⟨N, hN⟩ := exists_latticeBox_subset T hnhds0
  refine ⟨N, realized_congr (realized_cut T ψ W (realized_of_mem hfW)
    (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier)) N) fun x => ?_⟩
  by_cases hx : rowOf x - lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) ∈
      latticeBox T (m + 1) N
  · have hrow : rowOf x ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) := by
      have h1 := hN hx
      simpa using h1
    rw [cut, cut, ite_eq_left hx, ite_eq_left hx, hagree x hrow]
  · rw [cut, cut, ite_eq_right hx, ite_eq_right hx]

/-- Translation by the Levi moves the core step to every last row. -/
theorem exists_cut_of_one :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))),
      (∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
        ∃ N : ℤ, Realized ψ W (cut (latticeBox T (m + 1) N)
          (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier)) (mirabolicEval ψ (m + 1) φ))) →
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
      ∀ x₀ : mirabolic (m + 1) F.Carrier,
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
  have hnhds : {d : Fin (m + 1) → F.Carrier |
      d ᵥ* ((projection x₀)⁻¹ : Langlands.GeneralLinear (m + 1) F.Carrier).val ∈
        latticeBox T (m + 1) N} ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply ((isOpen_latticeBox T (m + 1) N).preimage
      (continuous_id.matrix_vecMul continuous_const)).mem_nhds
    simp only [Set.mem_preimage, id_eq, Matrix.zero_vecMul, SetLike.mem_coe]
    exact (latticeBox T (m + 1) N).zero_mem
  obtain ⟨N', hN'⟩ := exists_latticeBox_subset T hnhds
  refine ⟨N', realized_congr (realized_cut T ψ W h1 (rowOf x₀) N') fun x => ?_⟩
  by_cases hx : rowOf x - rowOf x₀ ∈ latticeBox T (m + 1) N'
  · have hrow : rowOf (x * (levi (projection x₀))⁻¹) -
        lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) =
        (rowOf x - rowOf x₀) ᵥ* ((projection x₀)⁻¹ : Langlands.GeneralLinear (m + 1) F.Carrier).val := by
      rw [row_mul, map_inv, projection_levi, Matrix.sub_vecMul]
      congr 1
      rw [rowOf, ← lastRow_mul_eq_vecMul, mul_inv_cancel]
    have hin : rowOf (x * (levi (projection x₀))⁻¹) -
        lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) ∈ latticeBox T (m + 1) N := by
      rw [hrow]
      exact hN' hx
    rw [cut, cut, ite_eq_left hx, ite_eq_left hin, cut, ite_eq_left hx, mirabolicEval_translate,
      inv_mul_cancel_right]
  · rw [cut, cut, ite_eq_right hx, cut, ite_eq_right hx]

theorem mk_eq_mk_iff {G : Type*} [AddCommGroup G] (s : AddSubgroup G) (a b : G) :
    (QuotientAddGroup.mk a : G ⧸ s) = QuotientAddGroup.mk b ↔ a - b ∈ s := by
  rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add_rev, neg_neg, neg_add_eq_sub]

/-- Compactness: local cuts at every last row assemble the whole compact function. -/
theorem mem_of_forall_cut :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := topologicalRing T
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ}
      (W : Subrepresentation (mirabolicSmoothInduced ψ (m + 1))),
      ∀ φ ∈ (mirabolicCompactSubrepresentation ψ (m + 1)).toSubmodule,
      (∀ x₀ : mirabolic (m + 1) F.Carrier, ∃ N : ℤ,
        Realized ψ W (cut (latticeBox T (m + 1) N) (rowOf x₀) (mirabolicEval ψ (m + 1) φ))) →
      φ ∈ W.toSubmodule := by
  intro ψ m W φ hφ hloc
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  classical
  have : LocallyCompactSpace (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (m + 1 + 1)
  have : LocallyCompactSpace (mirabolic (m + 1) F.Carrier) := Mirabolic.locallyCompactSpace
  have hφc : IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent (m + 1) F.Carrier)
      (mirabolicEval ψ (m + 1) φ)) := hφ
  obtain ⟨C, hC, hCimg⟩ := QuotientIntegration.leftQuotient_exists_isCompact_image
    (Mirabolic.upperUnipotent (m + 1) F.Carrier) Mirabolic.upperUnipotent_isClosed hφc
  choose N hN using hloc
  have hrowc : Continuous (rowOf : mirabolic (m + 1) F.Carrier → Fin (m + 1) → F.Carrier) :=
    continuous_lastRow.comp continuous_projection
  have hnhds : ∀ (k : ℤ) (x₀ : mirabolic (m + 1) F.Carrier),
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
  let Q := (Fin (m + 1) → F.Carrier) ⧸ latticeBox T (m + 1) L
  let S : Finset Q := t₂.image fun x₁ => (QuotientAddGroup.mk (rowOf x₁) : Q)
  have hsupp : ∀ x, mirabolicEval ψ (m + 1) φ x ≠ 0 →
      (QuotientAddGroup.mk (rowOf x) : Q) ∈ S := by
    intro x hx
    have hmem : Induction.quotientMap _ x ∈ Induction.quotientSupport
        (Mirabolic.upperUnipotent (m + 1) F.Carrier) (mirabolicEval ψ (m + 1) φ) :=
      ⟨x, hx, rfl⟩
    rw [← hCimg] at hmem
    obtain ⟨c, hc, hcx⟩ := hmem
    have hu : x * c⁻¹ ∈ Mirabolic.upperUnipotent (m + 1) F.Carrier := by
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

/-- Compact minimality for every rank and every topological realization. -/
theorem compactMinimality :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := topologicalRing T
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
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

open MirabolicMinimality in
/-- Bernstein–Zelevinsky (1976), Proposition 5.15(c), for the actual mirabolic smooth
induction over every p-adic field with its canonical topology. -/
theorem mirabolicCompactMinimality : MirabolicCompactMinimalityStatement.{uF} := by
  intro p hp F
  exact compactMinimality F.canonicalTopologicalData

end Langlands.Whittaker
