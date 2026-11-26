import Langlands.Global.AdelicStandardCosetShift
import Langlands.Analysis.L2IndependentSlabs

/-! # Slab estimates for functions on `P₀(F) U_J(𝔸) \ G(𝔸)`

For finitely many points `b_i` of `G(𝔸)` commuting with `L_J(𝔸)` and normalizing `U_J(𝔸)`,
heights `ht_i` on `G(𝔸)` left invariant under `P₀(F) U_J(𝔸)` with `ht_j(b_i g) = ht_j(g) + δ_{ij}`,
and a weight `W` with `W(g) = κ_i W(b_i g)`, the estimate of `L2IndependentSlabs` holds for
functions on `G(𝔸)` left invariant under `P₀(F) U_J(𝔸)`, against `W · Haar` on the
fundamental domain of `P₀(F)` (Bernstein–Lapid §7.5, Corollary and Proposition).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Analysis.CosetSpaceShift

variable {A : Type*} [Group A] [MeasurableSpace A] (H : Subgroup A)

theorem shift_iterate_mk (a : A) (ha : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (k : ℕ) (g : A) :
    (shift H a ha)^[k] (mk H g) = mk H (a ^ k * g) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, shift_mk, ih, ← mul_assoc, ← pow_succ]

end Langlands.Analysis.CosetSpaceShift

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis Langlands.Analysis.L2IndependentSlabs

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "A" => AdelicGroupPoints F G

/-- The residual `g ↦ φ(b^m g) + ∑_{k<m} p_k φ(b^k g)` of a monic difference equation for left
translation by `b`. -/
def residualFun (b : A) {m : ℕ} (p : Fin m → ℂ) (φ : A → ℂ) : A → ℂ :=
  fun g => φ (b ^ m * g) + ∑ k, p k * φ (b ^ (k : ℕ) * g)

variable {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i} {hν : IsGenericCocharacter i ν}

include hG hi hν in
/-- **Slab estimate for `P₀(F) U_J(𝔸)`-invariant functions.** Under the hypotheses above and the
sufficient coefficient bound `∑_k ‖p_{ik}‖ fᵢᵏ < fᵢ^{mᵢ}` with `fᵢ = √(κᵢ c(bᵢ))`, there is a
constant `C ≥ 1` such that every measurable invariant `φ` that is square integrable on the
box `{0 < htᵢ ≤ mᵢ ∀ i}` and whose residuals are square integrable on `{htᵢ > 0 ∀ i}` is
square integrable there, with norm at most `C` times the sum of these norms. -/
theorem exists_slabEstimate {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {I : Type*} [Fintype I] [DecidableEq I] (b : I → A)
    (hlevi : ∀ k, ∀ x ∈ adelicPoints F G (standardLevi i ν J), b k * x = x * b k)
    (hb : ∀ k, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      b k * w * (b k)⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (hb' : ∀ k, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      (b k)⁻¹ * w * b k ∈ adelicPoints F G (standardUnipotent i ν J))
    {W : A → ℝ≥0∞} (hWm : Measurable W) (hWH : ∀ h ∈ cosetSubgroup F G i ν J, ∀ g, W (h * g) = W g)
    (κ : I → ℝ≥0) (hκ : ∀ k, 0 < κ k) (hW : ∀ k g, W g = κ k * W (b k * g))
    (ht : I → A → ℝ) (htm : ∀ k, Measurable (ht k))
    (htH : ∀ k, ∀ h ∈ cosetSubgroup F G i ν J, ∀ g, ht k (h * g) = ht k g)
    (hta : ∀ k l g, ht l (b k * g) = ht l g + if k = l then 1 else 0)
    (m : I → ℕ) (p : ∀ k, Fin (m k) → ℂ)
    (hsmall : ∀ k,
      haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
      haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
        hcl.locallyCompactSpace
      ∑ q, ‖p k q‖ * (NNReal.sqrt (κ k * mulEquivHaarChar (conjPoints F G (b k) (hb k) (hb' k))) :
        ℝ) ^ (q : ℕ) <
        (NNReal.sqrt (κ k * mulEquivHaarChar (conjPoints F G (b k) (hb k) (hb' k))) : ℝ) ^ m k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {φ : A → ℂ}, Measurable φ →
      (∀ h ∈ cosetSubgroup F G i ν J, ∀ g, φ (h * g) = φ g) →
      MemLp φ 2 ((domainWeightedHaar F G i ν W).restrict {g | ∀ k, 0 < ht k g ∧ ht k g ≤ m k}) →
      (∀ k, MemLp (residualFun F G (b k) (p k) φ) 2
        ((domainWeightedHaar F G i ν W).restrict {g | ∀ k, 0 < ht k g})) →
      MemLp φ 2 ((domainWeightedHaar F G i ν W).restrict {g | ∀ k, 0 < ht k g}) ∧
        lpNorm φ 2 ((domainWeightedHaar F G i ν W).restrict {g | ∀ k, 0 < ht k g}) ≤
          C * (lpNorm φ 2 ((domainWeightedHaar F G i ν W).restrict
              {g | ∀ k, 0 < ht k g ∧ ht k g ≤ m k}) +
            ∑ k, lpNorm (residualFun F G (b k) (p k) φ) 2
              ((domainWeightedHaar F G i ν W).restrict {g | ∀ k, 0 < ht k g})) := by
  set Hs := cosetSubgroup F G i ν J
  set μW := domainWeightedHaar F G i ν W
  set μX := Measure.map (CosetSpaceShift.mk Hs) μW
  have hconj (k : I) : ∀ h ∈ Hs, b k * h * (b k)⁻¹ ∈ Hs := fun _ hh =>
    conj_mem_cosetSubgroup F G i ν (hG := hG) (hi := hi) (hν := hν) hJ (b k) (hlevi k) (hb k) hh
  let t : Finset I := Finset.univ
  let Sh : (↑t : Type _) → L2RenormalizingShift μX := fun k =>
    standardRenormalizingShift F G i ν (hG := hG) (hi := hi) (hν := hν) hJ (b k.1) (hlevi k.1)
      (hb k.1) (hb' k.1) hWm hWH (κ k.1) (hκ k.1) (hW k.1) (ht k.1) (htm k.1) (htH k.1)
      (fun g => by simpa using hta k.1 k.1 g)
  have hind : Independent Sh := by
    intro k l hkl x
    induction x using Quotient.inductionOn with
    | h g =>
      have hne : k.1 ≠ l.1 := fun h => hkl (Subtype.ext h)
      change ht l.1 (b k.1 * g) = ht l.1 g
      simp [hta k.1 l.1 g, hne]
  obtain ⟨C, hC1, hC⟩ := l2IndependentSlabs Sh hind m p (fun k => hsmall k.1)
  refine ⟨C, hC1, fun {φ} hφm hφH hbox hres => ?_⟩
  let φX := CosetSpaceShift.lift Hs φ hφH
  have hφX : StronglyMeasurable φX := (CosetSpaceShift.measurable_lift Hs hφH hφm).stronglyMeasurable
  -- the regions of the coset space and their preimages
  have hpos_pre : CosetSpaceShift.mk Hs ⁻¹' positiveRegion Sh = {g | ∀ k, 0 < ht k g} := by
    ext g
    simp only [positiveRegion, L2RenormalizingShift.positive, mem_preimage, mem_iInter, mem_Ioi,
      mem_ofPred_eq]
    constructor
    · intro h k
      exact h ⟨k, Finset.mem_univ k⟩
    · intro h k
      exact h k.1
  have hbox_pre : CosetSpaceShift.mk Hs ⁻¹' boundaryBox Sh m =
      {g | ∀ k, 0 < ht k g ∧ ht k g ≤ m k} := by
    ext g
    simp only [boundaryBox, L2RenormalizingShift.slab, mem_preimage, mem_iInter, mem_Ioc,
      mem_ofPred_eq]
    constructor
    · intro h k
      exact h ⟨k, Finset.mem_univ k⟩
    · intro h k
      exact h k.1
  have hposX : μX.restrict (positiveRegion Sh) =
      Measure.map (CosetSpaceShift.mk Hs) (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    rw [CosetSpaceShift.restrict_map_mk Hs μW (measurable_positiveRegion Sh), hpos_pre]
  have hboxX : μX.restrict (boundaryBox Sh m) =
      Measure.map (CosetSpaceShift.mk Hs) (μW.restrict {g | ∀ k, 0 < ht k g ∧ ht k g ≤ m k}) := by
    rw [CosetSpaceShift.restrict_map_mk Hs μW (measurable_boundaryBox Sh m), hbox_pre]
  -- residuals descend
  have hresComp (k : (↑t : Type _)) :
      (Sh k).residual (p k.1) φX ∘ CosetSpaceShift.mk Hs = residualFun F G (b k.1) (p k.1) φ := by
    funext g
    simp only [Function.comp_apply, L2RenormalizingShift.residual, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, residualFun]
    change φX ((Sh k).shift^[m k.1] (CosetSpaceShift.mk Hs g)) +
        ∑ q, p k.1 q * φX ((Sh k).shift^[(q : ℕ)] (CosetSpaceShift.mk Hs g)) = _
    change φX ((CosetSpaceShift.shift Hs (b k.1) (hconj k.1))^[m k.1] (CosetSpaceShift.mk Hs g)) +
        ∑ q, p k.1 q * φX ((CosetSpaceShift.shift Hs (b k.1) (hconj k.1))^[(q : ℕ)]
          (CosetSpaceShift.mk Hs g)) = _
    simp only [CosetSpaceShift.shift_iterate_mk]
    rfl
  have hresm (k : (↑t : Type _)) : Measurable ((Sh k).residual (p k.1) φX) := by
    unfold L2RenormalizingShift.residual
    refine Measurable.add (hφX.measurable.comp ((Sh k).measurable_shift.iterate _)) ?_
    have hs := Finset.measurable_sum
      (f := fun (q : Fin (m k.1)) (x : CosetSpaceShift.Space Hs) =>
        (p k.1 q • φX ∘ (Sh k).shift^[(q : ℕ)]) x) Finset.univ fun q _ =>
      ((hφX.measurable.comp ((Sh k).measurable_shift.iterate _)).const_smul _)
    convert hs using 1
    ext x
    simp only [Finset.sum_apply]
  have hres_eLp (k : (↑t : Type _)) :
      eLpNorm ((Sh k).residual (p k.1) φX) 2 (μX.restrict (positiveRegion Sh)) =
        eLpNorm (residualFun F G (b k.1) (p k.1) φ) 2 (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    rw [hposX, eLpNorm_map_measure (hresm k).aestronglyMeasurable
      (CosetSpaceShift.measurable_mk Hs).aemeasurable, hresComp]
  have hres_mem (k : (↑t : Type _)) :
      MemLp ((Sh k).residual (p k.1) φX) 2 (μX.restrict (positiveRegion Sh)) ↔
        MemLp (residualFun F G (b k.1) (p k.1) φ) 2 (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    rw [hposX, memLp_map_measure_iff (hresm k).aestronglyMeasurable
      (CosetSpaceShift.measurable_mk Hs).aemeasurable, hresComp]
  have hboxmem : MemLp φX 2 (μX.restrict (boundaryBox Sh m)) := by
    rw [hboxX, CosetSpaceShift.memLp_lift_iff Hs _ 2 hφH hφm]
    exact hbox
  obtain ⟨hmem, hle⟩ := hC hφX hboxmem fun k => (hres_mem k).mpr (hres k.1)
  have hposmem : MemLp φ 2 (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    rw [hposX, CosetSpaceShift.memLp_lift_iff Hs _ 2 hφH hφm] at hmem
    exact hmem
  refine ⟨hposmem, ?_⟩
  have e1 : lpNorm φX 2 (μX.restrict (positiveRegion Sh)) =
      lpNorm φ 2 (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    rw [lpNorm, lpNorm, hposX, CosetSpaceShift.eLpNorm_lift Hs _ 2 hφH hφm]
  have e2 : lpNorm φX 2 (μX.restrict (boundaryBox Sh m)) =
      lpNorm φ 2 (μW.restrict {g | ∀ k, 0 < ht k g ∧ ht k g ≤ m k}) := by
    rw [lpNorm, lpNorm, hboxX, CosetSpaceShift.eLpNorm_lift Hs _ 2 hφH hφm]
  have e3 : ∑ k : (↑t : Type _), lpNorm ((Sh k).residual (p k.1) φX) 2
        (μX.restrict (positiveRegion Sh)) =
      ∑ k, lpNorm (residualFun F G (b k) (p k) φ) 2 (μW.restrict {g | ∀ k, 0 < ht k g}) := by
    simp only [lpNorm, hres_eLp]
    exact Finset.sum_coe_sort Finset.univ
      (fun k => (eLpNorm (residualFun F G (b k) (p k) φ) 2
        (μW.restrict {g | ∀ k, 0 < ht k g})).toReal)
  rw [e1, e2, e3] at hle
  exact hle

end Langlands.Global.StandardConstantTerm
