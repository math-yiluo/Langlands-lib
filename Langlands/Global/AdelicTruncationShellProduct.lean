import Langlands.Global.AdelicTruncationShellBounds
import Langlands.LinearAlgebra.ArthurCombinatoricsSigma

/-! # Levi and split components of a characteristic truncation shell -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical Pointwise

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace ArthurRelative

variable {F : Type*} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  (J : Global.StandardIndex F G i ν)

local notation "Δ" => simpleRelativeRoots i ν
local notation "π" => levelProjection hG hi ν D J.val
local notation "L" => corootSubspace D J.val
local notation "A" => aSpace T J.val
local notation "w" => weight hG hi ν D

/-- The characteristic chamber for the Levi of `J`, expressed in its coroot subspace.
The two cutoffs are projected onto that subspace. -/
def characteristicLeviChamber (T₀ Tp : V T) : Set (V T) :=
  {X | X ∈ L ∧ ∀ α ∈ J.val,
    0 ≤ eval T α (X - (T₀ - π T₀)) ∧ w J.val α (X - (Tp - π Tp)) ≤ 0}

/-- The strictly dominant split cone translated by the split part of the truncation parameter. -/
def characteristicSplitChamber (Tp : V T) : Set (V T) :=
  {Y | Y ∈ D.realCorootSpan ∧ Y ∈ A ∧ ∀ α ∈ Δ \ J.val, 0 < eval T α (Y - π Tp)}

/-- The part of the translated split cone cut out by the upper weights outside the Levi.
These weights take the same value on `Tp + S` and its split projection. -/
def characteristicSplitShell (Tp S : V T) : Set (V T) :=
  characteristicSplitChamber hG hi D J Tp ∩
    {Y | ∀ α ∈ Δ \ J.val, w Δ α (Y - π (Tp + S)) ≤ 0}

private theorem levi_le_corootSpan : L ≤ D.realCorootSpan := by
  apply Submodule.span_mono
  rintro _ ⟨α, _, rfl⟩
  exact ⟨α, rfl⟩

private theorem split_mem_corootSpan {X : V T} (hX : X ∈ D.realCorootSpan) :
    π X ∈ D.realCorootSpan := by
  have h := levi_le_corootSpan D J (sub_levelProjection_mem_span hG hi (ν := ν) D J.val X)
  convert D.realCorootSpan.sub_mem hX h using 1
  abel

private theorem split_eq_zero (hν : IsGenericCocharacter i ν) {X : V T} (hX : X ∈ L) :
    π X = 0 := by
  rw [← levelProjection_eq_projectionOnto hG hi hν D J.property,
    Submodule.projectionOnto_apply_of_mem_right _ hX]
  rfl

private theorem split_eq_self (hν : IsGenericCocharacter i ν) {X : V T} (hX : X ∈ A) :
    π X = X := by
  rw [← levelProjection_eq_projectionOnto hG hi hν D J.property,
    Submodule.projectionOnto_apply_of_mem_left _ hX]

private theorem eval_split_eq_zero (hν : IsGenericCocharacter i ν) (X : V T)
    {α : characterLattice T} (hα : α ∈ J.val) : eval T α (π X) = 0 :=
  (mem_rootAnnihilator _ _).mp (levelProjection_mem_rootAnnihilator hG hi D hν J.property X) α hα

private theorem weight_split_eq_zero (hν : IsGenericCocharacter i ν) (X : V T)
    (α : characterLattice T) : w J.val α (π X) = 0 :=
  weight_eq_zero_of_mem_rootAnnihilator hG hi ν D J.val α
    (levelProjection_mem_rootAnnihilator hG hi D hν J.property X)

private theorem weight_split_eq (hν : IsGenericCocharacter i ν) (X : V T)
    {α : characterLattice T} (hα : α ∈ Δ \ J.val) : w Δ α (π X) = w Δ α X := by
  have hspan : L ≤ LinearMap.ker (w Δ α) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    have hne : α ≠ (β : characterLattice T) := fun he => hα.2 (he.symm ▸ hβ)
    change w Δ α (D.realCoroot β) = 0
    rw [weight_coroot hG hi D hν subset_rfl hα.1 β (J.property hβ),
      ite_eq_right hne]
  have he := hspan (sub_levelProjection_mem_span hG hi (ν := ν) D J.val X)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at he
  exact he.symm

private theorem eval_levi_nonneg (hν : IsGenericCocharacter i ν) {H : V T}
    (hH : ∀ β ∈ J.val, w J.val β H ≤ 0)
    {α : characterLattice T} (hα : α ∈ Δ \ J.val) : 0 ≤ eval T α (H - π H) := by
  have he : H - π H = ∑ β : standardIndex hG hi ν J.val,
      w J.val β.1 H • D.realCoroot ⟨β.1.1, β.1.2.1⟩ := by
    simp only [levelProjection, LinearMap.sub_apply, LinearMap.id_apply, sub_sub_cancel,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, weight_coe]
  rw [he, map_sum]
  apply Finset.sum_nonneg
  intro β _
  have hβ := (mem_standardIndex hG hi ν).mp β.2
  rw [map_smul, smul_eq_mul]
  apply mul_nonneg_of_nonpos_of_nonpos (hH β.1 hβ.2)
  have hne : (⟨α, hα.1⟩ : simpleRelativeRoots i ν) ≠ ⟨β.1.1, hβ.1⟩ := by
    intro heq
    have hab : α = β.1.1 := congrArg Subtype.val heq
    exact hα.2 (hab.symm ▸ hβ.2)
  rw [eval_eq_pair, D.pair_tmul_realCoroot, one_mul]
  exact_mod_cast D.simple_pairing_nonpos i ν hi.isSplitSubtorus.1
    (finite_relativeRoots hG hi) hν ⟨α, hα.1⟩ ⟨β.1.1, hβ.1⟩ hne

private theorem leviWeight_nonneg (hν : IsGenericCocharacter i ν) {S : V T}
    (hS : ∀ β ∈ J.val, 0 ≤ eval T β S) (α : characterLattice T) (hα : α ∈ J.val) :
    0 ≤ w J.val α S := by
  let := finite_indivisibleRoots hG hi
  let a : RelativeRoot.indivisibleRoots i := ⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν
    (J.property hα)⟩
  rw [← neg_nonpos, ← map_neg, show α = (a : characterLattice T) from rfl, weight_coe]
  apply ArthurCombinatorics.weightCoordinate_nonpos (base hG hi hν D)
    (standardIndex_subset_support hG hi D hν J.val)
  intro β hβ
  have he := eval_sub_toCorootSpan hG hi D β.2.1 (-S)
  rw [map_sub, sub_eq_zero] at he
  calc
    _ = eval T β.1 (toCorootSpan hG hi D (-S)) := by rw [eval_eq_pair]; rfl
    _ = eval T β.1 (-S) := he.symm
    _ ≤ 0 := by
      rw [map_neg, neg_nonpos]
      exact hS β.1 ((mem_standardIndex hG hi ν).mp hβ).2

/-- Once the outside weights are nonpositive, each full Levi-indexed weight is at
most its Levi counterpart. Apply the comparison of inverse Cartan blocks to `-H`. -/
private theorem fullWeight_le_leviWeight (hν : IsGenericCocharacter i ν) {H : V T}
    (hH : ∀ β ∈ Δ \ J.val, w Δ β H ≤ 0) {α : characterLattice T} (hα : α ∈ J.val) :
    w Δ α H ≤ w J.val α H := by
  let := finite_indivisibleRoots hG hi
  let a : RelativeRoot.indivisibleRoots i := ⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν
    (J.property hα)⟩
  have hsub : standardIndex hG hi ν J.val ⊆ standardIndex hG hi ν Δ :=
    standardIndex_mono hG hi ν J.property
  have ha : a ∈ standardIndex hG hi ν J.val :=
    (mem_standardIndex hG hi ν).mpr ⟨J.property hα, hα⟩
  rw [← neg_le_neg_iff, ← map_neg, ← map_neg, show α = (a : characterLattice T) from rfl,
    weight_coe, weight_coe]
  apply ArthurCombinatorics.weightCoordinate_le_of_subset (base hG hi hν D) hsub
    (standardIndex_subset_support hG hi D hν Δ) ha
  intro β hβ
  obtain ⟨hβD, hβJ⟩ := Finset.mem_sdiff.mp hβ
  have hΔ := ((mem_standardIndex hG hi ν).mp hβD).1
  rw [← weight_coe, map_neg, neg_nonneg]
  exact hH β.1 ⟨hΔ, fun he => hβJ ((mem_standardIndex hG hi ν).mpr ⟨hΔ, he⟩)⟩

private theorem parabolicCharacteristicChamber_iff (hν : IsGenericCocharacter i ν)
    {T₀ Tp X : V T} (hT₀ : ∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) :
    X ∈ parabolicCharacteristicChamber hG hi D J T₀ Tp ↔
      X - π X ∈ characteristicLeviChamber hG hi D J T₀ Tp ∧
        π X ∈ characteristicSplitChamber hG hi D J Tp := by
  have hr (α : characterLattice T) (hα : α ∈ J.val) :
      eval T α (X - π X - (T₀ - π T₀)) = eval T α (X - T₀) := by
    simp only [map_sub, eval_split_eq_zero hG hi D J hν X hα,
      eval_split_eq_zero hG hi D J hν T₀ hα, sub_zero]
  have hw (α : characterLattice T) :
      w J.val α (X - π X - (Tp - π Tp)) = w J.val α (X - Tp) := by
    simp only [map_sub, weight_split_eq_zero hG hi D J hν, sub_zero]
  have hproj (α : characterLattice T) : eval T α (π (X - Tp)) = eval T α (π X - π Tp) := by
    rw [map_sub π]
  constructor
  · intro hX
    refine ⟨⟨sub_levelProjection_mem_span hG hi (ν := ν) D J.val X, ?_⟩,
      ⟨split_mem_corootSpan hG hi D J hX.1,
       levelProjection_mem_rootAnnihilator hG hi D hν J.property X, ?_⟩⟩
    · intro α hα
      rw [hr α hα, hw α]
      exact ⟨hX.2.1 α (J.property hα), hX.2.2.1 α hα⟩
    · intro α hα
      exact hproj α ▸ hX.2.2.2 α hα
  · rintro ⟨hlevi, hsplit⟩
    have hX : X ∈ D.realCorootSpan := by
      have hm := D.realCorootSpan.add_mem (levi_le_corootSpan D J hlevi.1) hsplit.1
      simpa only [sub_add_cancel] using hm
    have hweights (α : characterLattice T) (hα : α ∈ J.val) : w J.val α (X - Tp) ≤ 0 :=
      hw α ▸ (hlevi.2 α hα).2
    have hroots (α : characterLattice T) (hα : α ∈ Δ \ J.val) : 0 < eval T α (π (X - Tp)) :=
      (hproj α).symm ▸ hsplit.2.2 α hα
    refine ⟨hX, fun α hα => ?_, hweights, hroots⟩
    by_cases hj : α ∈ J.val
    · exact hr α hj ▸ (hlevi.2 α hj).1
    · calc
        0 ≤ eval T α (X - Tp - π (X - Tp)) + eval T α (π (X - Tp)) + eval T α (Tp - T₀) :=
          add_nonneg (add_nonneg (eval_levi_nonneg hG hi D J hν hweights ⟨hα, hj⟩)
            (hroots α ⟨hα, hj⟩).le) (hT₀ α hα)
        _ = eval T α (X - T₀) := by simp only [map_sub]; ring

/-- The Levi and split product of the parabolic characteristic chamber, Delorme (7.2). -/
theorem parabolicCharacteristicChamber_eq_add (hν : IsGenericCocharacter i ν)
    {T₀ Tp : V T} (hT₀ : ∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) :
    parabolicCharacteristicChamber hG hi D J T₀ Tp =
      characteristicLeviChamber hG hi D J T₀ Tp + characteristicSplitChamber hG hi D J Tp := by
  ext X
  rw [parabolicCharacteristicChamber_iff hG hi D J hν hT₀, Set.mem_add]
  constructor
  · rintro ⟨hlevi, hsplit⟩
    exact ⟨X - π X, hlevi, π X, hsplit, sub_add_cancel _ _⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [map_add, split_eq_zero hG hi D J hν hx.1, split_eq_self hG hi D J hν hy.2.1,
      zero_add, add_sub_cancel_right]
    exact ⟨hx, hy⟩

/-- The shell decomposition (7.23) in the actual relative coroot space. The lower
cutoff is no higher than `Tp` on each simple root. The increment is nonnegative
on the Levi's simple roots. -/
def TruncationShellProductStatement : Prop :=
  IsGenericCocharacter i ν → ∀ {T₀ Tp S : V T},
    (∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) →
    (∀ α ∈ J.val, 0 ≤ eval T α S) →
    characteristicShell hG hi D J T₀ Tp S =
      characteristicLeviChamber hG hi D J T₀ Tp + characteristicSplitShell hG hi D J Tp S

/-- Apply the chamber decomposition and translate the upper full weights into
the outside split weights and the Levi inequalities. -/
theorem truncationShellProduct : TruncationShellProductStatement hG hi D J := by
  intro hν T₀ Tp S hT₀ hS
  ext X
  change X ∈ characteristicChamber ν hG hi D T₀ (Tp + S) ∩
      parabolicCharacteristicChamber hG hi D J T₀ Tp ↔ _
  rw [Set.mem_inter_iff, parabolicCharacteristicChamber_iff hG hi D J hν hT₀, Set.mem_add]
  have hout (Y : V T) (α : characterLattice T) (hα : α ∈ Δ \ J.val) :
      w Δ α (π Y - π (Tp + S)) = w Δ α (Y - (Tp + S)) := by
    rw [← map_sub π, weight_split_eq hG hi D J hν _ hα]
  have hΔ : (simpleFinset ν hG hi : Set (characterLattice T)) = Δ :=
    Set.ext fun _ => mem_simpleFinset hG hi
  constructor
  · rintro ⟨hfull, hlevi, hsplit⟩
    refine ⟨X - π X, hlevi, π X, ⟨hsplit, fun α hα => ?_⟩, sub_add_cancel _ _⟩
    rw [hout X α hα]
    simpa only [hΔ] using (hfull.2 α ((mem_simpleFinset hG hi).mpr hα.1)).2
  · rintro ⟨x, hx, y, ⟨hy, hupper⟩, rfl⟩
    have hp : π (x + y) = y := by
      rw [map_add, split_eq_zero hG hi D J hν hx.1, split_eq_self hG hi D J hν hy.2.1, zero_add]
    have hspl : x + y - π (x + y) ∈ characteristicLeviChamber hG hi D J T₀ Tp ∧
        π (x + y) ∈ characteristicSplitChamber hG hi D J Tp := by
      rw [hp, add_sub_cancel_right]
      exact ⟨hx, hy⟩
    have hpar := (parabolicCharacteristicChamber_iff hG hi D J hν hT₀).mpr hspl
    have houtside (α : characterLattice T) (hα : α ∈ Δ \ J.val) :
        w Δ α (x + y - (Tp + S)) ≤ 0 := by
      rw [← hout (x + y) α hα, hp]
      exact hupper α hα
    refine ⟨⟨hpar.1, fun α hα => ⟨hpar.2.1 α ((mem_simpleFinset hG hi).mp hα), ?_⟩⟩, hspl⟩
    rw [hΔ]
    have hαD := (mem_simpleFinset hG hi).mp hα
    by_cases hαJ : α ∈ J.val
    · apply (fullWeight_le_leviWeight hG hi D J hν houtside hαJ).trans
      rw [show x + y - (Tp + S) = (x + y - Tp) - S by abel, map_sub]
      exact sub_nonpos.mpr ((hpar.2.2.1 α hαJ).trans (leviWeight_nonneg hG hi D J hν hS α hαJ))
    · exact houtside α ⟨hαD, hαJ⟩

end Langlands.Global.ArthurTruncation
