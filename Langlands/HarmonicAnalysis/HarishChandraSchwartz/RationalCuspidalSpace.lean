import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvolution

/-! # The integrable cuspidal kernel on actual rational points

The defining condition ranges over every proper standard root subset, every Haar measure
on its actual radical, and every two-sided translate. Convergence is part of the kernel.
No constant-term estimate or cuspidal projector is assumed.
-/

noncomputable section

universe u uG

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section Functions

variable {Γ : Type uG} [Group Γ] [MeasurableSpace Γ] {U M : Subgroup Γ}

/-- Absolute convergence and vanishing along every two-sided translate of `U`. -/
def IsIntegrableUnipotentCuspidal (muU : Measure U) (f : Γ → ℂ) : Prop :=
  ∀ x y : Γ, Integrable (fun v : U => f (x * v * y)) muU ∧
    ∫ v : U, f (x * v * y) ∂muU = 0

/-- The convergence condition makes the integral kernel an honest complex submodule. -/
def integrableUnipotentCuspidalSubmodule (muU : Measure U) : Submodule ℂ (Γ → ℂ) where
  carrier := {f | IsIntegrableUnipotentCuspidal muU f}
  zero_mem' := by
    intro x y
    exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
  add_mem' := by
    intro f g hf hg x y
    refine ⟨(hf x y).1.add (hg x y).1, ?_⟩
    change ∫ v : U, (f (x * v * y) + g (x * v * y)) ∂muU = 0
    rw [integral_add (hf x y).1 (hg x y).1, (hf x y).2, (hg x y).2, add_zero]
  smul_mem' := by
    intro c f hf x y
    refine ⟨(hf x y).1.const_mul c, ?_⟩
    change ∫ v : U, c * f (x * v * y) ∂muU = 0
    rw [integral_const_mul, (hf x y).2, mul_zero]

/-- The normalized induced constant term has precisely the same vanishing condition;
at the identity of the Levi the normalizing factor is one. -/
theorem isIntegrableUnipotentCuspidal_iff_constantTermInd
    (muU : Measure U) (δ : M →* ℝ≥0ˣ) (f : Γ → ℂ) :
    IsIntegrableUnipotentCuspidal muU f ↔
      (∀ x y : Γ, Integrable (fun v : U => f (x * v * y)) muU) ∧
      ∀ g : Γ × Γ, constantTermInd muU δ f g = 0 := by
  constructor
  · intro hf
    refine ⟨fun x y => (hf x y).1, ?_⟩
    intro g
    funext m
    change constantTermInd muU δ f g m = 0
    simp only [constantTermInd, constantTerm, translate_apply]
    have hz := (hf (g.2⁻¹ * m) g.1).2
    simp only [mul_assoc] at hz ⊢
    rw [hz, mul_zero]
  · rintro ⟨hi, hz⟩ x y
    refine ⟨hi x y, ?_⟩
    have h := congrFun (hz (y, x⁻¹)) 1
    simpa [constantTermInd, constantTerm, translate_apply, mul_assoc] using h

/-- Left invariance, used in the right-translation representation of VIII.4.2. -/
def IsLeftInvariant (H : Subgroup Γ) (f : Γ → ℂ) : Prop :=
  ∀ h ∈ H, ∀ g, f (h * g) = f g

def leftInvariantFunctionSubmodule (H : Subgroup Γ) : Submodule ℂ (Γ → ℂ) where
  carrier := {f | IsLeftInvariant H f}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {f g} hf hg h hh x => by
    simp only [Pi.add_apply, hf h hh x, hg h hh x]
  smul_mem' := fun c f hf h hh g => by
    simp only [Pi.smul_apply, hf h hh g]

def biInvariantFunctionSubmodule (H : Subgroup Γ) : Submodule ℂ (Γ → ℂ) where
  carrier := {f | IsBiInvariant H f}
  zero_mem' := isBiInvariant_zero H
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

omit [MeasurableSpace Γ] in
theorem IsBiInvariant.isLeftInvariant {H : Subgroup Γ} {f : Γ → ℂ}
    (hf : IsBiInvariant H f) : IsLeftInvariant H f := by
  intro h hh g
  simpa using hf h hh 1 H.one_mem g

end Functions

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The intrinsic kernel, in the standard-parabolic/all-translates presentation of VIII.2.1.
Properness is the strict root-subset condition, so an empty simple-root system imposes
no conditions. Quantifying over measures makes no normalization choice. -/
def rationalCuspidalSubmodule : Submodule ℂ (RationalSchwartzSpace hKc hPK ρ) where
  carrier := {f | ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
    RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν →
    ∀ muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)),
      muU.IsHaarMeasure → IsIntegrableUnipotentCuspidal muU (f : rationalPoints G → ℂ)}
  zero_mem' := fun _ _ muU _ => (integrableUnipotentCuspidalSubmodule muU).zero_mem
  add_mem' := fun hf hg I hI muU hmuU =>
    (integrableUnipotentCuspidalSubmodule muU).add_mem (hf I hI muU hmuU) (hg I hI muU hmuU)
  smul_mem' := fun c _ hf I hI muU hmuU =>
    (integrableUnipotentCuspidalSubmodule muU).smul_mem c (hf I hI muU hmuU)

@[simp] theorem mem_rationalCuspidalSubmodule (f : RationalSchwartzSpace hKc hPK ρ) :
    f ∈ rationalCuspidalSubmodule hKc hPK ρ ↔
      ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
        RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν →
        ∀ muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)),
          muU.IsHaarMeasure → IsIntegrableUnipotentCuspidal muU (f : rationalPoints G → ℂ) :=
  Iff.rfl

/-- In relative rank zero the kernel is the entire actual Schwartz space. -/
theorem rationalCuspidalSubmodule_eq_top_of_simpleRoots_empty
    (h0 : simpleRelativeRoots i ν = ∅) :
    rationalCuspidalSubmodule hKc hPK ρ = ⊤ := by
  apply top_unique
  intro f _ I hI
  exact (hI (Set.eq_empty_iff_forall_notMem.mpr (fun α hα => by
    have := RationalPointFamily.rootSet_subset i ν I hα
    simp [h0] at this) |>.trans h0.symm)).elim

/-- The prescribed bi-invariant part `°C_H`. -/
def rationalCuspidalLevel (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSchwartzSpace hKc hPK ρ) :=
  rationalCuspidalSubmodule hKc hPK ρ ⊓
    (biInvariantFunctionSubmodule H).comap Space.toFunLinear

/-- The prescribed left-invariant part `°C(H \ G)`. -/
def rationalCuspidalLeftLevel (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSchwartzSpace hKc hPK ρ) :=
  rationalCuspidalSubmodule hKc hPK ρ ⊓
    (leftInvariantFunctionSubmodule H).comap Space.toFunLinear

@[simp] theorem mem_rationalCuspidalLevel (H : Subgroup (rationalPoints G))
    (f : RationalSchwartzSpace hKc hPK ρ) :
    f ∈ rationalCuspidalLevel hKc hPK ρ H ↔
      f ∈ rationalCuspidalSubmodule hKc hPK ρ ∧ IsBiInvariant H (f : rationalPoints G → ℂ) :=
  Iff.rfl

@[simp] theorem mem_rationalCuspidalLeftLevel (H : Subgroup (rationalPoints G))
    (f : RationalSchwartzSpace hKc hPK ρ) :
    f ∈ rationalCuspidalLeftLevel hKc hPK ρ H ↔
      f ∈ rationalCuspidalSubmodule hKc hPK ρ ∧ IsLeftInvariant H (f : rationalPoints G → ℂ) :=
  Iff.rfl

theorem rationalCuspidalLevel_le (H : Subgroup (rationalPoints G)) :
    rationalCuspidalLevel hKc hPK ρ H ≤ rationalCuspidalSubmodule hKc hPK ρ :=
  inf_le_left

theorem rationalCuspidalLeftLevel_le (H : Subgroup (rationalPoints G)) :
    rationalCuspidalLeftLevel hKc hPK ρ H ≤ rationalCuspidalSubmodule hKc hPK ρ :=
  inf_le_left

theorem rationalCuspidalLevel_le_leftLevel (H : Subgroup (rationalPoints G)) :
    rationalCuspidalLevel hKc hPK ρ H ≤ rationalCuspidalLeftLevel hKc hPK ρ H :=
  fun _ hf => ⟨hf.1, hf.2.isLeftInvariant⟩

theorem rationalCuspidalLevel_antitone {H H' : Subgroup (rationalPoints G)} (h : H' ≤ H) :
    rationalCuspidalLevel hKc hPK ρ H ≤ rationalCuspidalLevel hKc hPK ρ H' :=
  fun _ hf => ⟨hf.1, hf.2.mono h⟩

theorem rationalCuspidalLeftLevel_antitone {H H' : Subgroup (rationalPoints G)} (h : H' ≤ H) :
    rationalCuspidalLeftLevel hKc hPK ρ H ≤ rationalCuspidalLeftLevel hKc hPK ρ H' :=
  fun _ hf => ⟨hf.1, fun a ha g => hf.2 a (h ha) g⟩

/-- The all-standard normalized constant-term formulation, with convergence retained. -/
theorem mem_rationalCuspidalSubmodule_iff_constantTermInd
    (f : RationalSchwartzSpace hKc hPK ρ) :
    f ∈ rationalCuspidalSubmodule hKc hPK ρ ↔
      ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
        RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν →
        ∀ muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)),
          muU.IsHaarMeasure →
          (∀ x y : rationalPoints G, Integrable (fun v :
              standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I) =>
            f (x * (v : rationalPoints G) * y)) muU) ∧
          ∀ g : rationalPoints G × rationalPoints G,
            constantTermInd muU
              (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
              (f : rationalPoints G → ℂ) g = 0 := by
  simp only [mem_rationalCuspidalSubmodule]
  exact forall_congr' fun I => imp_congr_right fun _ =>
    forall_congr' fun muU => imp_congr_right fun _ =>
      isIntegrableUnipotentCuspidal_iff_constantTermInd muU _ _

section Adapter

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)))
  [muU.IsHaarMeasure]
  (hE : ConstantTermEstimate muU
    (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))

/-- Specialization to the published Schwartz-valued standard constant term.
The estimate is exposed only in this auxiliary adapter. -/
theorem rationalConstantTermIndVanishes_of_mem_rationalCuspidalSubmodule
    {f : RationalSchwartzSpace hKc hPK ρ}
    (hf : f ∈ rationalCuspidalSubmodule hKc hPK ρ)
    (hI : RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν) :
    RationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM muU hE f := by
  apply (isUnipotentCuspidal_iff_rationalConstantTermIndVanishes
    hG hi hν I hKc hPK ρ hM muU hE f).mp
  exact fun x y => (hf I hI muU inferInstance x y).2

end Adapter

end Langlands.HarishChandraSchwartz
