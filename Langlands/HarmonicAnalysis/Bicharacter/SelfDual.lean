import Langlands.HarmonicAnalysis.AdditiveCharacterExists
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Self-dual bicharacters

A *self-dual bicharacter* on a commutative topological group `X` is a symmetric, locally constant
bicharacter `e : X → X → ℂ` with values of modulus one such that `x ↦ e x ·` identifies `X` with
its Pontryagin dual topologically: the annihilator of a large compact set is a small
neighbourhood of `0`, and the annihilator of a neighbourhood of `0` is relatively compact
(`IsSelfDualBicharacter`). The groups considered are totally disconnected: they have arbitrarily
large and arbitrarily small compact open subgroups (`CompactOpenExhaustion`).

The main examples: `(x, y) ↦ ψ (β x y)` for a non-trivial continuous unitary character `ψ` of a
nonarchimedean local field `F` and a non-degenerate symmetric bilinear form `β` on a
finite-dimensional `F`-vector space (`isSelfDualBicharacter_of_symm`). A finite-dimensional
`F`-vector space with its module topology has the topological properties the Fourier analysis of
`Langlands/HarmonicAnalysis/Bicharacter/Fourier.lean` needs
(`compactOpenExhaustion_of_finiteDimensional`, `t2Space_of_finiteDimensional`,
`locallyCompactSpace_of_finiteDimensional`, `secondCountableTopology_of_finiteDimensional`).

Over `F` itself: the closed balls `{x | v x ≤ v s}` are compact open subgroups
(`isOpen_setOf_valuation_le`, `exists_setOf_valuation_le_subset`), and the integral of a
non-trivial character over a large ball vanishes (`exists_setIntegral_setOf_valuation_le_eq_zero`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped Topology Pointwise

namespace Langlands.HarmonicAnalysis

/-! ### Compact open subgroups -/

/-- A topological additive group with arbitrarily large and arbitrarily small compact open
subgroups: every compact set lies in a compact open subgroup, and every neighbourhood of `0`
contains one. -/
class CompactOpenExhaustion (X : Type*) [AddGroup X] [TopologicalSpace X] : Prop where
  exists_superset : ∀ K : Set X, IsCompact K →
    ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L
  exists_subset : ∀ U ∈ 𝓝 (0 : X),
    ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ (L : Set X) ⊆ U

/-- Transport of the topological properties along an additive homeomorphism. -/
theorem CompactOpenExhaustion.of_addEquiv {X Y : Type*} [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] (f : X ≃ₜ+ Y) [CompactOpenExhaustion Y] :
    CompactOpenExhaustion X := by
  refine ⟨fun K hK => ?_, fun U hU => ?_⟩
  · obtain ⟨L, hLc, hLo, hKL⟩ :=
      CompactOpenExhaustion.exists_superset (f '' K) (hK.image f.continuous)
    refine ⟨L.comap f.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_⟩
    · exact f.toHomeomorph.isCompact_preimage.mpr hLc
    · exact hLo.preimage f.continuous
    · intro x hx; exact hKL ⟨x, hx, rfl⟩
  · have hU' : f.symm ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply f.symm.continuous.continuousAt.preimage_mem_nhds; simpa using hU
    obtain ⟨L, hLc, hLo, hLU⟩ := CompactOpenExhaustion.exists_subset _ hU'
    refine ⟨L.comap f.toAddEquiv.toAddMonoidHom, ?_, hLo.preimage f.continuous, ?_⟩
    · exact f.toHomeomorph.isCompact_preimage.mpr hLc
    · intro x hx
      have h := hLU hx
      change f.symm (f x) ∈ U at h
      rwa [f.symm_apply_apply] at h

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The closed ball `{x | v x ≤ v s}`, `s ≠ 0`, is open. -/
theorem isOpen_setOf_valuation_le (s : Fˣ) :
    IsOpen {x : F | valuation F x ≤ valuation F (s : F)} := by
  have h : {x : F | valuation F x ≤ valuation F (s : F)} = s • (𝒪[F] : Set F) := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
      smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_mul_le_iff₀ (by simp [zero_lt_iff]), mul_one]
  rw [h]
  exact (GeneralLocalField.isOpen_integer F).smul s

/-- Every neighbourhood of `0` contains a closed ball `{x | v x ≤ v s}`. -/
theorem exists_setOf_valuation_le_subset {U : Set F} (hU : U ∈ 𝓝 (0 : F)) :
    ∃ s : Fˣ, {x : F | valuation F x ≤ valuation F (s : F)} ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero F)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 (r * y) (mul_ne_zero hr0 hy0), fun z hz => hγ ?_⟩
  have hz' : valuation F z ≤ valuation F (r * y) := hz
  refine lt_of_le_of_lt hz' ?_
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

namespace SelfDual.Internal

/-- The box `∏ {x | v x ≤ v s}` in `n → F`. -/
def box (n : Type*) (s : Fˣ) : Set (n → F) :=
  Set.univ.pi fun _ => {x : F | valuation F x ≤ valuation F (s : F)}

theorem isOpen_box {n : Type*} [Finite n] (s : Fˣ) : IsOpen (box n s : Set (n → F)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_setOf_valuation_le s

theorem isCompact_box {n : Type*} (s : Fˣ) : IsCompact (box n s : Set (n → F)) :=
  isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F _

theorem exists_box_subset {n : Type*} [Finite n] {U : Set (n → F)} (hU : U ∈ 𝓝 (0 : n → F)) :
    ∃ s : Fˣ, box n s ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  have h1 : (⋂ i, t i) ∈ 𝓝 (0 : F) := Filter.iInter_mem.mpr ht
  obtain ⟨s, hs⟩ := exists_setOf_valuation_le_subset h1
  exact ⟨s, fun x hx => hsub fun i _ => Set.mem_iInter.mp (hs (hx i trivial)) i⟩

/-- The box as an additive subgroup. -/
def boxSub (n : Type*) (s : Fˣ) : AddSubgroup (n → F) where
  carrier := box n s
  zero_mem' := fun i _ => by simp
  add_mem' := by
    intro a b ha hb i _
    have h1 : valuation F (a i) ≤ valuation F (s : F) := ha i trivial
    have h2 : valuation F (b i) ≤ valuation F (s : F) := hb i trivial
    show valuation F ((a + b) i) ≤ valuation F (s : F)
    rw [Pi.add_apply]
    exact (valuation F).map_add_le h1 h2
  neg_mem' := fun ha i _ => by simpa using ha i trivial

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_box_mono {s t : Fˣ} (h : valuation F (s : F) ≤ valuation F (t : F)) {y : F}
    (hy : valuation F y ≤ valuation F (s : F)) : valuation F y ≤ valuation F (t : F) :=
  le_trans hy h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_boxSub (n : Type*) (s : Fˣ) : (boxSub n s : Set (n → F)) = box n s := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_some_ball (y : F) : ∃ s : Fˣ, valuation F y ≤ valuation F (s : F) := by
  by_cases hy : y = 0
  · exact ⟨1, by simp [hy]⟩
  · exact ⟨Units.mk0 y hy, by simp⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_some_box (n : Type*) [Finite n] (x : n → F) : ∃ s : Fˣ, x ∈ box n s := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i⟩
  · choose u hu using fun i => mem_some_ball (x i)
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (u i : F)
    exact ⟨u j, fun i _ => mem_box_mono (hj i) (hu i)⟩

end SelfDual.Internal

open SelfDual.Internal

instance compactOpenExhaustion_pi (n : Type*) [Finite n] : CompactOpenExhaustion (n → F) := by
  refine ⟨fun K hK => ?_, fun U hU => ?_⟩
  · obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : Fˣ => box n s) (fun s => isOpen_box s)
      (fun x _ => Set.mem_iUnion.mpr (mem_some_box n x)) (by
        intro s t
        rcases le_total (valuation F (s : F)) (valuation F (t : F)) with h | h
        · exact ⟨t, fun x hx i _ => mem_box_mono h (hx i trivial), le_rfl⟩
        · exact ⟨s, le_rfl, fun x hx i _ => mem_box_mono h (hx i trivial)⟩)
    exact ⟨boxSub n s, by rw [coe_boxSub]; exact isCompact_box s,
      by rw [coe_boxSub]; exact isOpen_box s, by rw [coe_boxSub]; exact hs⟩
  · obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub n s, by rw [coe_boxSub]; exact isCompact_box s,
      by rw [coe_boxSub]; exact isOpen_box s, by rw [coe_boxSub]; exact hs⟩

/-- The additive homeomorphism of a finite-dimensional space with its module topology with
`Fⁿ`, along a basis. -/
def finiteDimensionalCoordinates (F : Type*) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] : V ≃ₜ+ (Fin (Module.finrank F V) → F) :=
  haveI := IsModuleTopology.toContinuousAdd F V
  let e := (Module.finBasis F V).equivFun
  { e.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

section FiniteDimensional

variable (F) (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [TopologicalSpace V] [IsModuleTopology F V]

include F

theorem compactOpenExhaustion_of_finiteDimensional : CompactOpenExhaustion V :=
  have := IsModuleTopology.isTopologicalAddGroup F V
  CompactOpenExhaustion.of_addEquiv (finiteDimensionalCoordinates F V)

theorem t2Space_of_finiteDimensional : T2Space V :=
  (finiteDimensionalCoordinates F V).toHomeomorph.isEmbedding.t2Space

theorem locallyCompactSpace_of_finiteDimensional : LocallyCompactSpace V :=
  (finiteDimensionalCoordinates F V).toHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem secondCountableTopology_of_finiteDimensional : SecondCountableTopology V :=
  have := GeneralLocalField.secondCountableTopology F
  (finiteDimensionalCoordinates F V).toHomeomorph.isInducing.secondCountableTopology

end FiniteDimensional

/-- A finite-dimensional vector space over the nonarchimedean local field `F` with its module
topology. `F` (with its structure and the module structure) is an out-parameter, so that the
consequences of `compactOpenExhaustion_of_finiteDimensional`, `t2Space_of_finiteDimensional`,
`locallyCompactSpace_of_finiteDimensional` and `secondCountableTopology_of_finiteDimensional` are
instances on the spaces that carry an instance of this class (the coordinate spaces `n → F` and
the matrix spaces `Matrix m n F` below). -/
class IsFiniteDimensionalOverLocalField (F : outParam Type*) [outParam (Field F)]
    [outParam (ValuativeRel F)] [outParam (TopologicalSpace F)]
    [outParam (IsNonarchimedeanLocalField F)] (V : Type*) [AddCommGroup V]
    [outParam (Module F V)] [TopologicalSpace V] : Prop where
  finiteDimensional : FiniteDimensional F V
  isModuleTopology : IsModuleTopology F V

section IsFiniteDimensionalOverLocalField

variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]

instance (priority := 100) IsFiniteDimensionalOverLocalField.compactOpenExhaustion
    [h : IsFiniteDimensionalOverLocalField F V] : CompactOpenExhaustion V :=
  haveI := h.finiteDimensional; haveI := h.isModuleTopology
  compactOpenExhaustion_of_finiteDimensional F V

instance (priority := 100) IsFiniteDimensionalOverLocalField.t2Space
    [h : IsFiniteDimensionalOverLocalField F V] : T2Space V :=
  haveI := h.finiteDimensional; haveI := h.isModuleTopology
  t2Space_of_finiteDimensional F V

instance (priority := 100) IsFiniteDimensionalOverLocalField.locallyCompactSpace
    [h : IsFiniteDimensionalOverLocalField F V] : LocallyCompactSpace V :=
  haveI := h.finiteDimensional; haveI := h.isModuleTopology
  locallyCompactSpace_of_finiteDimensional F V

instance (priority := 100) IsFiniteDimensionalOverLocalField.secondCountableTopology
    [h : IsFiniteDimensionalOverLocalField F V] : SecondCountableTopology V :=
  haveI := h.finiteDimensional; haveI := h.isModuleTopology
  secondCountableTopology_of_finiteDimensional F V

instance IsFiniteDimensionalOverLocalField.pi (n : Type*) [Finite n] :
    IsFiniteDimensionalOverLocalField F (n → F) where
  finiteDimensional := inferInstance
  isModuleTopology := inferInstance

instance IsFiniteDimensionalOverLocalField.matrix (m n : Type*) [Finite m] [Finite n] :
    IsFiniteDimensionalOverLocalField F (Matrix m n F) where
  finiteDimensional := inferInstanceAs (FiniteDimensional F (m → n → F))
  isModuleTopology := inferInstanceAs (IsModuleTopology F (m → n → F))

end IsFiniteDimensionalOverLocalField

/-- The integral of a non-trivial character of `F` over a large closed ball vanishes. -/
theorem exists_setIntegral_setOf_valuation_le_eq_zero [MeasurableSpace F] [BorelSpace F]
    (lam : Measure F) [lam.IsAddLeftInvariant] {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∃ s₀ : Fˣ, ∀ s : Fˣ, valuation F (s₀ : F) ≤ valuation F (s : F) →
      ∫ x in {x : F | valuation F x ≤ valuation F (s : F)}, ψ x ∂lam = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  set B := {x : F | valuation F x ≤ valuation F (s : F)}
  have hs' : t ∈ B := hs
  have hm : MeasurableSet B := (isOpen_setOf_valuation_le s).measurableSet
  have hadd : ∀ x y : F, x ∈ B → y ∈ B → x + y ∈ B := fun x y hx hy => by
    change valuation F (x + y) ≤ valuation F (s : F)
    exact (valuation F).map_add_le hx hy
  have hneg : -t ∈ B := by simpa [B] using hs'
  have hiff : ∀ x : F, t + x ∈ B ↔ x ∈ B := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam) (B.indicator (fun x => ψ x)) t
  have h2 : (fun x => B.indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * B.indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)),
        mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, B.indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)

end LocalField

/-! ### Self-dual bicharacters -/

/-- A self-dual bicharacter on a commutative topological group `X`: a symmetric bicharacter
with values of modulus one, locally constant on `X × X`, such that the annihilator of a large
compact set is contained in a given neighbourhood of `0` (`small`), and the annihilator of a
neighbourhood of `0` is contained in a compact set (`big`). -/
structure IsSelfDualBicharacter {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    (e : X → X → ℂ) : Prop where
  map_add_left : ∀ x x' y, e (x + x') y = e x y * e x' y
  symm : ∀ x y, e x y = e y x
  norm_eq_one : ∀ x y, ‖e x y‖ = 1
  isLocallyConstant : IsLocallyConstant fun p : X × X => e p.1 p.2
  small : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e x y = 1) → y ∈ U
  big : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ U, e x y = 1) → y ∈ K

namespace IsSelfDualBicharacter

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}

theorem ne_zero (he : IsSelfDualBicharacter e) (x y : X) : e x y ≠ 0 := by
  intro h
  have h1 := he.norm_eq_one x y
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem map_add_right (he : IsSelfDualBicharacter e) (x y y' : X) :
    e x (y + y') = e x y * e x y' := by
  rw [he.symm x (y + y'), he.map_add_left y y' x, he.symm y x, he.symm y' x]

theorem map_zero_right (he : IsSelfDualBicharacter e) (x : X) : e x 0 = 1 := by
  have h := he.map_add_right x 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (he.ne_zero x 0) (by rw [mul_one]; exact h.symm)

theorem map_zero_left (he : IsSelfDualBicharacter e) (y : X) : e 0 y = 1 := by
  rw [he.symm]; exact he.map_zero_right y

theorem conj_apply (he : IsSelfDualBicharacter e) (x y : X) :
    starRingEnd ℂ (e x y) = e (-x) y := by
  have h1 : e (-x) y * e x y = 1 := by rw [← he.map_add_left, neg_add_cancel, he.map_zero_left]
  have h2 : starRingEnd ℂ (e x y) * e x y = 1 := by
    rw [Complex.conj_mul', he.norm_eq_one]; simp
  exact mul_right_cancel₀ (he.ne_zero x y) (h2.trans h1.symm)

theorem continuous (he : IsSelfDualBicharacter e) : Continuous fun p : X × X => e p.1 p.2 :=
  he.isLocallyConstant.continuous

/-- The annihilator `{z | ∀ y ∈ L, e y z = 1}` of a set, as a subgroup. -/
def annihilator (he : IsSelfDualBicharacter e) (L : Set X) : AddSubgroup X where
  carrier := {z | ∀ y ∈ L, e y z = 1}
  zero_mem' := fun y _ => he.map_zero_right y
  add_mem' := fun {a b} ha hb y hy => by rw [he.map_add_right, ha y hy, hb y hy, one_mul]
  neg_mem' := fun {a} ha y hy => by
    have h := he.map_add_right y a (-a)
    rw [add_neg_cancel, he.map_zero_right, ha y hy, one_mul] at h
    exact h.symm

theorem mem_annihilator (he : IsSelfDualBicharacter e) {L : Set X} {z : X} :
    z ∈ he.annihilator L ↔ ∀ y ∈ L, e y z = 1 := Iff.rfl

/-- The annihilator of a compact set is open. -/
theorem isOpen_annihilator [IsTopologicalAddGroup X] (he : IsSelfDualBicharacter e) {L : Set X}
    (hL : IsCompact L) : IsOpen (he.annihilator L : Set X) := by
  have hS : IsOpen {p : X × X | e p.1 p.2 = 1} := he.isLocallyConstant.isOpen_fiber 1
  have hsub : L ×ˢ ({0} : Set X) ⊆ {p : X × X | e p.1 p.2 = 1} := by
    rintro ⟨y, z⟩ ⟨_, hz⟩
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact he.map_zero_right y
  obtain ⟨u, v, -, hv, hLu, h0v, huv⟩ := generalized_tube_lemma hL isCompact_singleton hS hsub
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  refine Filter.mem_of_superset (hv.mem_nhds (h0v (Set.mem_singleton 0))) ?_
  intro z hz y hy
  exact huv (show (y, z) ∈ u ×ˢ v from ⟨hLu hy, hz⟩)

end IsSelfDualBicharacter

section Pairing

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
open SelfDual.Internal in
theorem SelfDual.Internal.mem_box_of_forall_dotProduct {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : AddChar F ℂ) {t₀ : Fˣ} (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F}
    (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) : v ∈ box d (t₀ * s⁻¹) := by
  intro i _
  by_contra h
  simp only [Set.mem_ofPred_eq, not_le] at h
  have hw : v i ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at h
    exact absurd h (not_lt_of_ge zero_le)
  apply ht
  have hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, Set.mem_ofPred_eq]
      have e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j := by
        push_cast
        field_simp
      have hpos : 0 < valuation F (v j) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hw
      rw [e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]
      exact mul_le_mul' h.le le_rfl
    · simp [Pi.single_eq_of_ne hj]
  have h2 := hv _ hu
  rwa [single_dotProduct, div_mul_cancel₀ _ hw] at h2

open SelfDual.Internal in
/-- **`ψ ∘ β` is a self-dual bicharacter** for a non-trivial continuous unitary character `ψ` of
`F` and a non-degenerate symmetric bilinear form `β` on a finite-dimensional `F`-vector space
with its module topology. -/
theorem isSelfDualBicharacter_of_symm {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F)
    (hs : ∀ x y, β x y = β y x) (hnd : ∀ y, (∀ x, β x y = 0) → y = 0) :
    IsSelfDualBicharacter fun x y => ψ (β x y) := by
  have := IsModuleTopology.toContinuousAdd F V
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ)
  let T : Fˣ := Units.mk0 t ht0
  have hT : ψ (T : F) ≠ 1 := ht
  let b := Module.finBasis F V
  let e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F) := LinearMap.pi fun i => β (b i)
  have hf₂ : Function.Injective f₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd y
    intro x
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]
  have hbij : Function.Bijective f₂ :=
    ⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩
  let e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := LinearEquiv.ofBijective f₂ hbij
  have key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y := by
    intro u y
    simp [e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]
  have cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm :=
    fun g => ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap,
      IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩
  have ann : ∀ (s : Fˣ) y,
      (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) →
      e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹) := by
    intro s y h
    exact mem_box_of_forall_dotProduct ψ hT s fun u hu => by rw [← key]; exact h u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul]
  · intro x y
    rw [hs]
  · intro x y
    exact hn _
  · exact (isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · intro U hU
    have hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨r, hr⟩ := exists_box_subset hU'
    refine ⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹),
      (isCompact_box _).image (cont e₁).2, fun y hy => ?_⟩
    have h2 := ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩
    rw [show T * (T * r⁻¹)⁻¹ = r by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]] at h2
    simpa using hr h2
  · intro U hU
    have hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨s, hs'⟩ := exists_box_subset hU'
    exact ⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2,
      fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩

end Pairing

end Langlands.HarmonicAnalysis
