import Langlands.RingTheory.Smooth.SectionJets
import Mathlib.RingTheory.Ideal.Cotangent

/-! # The augmentation filtration on section jets -/

noncomputable section

universe u v

set_option autoImplicit false

namespace Algebra.SectionJet

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R)

/-- The order-`n` jet algebra of the specified section. -/
abbrev Quotient (n : ℕ) := A ⧸ RingHom.ker ε ^ (n + 1)

/-- The natural map from an order-`n + 1` jet to an order-`n` jet. -/
def truncate (n : ℕ) : Quotient ε (n + 1) →ₐ[R] Quotient ε n :=
  Ideal.quotientMapₐ _ (AlgHom.id R A)
    (fun _ ha => Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) ha)

@[simp]
theorem truncate_mk (n : ℕ) (a : A) :
    truncate ε n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem truncate_surjective (n : ℕ) : Function.Surjective (truncate ε n) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The degree-`n + 1` layer, as the actual kernel of jet truncation. -/
abbrev Layer (n : ℕ) := LinearMap.ker (truncate ε n).toLinearMap

theorem mk_mem_layer_iff (n : ℕ) (a : A) :
    Ideal.Quotient.mk (RingHom.ker ε ^ (n + 1 + 1)) a ∈ Layer ε n ↔
      a ∈ RingHom.ker ε ^ (n + 1) := by
  change Ideal.Quotient.mk (RingHom.ker ε ^ (n + 1)) a = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Evaluation of a section jet at its section. -/
def augmentation (n : ℕ) : Quotient ε n →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ ε (Ideal.pow_le_self (Nat.succ_ne_zero n))

@[simp]
theorem augmentation_mk (n : ℕ) (a : A) :
    augmentation ε n (Ideal.Quotient.mk _ a) = ε a := rfl

@[simp]
theorem augmentation_algebraMap (n : ℕ) (r : R) :
    augmentation ε n (algebraMap R (Quotient ε n) r) = r := by
  exact (augmentation ε n).commutes r

theorem augmentation_comp_truncate (n : ℕ) :
    (augmentation ε n).comp (truncate ε n) = augmentation ε (n + 1) := by
  apply Ideal.Quotient.algHom_ext R
  ext a
  rfl

@[simp]
theorem augmentation_truncate (n : ℕ) (x : Quotient ε (n + 1)) :
    augmentation ε n (truncate ε n x) = augmentation ε (n + 1) x :=
  AlgHom.congr_fun (augmentation_comp_truncate ε n) x

/-- The order-zero jet algebra is canonically the base ring. -/
def zeroEquiv : Quotient ε 0 ≃ₐ[R] R :=
  AlgEquiv.ofBijective (augmentation ε 0) ⟨by
    intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    simpa [RingHom.mem_ker, map_sub, sub_eq_zero] using h,
    fun r => ⟨algebraMap R _ r, augmentation_algebraMap ε 0 r⟩⟩

section Splitting

variable [FormallySmooth R A] [FiniteType R A]

instance finite_quotient (n : ℕ) : Module.Finite R (Quotient ε n) :=
  (FormallySmooth.finite_projective_quotient_ker_pow ε n).1

instance projective_quotient (n : ℕ) : Module.Projective R (Quotient ε n) :=
  (FormallySmooth.finite_projective_quotient_ker_pow ε n).2

theorem exists_linear_section (n : ℕ) :
    ∃ s : Quotient ε n →ₗ[R] Quotient ε (n + 1),
      (truncate ε n).toLinearMap.comp s = LinearMap.id :=
  (truncate ε n).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (truncate_surjective ε n))

/-- A choice of linear section of jet truncation. No multiplicativity is asserted. -/
def linearSection (n : ℕ) : Quotient ε n →ₗ[R] Quotient ε (n + 1) :=
  (exists_linear_section ε n).choose

@[simp]
theorem truncate_linearSection (n : ℕ) (x : Quotient ε n) :
    truncate ε n (linearSection ε n x) = x :=
  LinearMap.congr_fun (exists_linear_section ε n).choose_spec x

/-- The retraction to the successive kernel for the chosen linear section. -/
def layerProjection (n : ℕ) : Quotient ε (n + 1) →ₗ[R] Layer ε n :=
  (LinearMap.id - (linearSection ε n).comp (truncate ε n).toLinearMap).codRestrict _
    (fun x => by
      change truncate ε n (x - linearSection ε n (truncate ε n x)) = 0
      rw [map_sub, truncate_linearSection, sub_self])

@[simp]
theorem layerProjection_subtype (n : ℕ) (x : Layer ε n) :
    layerProjection ε n x.val = x := by
  apply Subtype.ext
  change x.val - linearSection ε n (truncate ε n x.val) = x.val
  rw [show truncate ε n x.val = 0 from x.property, map_zero, sub_zero]

instance finite_layer (n : ℕ) : Module.Finite R (Layer ε n) :=
  Module.Finite.of_surjective (layerProjection ε n)
    (fun x => ⟨x.val, layerProjection_subtype ε n x⟩)

instance projective_layer (n : ℕ) : Module.Projective R (Layer ε n) :=
  Module.Projective.of_split (Layer ε n).subtype (layerProjection ε n)
    (LinearMap.ext (layerProjection_subtype ε n))

/-- Successive jets split as modules into their lower jet and the next layer. -/
def splitEquiv (n : ℕ) :
    Quotient ε (n + 1) ≃ₗ[R] Quotient ε n × Layer ε n where
  toLinearMap := (truncate ε n).toLinearMap.prod (layerProjection ε n)
  invFun x := linearSection ε n x.1 + x.2.val
  left_inv x := by
    change linearSection ε n (truncate ε n x) +
      (x - linearSection ε n (truncate ε n x)) = x
    abel
  right_inv x := by
    apply Prod.ext
    · change truncate ε n (linearSection ε n x.1 + x.2.val) = x.1
      rw [map_add, truncate_linearSection, show truncate ε n x.2.val = 0 from x.2.property,
        add_zero]
    · apply Subtype.ext
      change linearSection ε n x.1 + x.2.val -
        linearSection ε n (truncate ε n (linearSection ε n x.1 + x.2.val)) = x.2.val
      rw [map_add, truncate_linearSection, show truncate ε n x.2.val = 0 from x.2.property,
        add_zero]
      abel

end Splitting

/-- The first cotangent layer is exactly the kernel of the first truncation. -/
def cotangentToLayer : (RingHom.ker ε).Cotangent →ₗ[R] Layer ε 0 :=
  ((RingHom.ker ε).cotangentToQuotientSquare.restrictScalars R).codRestrict _ (by
    intro x
    obtain ⟨a, rfl⟩ := (RingHom.ker ε).toCotangent_surjective x
    exact (mk_mem_layer_iff ε 0 a.val).mpr (by simp [a.property]))

@[simp]
theorem cotangentToLayer_toCotangent (a : RingHom.ker ε) :
    (cotangentToLayer ε ((RingHom.ker ε).toCotangent a)).val =
      Ideal.Quotient.mk (RingHom.ker ε ^ 2) a.val := rfl

/-- The canonical comparison between `I/I²` and the first actual jet kernel. -/
def cotangentEquivLayer : (RingHom.ker ε).Cotangent ≃ₗ[R] Layer ε 0 :=
  LinearEquiv.ofBijective (cotangentToLayer ε) ⟨by
    intro x y h
    exact (RingHom.ker ε).cotangentToQuotientSquare_injective (congrArg Subtype.val h), by
    intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.val
    have haI : a ∈ RingHom.ker ε := by
      have := (mk_mem_layer_iff ε 0 a).mp (ha.symm ▸ x.property)
      simpa using this
    exact ⟨(RingHom.ker ε).toCotangent ⟨a, haI⟩, Subtype.ext ha⟩⟩

/-- The first jet has a canonical linear projection to its first layer. -/
def firstLayerProjection : Quotient ε 1 →ₗ[R] Layer ε 0 :=
  (LinearMap.id -
    (Algebra.ofId R (Quotient ε 1)).toLinearMap.comp (augmentation ε 1).toLinearMap).codRestrict _
    (fun x => by
      change truncate ε 0 (x - algebraMap R (Quotient ε 1) (augmentation ε 1 x)) = 0
      apply (zeroEquiv ε).injective
      change augmentation ε 0
        (truncate ε 0 (x - algebraMap R (Quotient ε 1) (augmentation ε 1 x))) = _
      simp)

@[simp]
theorem augmentation_layer (x : Layer ε 0) :
    augmentation ε 1 x.val = 0 := by
  rw [← augmentation_truncate ε 0 x.val, show truncate ε 0 x.val = 0 from x.property,
    map_zero]

@[simp]
theorem firstLayerProjection_subtype (x : Layer ε 0) :
    firstLayerProjection ε x.val = x := by
  apply Subtype.ext
  change x.val - algebraMap R (Quotient ε 1) (augmentation ε 1 x.val) = x.val
  rw [augmentation_layer, map_zero, sub_zero]

/-- The first jet is canonically the direct sum of the base and `I/I²` as an
`R`-module. The scalar summand is the algebra structure map. -/
def firstSplitEquiv :
    Quotient ε 1 ≃ₗ[R] R × (RingHom.ker ε).Cotangent where
  toLinearMap := (augmentation ε 1).toLinearMap.prod
    ((cotangentEquivLayer ε).symm.toLinearMap.comp (firstLayerProjection ε))
  invFun x := algebraMap R (Quotient ε 1) x.1 + (cotangentEquivLayer ε x.2).val
  left_inv x := by
    change algebraMap R (Quotient ε 1) (augmentation ε 1 x) +
      (cotangentEquivLayer ε ((cotangentEquivLayer ε).symm
        (firstLayerProjection ε x))).val = x
    rw [LinearEquiv.apply_symm_apply]
    change algebraMap R (Quotient ε 1) (augmentation ε 1 x) +
      (x - algebraMap R (Quotient ε 1) (augmentation ε 1 x)) = x
    abel
  right_inv x := by
    apply Prod.ext
    · change augmentation ε 1
        (algebraMap R (Quotient ε 1) x.1 + (cotangentEquivLayer ε x.2).val) = x.1
      simp
    · change (cotangentEquivLayer ε).symm (firstLayerProjection ε
        (algebraMap R (Quotient ε 1) x.1 + (cotangentEquivLayer ε x.2).val)) = x.2
      apply (cotangentEquivLayer ε).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      change algebraMap R (Quotient ε 1) x.1 + (cotangentEquivLayer ε x.2).val -
        algebraMap R (Quotient ε 1) (augmentation ε 1
          (algebraMap R (Quotient ε 1) x.1 + (cotangentEquivLayer ε x.2).val)) =
        (cotangentEquivLayer ε x.2).val
      simp

section Splitting

variable [FormallySmooth R A] [FiniteType R A]

instance finite_cotangent : Module.Finite R (RingHom.ker ε).Cotangent :=
  Module.Finite.equiv (cotangentEquivLayer ε).symm

instance projective_cotangent : Module.Projective R (RingHom.ker ε).Cotangent :=
  Module.Projective.of_equiv (cotangentEquivLayer ε).symm

end Splitting

end Algebra.SectionJet
