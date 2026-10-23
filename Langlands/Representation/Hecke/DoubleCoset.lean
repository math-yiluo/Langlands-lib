import Langlands.Representation.Hecke.CornerAction
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Actual compact-open double-coset Hecke operators -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure
open HarmonicAnalysis (SchwartzBruhat)
open scoped Pointwise

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

namespace TestFunction

/-- The actual double coset `K g K`. -/
def doubleCosetSet (g : G) : Set G := DoubleCoset.doubleCoset g K K

omit [IsTopologicalGroup G] in
@[simp] theorem mem_doubleCosetSet (g x : G) :
    x ∈ doubleCosetSet K g ↔ ∃ a ∈ K, ∃ b ∈ K, x = a * g * b :=
  DoubleCoset.mem_doubleCoset

theorem isOpen_doubleCosetSet (g : G) : IsOpen (doubleCosetSet K g) :=
  (K.isOpen.mul_right).mul_right

include hK in
theorem isCompact_doubleCosetSet (g : G) : IsCompact (doubleCosetSet K g) :=
  (hK.mul isCompact_singleton).mul hK

omit [IsTopologicalGroup G] in
theorem mul_mem_doubleCosetSet_left (g : G) (k : K) (x : G) :
    (k : G) * x ∈ doubleCosetSet K g ↔ x ∈ doubleCosetSet K g := by
  simp only [mem_doubleCosetSet]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨(k : G)⁻¹ * a, K.mul_mem (K.inv_mem k.property) ha, b, hb, ?_⟩
    calc
      x = (k : G)⁻¹ * ((k : G) * x) := (inv_mul_cancel_left _ _).symm
      _ = _ := by rw [h]; simp only [mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(k : G) * a, K.mul_mem k.property ha, b, hb, by simp only [mul_assoc]⟩

omit [IsTopologicalGroup G] in
theorem mul_mem_doubleCosetSet_right (g : G) (k : K) (x : G) :
    x * (k : G) ∈ doubleCosetSet K g ↔ x ∈ doubleCosetSet K g := by
  simp only [mem_doubleCosetSet]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b * (k : G)⁻¹, K.mul_mem hb (K.inv_mem k.property), ?_⟩
    calc
      x = (x * (k : G)) * (k : G)⁻¹ := (mul_inv_cancel_right _ _).symm
      _ = _ := by rw [h]; simp only [mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * (k : G), K.mul_mem hb k.property, by simp only [mul_assoc]⟩

omit [IsTopologicalGroup G] in
@[simp] theorem doubleCosetSet_one : doubleCosetSet K (1 : G) = K := by
  ext x
  simp only [mem_doubleCosetSet, mul_one, SetLike.mem_coe]
  exact ⟨fun ⟨a, ha, b, hb, h⟩ => h ▸ K.mul_mem ha hb,
    fun hx => ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩⟩

omit [IsTopologicalGroup G] in
theorem doubleCosetSet_eq_of_mem {g a : G} (ha : a ∈ doubleCosetSet K g) :
    doubleCosetSet K a = doubleCosetSet K g :=
  DoubleCoset.doubleCoset_eq_of_mem ha

variable [T2Space G]

include hK in
theorem isClopen_doubleCosetSet (g : G) : IsClopen (doubleCosetSet K g) :=
  ⟨(isCompact_doubleCosetSet K hK g).isClosed, isOpen_doubleCosetSet K g⟩

/-- The unnormalized characteristic function of the actual compact-open double coset. -/
def doubleCosetIndicator (g : G) : SchwartzBruhat G :=
  characteristic (isClopen_doubleCosetSet K hK g) (isCompact_doubleCosetSet K hK g)

@[simp] theorem doubleCosetIndicator_apply (g x : G) :
    doubleCosetIndicator K hK g x = (doubleCosetSet K g).indicator (fun _ => (1 : ℂ)) x := rfl

theorem support_doubleCosetIndicator (g : G) :
    Function.support (doubleCosetIndicator K hK g : G → ℂ) = doubleCosetSet K g :=
  support_characteristic _ _

theorem doubleCosetIndicator_mem (g : G) :
    doubleCosetIndicator K hK g ∈ biInvariant K.toSubgroup K.toSubgroup := by
  classical
  constructor
  · intro k x
    simp only [doubleCosetIndicator_apply, Set.indicator_apply]
    congr 1
    exact propext (mul_mem_doubleCosetSet_left K g k x)
  · intro k x
    simp only [doubleCosetIndicator_apply, Set.indicator_apply]
    congr 1
    exact propext (mul_mem_doubleCosetSet_right K g k x)

@[simp] theorem doubleCosetIndicator_one :
    doubleCosetIndicator K hK (1 : G) = subgroupIndicator K hK := by
  ext x
  simp

theorem doubleCosetIndicator_eq_of_mem {g a : G} (ha : a ∈ doubleCosetSet K g) :
    doubleCosetIndicator K hK a = doubleCosetIndicator K hK g := by
  ext x
  simp only [doubleCosetIndicator_apply, doubleCosetSet_eq_of_mem K ha]

end TestFunction

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

namespace HeckeAlgebra.Corner

/-- The actual `K g K` indicator divided by the Haar mass of `K`, as an element
of the unital convolution corner. Thus the identity double coset gives its unit. -/
def doubleCoset (g : G) : Corner μ K hK :=
  ⟨((μ.real (K : Set G) : ℂ)⁻¹) • TestFunction.doubleCosetIndicator K hK g,
    (TestFunction.biInvariant K.toSubgroup K.toSubgroup).smul_mem _
      (TestFunction.doubleCosetIndicator_mem K hK g)⟩

@[simp] theorem doubleCoset_apply (g x : G) :
    doubleCoset K hK μ g x = (μ.real (K : Set G) : ℂ)⁻¹ *
      (TestFunction.doubleCosetSet K g).indicator (fun _ => (1 : ℂ)) x := rfl

theorem doubleCoset_apply_of_mass_one (hμ : μ.real (K : Set G) = 1) (g x : G) :
    doubleCoset K hK μ g x =
      (TestFunction.doubleCosetSet K g).indicator (fun _ => (1 : ℂ)) x := by
  simp [hμ]

@[simp] theorem doubleCoset_one : doubleCoset K hK μ (1 : G) = 1 := by
  apply Subtype.ext
  change ((μ.real (K : Set G) : ℂ)⁻¹) • TestFunction.doubleCosetIndicator K hK 1 = _
  rw [TestFunction.doubleCosetIndicator_one]
  rfl

theorem doubleCoset_eq_of_mem {g a : G} (ha : a ∈ TestFunction.doubleCosetSet K g) :
    doubleCoset K hK μ a = doubleCoset K hK μ g := by
  apply Subtype.ext
  change ((μ.real (K : Set G) : ℂ)⁻¹) • TestFunction.doubleCosetIndicator K hK a = _
  rw [TestFunction.doubleCosetIndicator_eq_of_mem K hK ha]
  rfl

end HeckeAlgebra.Corner

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The actual integrated double-coset operator on the existing spherical fixed space. -/
def doubleCosetOperator (g : G) : Module.End ℂ (fixedVectors ρ K.toSubgroup) :=
  cornerAction μ ρ hρ K hK (HeckeAlgebra.Corner.doubleCoset K hK μ g)

@[simp] theorem doubleCosetOperator_apply (g : G) (v : fixedVectors ρ K.toSubgroup) :
    (doubleCosetOperator K hK μ ρ hρ g v : V) =
      heckeAction μ ρ hρ
        (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
          (HeckeAlgebra.Corner.doubleCoset K hK μ g)) v := rfl

@[simp] theorem doubleCosetOperator_one :
    doubleCosetOperator K hK μ ρ hρ (1 : G) = 1 := by
  unfold doubleCosetOperator
  rw [HeckeAlgebra.Corner.doubleCoset_one, map_one]

theorem doubleCosetOperator_eq_of_mem {g a : G}
    (ha : a ∈ TestFunction.doubleCosetSet K g) :
    doubleCosetOperator K hK μ ρ hρ a = doubleCosetOperator K hK μ ρ hρ g := by
  unfold doubleCosetOperator
  rw [HeckeAlgebra.Corner.doubleCoset_eq_of_mem K hK μ ha]

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual double-coset operators commute with representation intertwiners. -/
theorem doubleCosetOperator_intertwiner {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) (g : G) (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsMap T K.toSubgroup (doubleCosetOperator K hK μ ρ hρ g v) =
      doubleCosetOperator K hK μ σ hσ g (fixedVectorsMap T K.toSubgroup v) :=
  cornerAction_intertwiner μ ρ hρ K hK hσ T _ v

end Langlands.Hecke
