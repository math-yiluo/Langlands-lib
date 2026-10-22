import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Clopen
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Tactic

/-!
# Concrete archimedean Weil groups

The real group has coordinates `z * j^e`, with `j^2 = -1` and
`j * z = conjugate(z) * j`. Its topology is the product with discrete `Bool`.
-/

noncomputable section

namespace Langlands.Weil.Archimedean

/-- The complex Weil group with the usual topology on nonzero complex numbers. -/
abbrev ComplexWeil := ℂˣ

/-- The normalized complex absolute value, `z ↦ z * conjugate(z)`. -/
def complexNorm : ComplexWeil →ₜ* ℝˣ where
  toMonoidHom := Units.map Complex.normSq.toMonoidHom
  continuous_toFun := Complex.continuous_normSq.units_map _

@[simp]
theorem complexNorm_apply (z : ComplexWeil) :
    (complexNorm z : ℝ) = Complex.normSq (z : ℂ) := rfl

theorem complexNorm_pos (z : ComplexWeil) : 0 < (complexNorm z : ℝ) :=
  Complex.normSq_pos.mpr z.ne_zero

/-- Coordinates `z * j^e` in the nonsplit real Weil group. -/
def RealWeil := ℂˣ × Bool

namespace RealWeil

instance : TopologicalSpace RealWeil := inferInstanceAs (TopologicalSpace (ℂˣ × Bool))

/-- The nonzero complex coordinate. It is not a group homomorphism. -/
def complexPart (w : RealWeil) : ℂˣ := w.1

/-- Whether the element belongs to the `j` coset. -/
def parity (w : RealWeil) : Bool := w.2

private def multiplication (x y : RealWeil) : RealWeil :=
  (x.1 * (if x.2 then star y.1 else y.1) * (if x.2 && y.2 then -1 else 1),
    Bool.xor x.2 y.2)

private def inversion (x : RealWeil) : RealWeil :=
  (if x.2 then -star (x.1⁻¹) else x.1⁻¹, x.2)

instance : Group RealWeil where
  one := (1, false)
  mul := multiplication
  inv := inversion
  one_mul := by
    change ∀ x, multiplication (1, false) x = x
    rintro ⟨z, b⟩
    change @Eq (ℂˣ × Bool) _ _
    cases b <;> simp [multiplication]
  mul_one := by
    change ∀ x, multiplication x (1, false) = x
    rintro ⟨z, b⟩
    change @Eq (ℂˣ × Bool) _ _
    cases b <;> simp [multiplication]
  mul_assoc := by
    change ∀ x y z, multiplication (multiplication x y) z =
      multiplication x (multiplication y z)
    rintro ⟨z, a⟩ ⟨w, b⟩ ⟨v, c⟩
    change @Eq (ℂˣ × Bool) _ _
    cases a <;> cases b <;> cases c <;>
      simp [multiplication, mul_assoc, mul_left_comm, mul_comm]
    apply Units.ext
    simp [mul_comm]
  inv_mul_cancel := by
    change ∀ x, multiplication (inversion x) x = (1, false)
    rintro ⟨z, b⟩
    change @Eq (ℂˣ × Bool) _ _
    cases b <;> simp [multiplication, inversion, mul_comm]

@[ext]
theorem ext {x y : RealWeil} (hz : x.complexPart = y.complexPart)
    (hb : x.parity = y.parity) : x = y := Prod.ext hz hb

@[simp]
theorem parity_mul (x y : RealWeil) : (x * y).parity = Bool.xor x.parity y.parity := rfl

@[simp]
theorem parity_one : (1 : RealWeil).parity = false := rfl

@[simp]
theorem parity_inv (x : RealWeil) : x⁻¹.parity = x.parity := rfl

@[fun_prop]
theorem continuous_complexPart : Continuous complexPart := continuous_fst

@[fun_prop]
theorem continuous_parity : Continuous parity := continuous_snd

private theorem continuous_bool_if {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {b : X → Bool} {f g : X → Y} (hb : Continuous b)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ if b x then f x else g x) := by
  have hc : IsClopen {x | b x = true} := (isClopen_discrete {true}).preimage hb
  exact Continuous.if (by simp [hc.frontier_eq]) hf hg

instance : IsTopologicalGroup RealWeil where
  continuous_mul := by
    have hx : Continuous (fun p : RealWeil × RealWeil ↦ p.1.complexPart) :=
      continuous_complexPart.comp continuous_fst
    have hy : Continuous (fun p : RealWeil × RealWeil ↦ p.2.complexPart) :=
      continuous_complexPart.comp continuous_snd
    have ha : Continuous (fun p : RealWeil × RealWeil ↦ p.1.parity) :=
      continuous_parity.comp continuous_fst
    have hb : Continuous (fun p : RealWeil × RealWeil ↦ p.2.parity) :=
      continuous_parity.comp continuous_snd
    have hand : Continuous (fun p : RealWeil × RealWeil ↦ p.1.parity && p.2.parity) :=
      (continuous_of_discreteTopology (f := fun q : Bool × Bool ↦ q.1 && q.2)).comp
        (ha.prodMk hb)
    have hxor : Continuous (fun p : RealWeil × RealWeil ↦ Bool.xor p.1.parity p.2.parity) :=
      (continuous_of_discreteTopology (f := fun q : Bool × Bool ↦ Bool.xor q.1 q.2)).comp
        (ha.prodMk hb)
    exact ((hx.mul (continuous_bool_if ha hy.star hy)).mul
      (continuous_bool_if hand continuous_const continuous_const)).prodMk hxor
  continuous_inv := by
    change Continuous (fun a : RealWeil ↦
      (if a.parity then -star (a.complexPart⁻¹) else a.complexPart⁻¹, a.parity))
    have hn : Continuous (fun a : RealWeil ↦ (-1 : ℂˣ) * star (a.complexPart⁻¹)) :=
      continuous_const.mul continuous_complexPart.inv.star
    apply ((continuous_bool_if continuous_parity hn
      continuous_complexPart.inv).prodMk continuous_parity).congr
    intro a
    simp only [neg_one_mul, Pi.inv_apply]

/-- Inclusion of the identity component, the complex Weil group. -/
def ofComplex : ComplexWeil →ₜ* RealWeil where
  toFun z := (z, false)
  map_one' := rfl
  map_mul' z w := by
    change ((z * w, false) : RealWeil) = (z * w * 1, false)
    simp
  continuous_toFun := continuous_id.prodMk continuous_const

/-- The standard element above complex conjugation. -/
def j : RealWeil := (1, true)

@[simp]
theorem j_sq : j * j = ofComplex (-1) := by
  change ((1 * star (1 : ℂˣ) * (-1), false) : RealWeil) = (-1, false)
  simp

@[simp]
theorem j_mul_ofComplex (z : ComplexWeil) : j * ofComplex z = ofComplex (star z) * j := by
  change ((1 * star z * 1, true) : RealWeil) = (star z * 1 * 1, true)
  simp

theorem j_conjugation (z : ComplexWeil) : j * ofComplex z * j⁻¹ = ofComplex (star z) := by
  rw [j_mul_ofComplex, mul_inv_cancel_right]

/-- The coordinate description is exactly the disjoint union of two complex copies. -/
def coordinates : RealWeil ≃ₜ ℂˣ × Bool := Homeomorph.refl _

/-- The complex inclusion is a topological embedding onto an open subgroup. -/
theorem isOpenEmbedding_ofComplex : Topology.IsOpenEmbedding ofComplex := by
  refine ⟨isEmbedding_prodMkLeft false, ?_⟩
  have hr : Set.range ofComplex = parity ⁻¹' {false} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rfl
    · intro h
      exact ⟨x.1, Prod.ext rfl h.symm⟩
  rw [hr]
  exact (isOpen_discrete {false}).preimage continuous_parity

/-- Projection onto the actual real automorphism group of the complex field. -/
def toGalois : RealWeil →ₜ* (ℂ ≃ₐ[ℝ] ℂ) where
  toFun w := if w.parity then Complex.conjAe else 1
  map_one' := rfl
  map_mul' := by
    rintro ⟨z, a⟩ ⟨w, b⟩
    change (if Bool.xor a b then Complex.conjAe else 1) =
      (if a then Complex.conjAe else 1) * (if b then Complex.conjAe else 1)
    cases a <;> cases b <;> ext c <;> simp
  continuous_toFun :=
    (continuous_of_discreteTopology
      (f := fun b : Bool ↦ if b then Complex.conjAe else 1)).comp continuous_parity

@[simp]
theorem toGalois_ofComplex (z : ComplexWeil) : toGalois (ofComplex z) = 1 := rfl

@[simp]
theorem toGalois_j : toGalois j = Complex.conjAe := rfl

theorem toGalois_surjective : Function.Surjective toGalois := by
  intro σ
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · refine ⟨1, ?_⟩
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ ↦ f z) h.symm
  · refine ⟨j, ?_⟩
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ ↦ f z) h.symm

private theorem conj_ne_one : Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) := by
  intro h
  have hi := congrArg (fun f : ℂ ≃ₐ[ℝ] ℂ ↦ (f Complex.I).im) h
  norm_num at hi

@[simp]
theorem toGalois_eq_one (w : RealWeil) : toGalois w = 1 ↔ w.parity = false := by
  change (if w.parity then Complex.conjAe else 1) = 1 ↔ w.parity = false
  cases w.parity <;> simp [conj_ne_one]

theorem ker_toGalois : toGalois.toMonoidHom.ker = ofComplex.toMonoidHom.range := by
  ext w
  change toGalois w = 1 ↔ ∃ z, ofComplex z = w
  rw [toGalois_eq_one]
  constructor
  · intro h
    exact ⟨w.1, Prod.ext rfl h.symm⟩
  · rintro ⟨z, rfl⟩
    rfl

/-- The normalized Weil norm has value `|z|^2` on both components. -/
def norm : RealWeil →ₜ* ℝˣ where
  toFun w := complexNorm w.complexPart
  map_one' := by change complexNorm 1 = 1; exact map_one _
  map_mul' := by
    rintro ⟨z, a⟩ ⟨w, b⟩
    change complexNorm (multiplication (z, a) (w, b)).1 =
      complexNorm z * complexNorm w
    apply Units.ext
    simp only [Units.val_mul, complexNorm_apply]
    cases a <;> cases b <;> simp [multiplication]
  continuous_toFun := complexNorm.continuous.comp continuous_complexPart

theorem norm_pos (w : RealWeil) : 0 < (norm w : ℝ) := complexNorm_pos w.complexPart

@[simp]
theorem norm_ofComplex (z : ComplexWeil) : norm (ofComplex z) = complexNorm z := rfl

@[simp]
theorem norm_j : norm j = 1 := map_one complexNorm

/-- The sign of the component, taking values in the real units. -/
def componentSign : RealWeil →ₜ* ℝˣ where
  toFun w := if w.parity then -1 else 1
  map_one' := rfl
  map_mul' := by
    rintro ⟨z, a⟩ ⟨w, b⟩
    change (if Bool.xor a b then (-1 : ℝˣ) else 1) =
      (if a then -1 else 1) * (if b then -1 else 1)
    cases a <;> cases b <;> simp
  continuous_toFun :=
    (continuous_of_discreteTopology
      (f := fun b : Bool ↦ if b then (-1 : ℝˣ) else 1)).comp continuous_parity

/-- The explicit real abelian coordinate, `z*j^b ↦ (-1)^b |z|^2`.
Its identification with the abelianization is a separate result. -/
def abelianCoordinate : RealWeil →ₜ* ℝˣ := componentSign * norm

@[simp]
theorem abelianCoordinate_ofComplex (z : ComplexWeil) :
    abelianCoordinate (ofComplex z) = complexNorm z := by
  change 1 * complexNorm z = complexNorm z
  exact one_mul _

@[simp]
theorem abelianCoordinate_j : abelianCoordinate j = -1 := by
  change -1 * complexNorm 1 = (-1 : ℝˣ)
  simp

end RealWeil
end Langlands.Weil.Archimedean
