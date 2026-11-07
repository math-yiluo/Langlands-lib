import Langlands.GroupTheory.CocycleClassEquiv
import Mathlib.Tactic.Group

/-! # Pushing out a group extension along an equivariant kernel map -/

noncomputable section

namespace Langlands.GroupExtensionPushout

universe u v

variable {W : Type u} {G : Type v} {A : Type v}
  [Group W] [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- Conjugation of the kernel by an element of the extension group. -/
def conjugateKernel (q : W →* G) (x : W) (n : q.ker) : q.ker :=
  ⟨x * n * x⁻¹, by simp [show q n = 1 from n.property]⟩

/-- A section of a surjective group homomorphism, normalized at the identity. -/
structure Section (q : W →* G) where
  toFun : G → W
  right_inv : ∀ g, q (toFun g) = g
  normalized : toFun 1 = 1

namespace Section

variable {q : W →* G}

instance : CoeFun (Section q) (fun _ => G → W) := ⟨toFun⟩

/-- A normalized section chosen from surjectivity. -/
def ofSurjective (hq : Function.Surjective q) : Section q := by
  classical
  exact
    { toFun := fun g => if g = 1 then 1 else (hq g).choose
      right_inv := fun g => by
        split_ifs with h
        · exact q.map_one.trans h.symm
        · exact (hq g).choose_spec
      normalized := by simp }

variable (s : Section q)

@[simp] theorem map_apply (g : G) : q (s g) = g := s.right_inv g
@[simp] theorem map_one : s 1 = 1 := s.normalized

/-- The kernel coordinate of an element relative to the section. -/
def kernelPart (x : W) : q.ker :=
  ⟨x * (s (q x))⁻¹, by simp⟩

/-- The factor set before applying the abelian kernel map. -/
def factorKernel (g h : G) : q.ker :=
  ⟨s g * s h * (s (g * h))⁻¹, by simp⟩

@[simp] theorem kernelPart_one : s.kernelPart 1 = 1 := by
  apply Subtype.ext
  simp [kernelPart]

@[simp] theorem kernelPart_kernel (n : q.ker) : s.kernelPart n = n := by
  apply Subtype.ext
  simp [kernelPart, show q n = 1 from n.property]

@[simp] theorem factorKernel_one_one : s.factorKernel 1 1 = 1 := by
  apply Subtype.ext
  simp [factorKernel]

/-- Associativity of three section values gives the kernel factor-set identity. -/
theorem factorKernel_identity (g h j : G) :
    s.factorKernel g h * s.factorKernel (g * h) j =
      conjugateKernel q (s g) (s.factorKernel h j) * s.factorKernel g (h * j) := by
  apply Subtype.ext
  change (s g * s h * (s (g * h))⁻¹) *
      (s (g * h) * s j * (s ((g * h) * j))⁻¹) =
    (s g * (s h * s j * (s (h * j))⁻¹) * (s g)⁻¹) *
      (s g * s (h * j) * (s (g * (h * j)))⁻¹)
  rw [mul_assoc g h j]
  group

/-- Multiplication expressed in kernel and section coordinates. -/
theorem kernelPart_mul (x y : W) :
    s.kernelPart (x * y) = s.kernelPart x *
      conjugateKernel q (s (q x)) (s.kernelPart y) * s.factorKernel (q x) (q y) := by
  apply Subtype.ext
  change x * y * (s (q (x * y)))⁻¹ =
    (x * (s (q x))⁻¹) *
      (s (q x) * (y * (s (q y))⁻¹) * (s (q x))⁻¹) *
      (s (q x) * s (q y) * (s (q x * q y))⁻¹)
  rw [q.map_mul]
  group

variable (r : q.ker →* A)
  (hr : ∀ (x : W) (n : q.ker), r (conjugateKernel q x n) = q x • r n)

/-- The normalized abelian factor cocycle of the chosen section. -/
def cocycle : NormalizedTwoCocycle G A where
  toFun gh := r (s.factorKernel gh.1 gh.2)
  cocycle g h j := by
    have he := congrArg r (s.factorKernel_identity g h j)
    simp only [map_mul, hr, s.map_apply] at he
    simpa only [mul_comm] using he
  normalized := by simp

/-- The pushout map in the chosen coordinates. -/
def toMonoidHom : W →* (s.cocycle r hr).Extension where
  toFun x := ⟨r (s.kernelPart x), q x⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    apply NormalizedTwoCocycle.Extension.ext
    · change r (s.kernelPart (x * y)) =
        r (s.kernelPart x) * (q x • r (s.kernelPart y)) * r (s.factorKernel (q x) (q y))
      rw [s.kernelPart_mul, map_mul, map_mul, hr, s.map_apply]
    · exact q.map_mul x y

@[simp] theorem projection_toMonoidHom (x : W) :
    NormalizedTwoCocycle.Extension.projection (s.cocycle r hr) (s.toMonoidHom r hr x) = q x := rfl

@[simp] theorem toMonoidHom_kernel (n : q.ker) :
    s.toMonoidHom r hr n = NormalizedTwoCocycle.Extension.inl (s.cocycle r hr) (r n) := by
  apply NormalizedTwoCocycle.Extension.ext
  · simp [toMonoidHom]
  · exact n.property

/-- Changing the normalized section does not change the second cohomology class. -/
theorem cohomologyClass_eq (t : Section q) :
    NormalizedTwoCocycle.cohomologyClass (s.cocycle r hr) =
      NormalizedTwoCocycle.cohomologyClass (t.cocycle r hr) := by
  apply NormalizedTwoCocycle.cohomologyClass_eq_of_cochain _ _
    (fun g => r (t.kernelPart (s g)))
  intro g h
  have he : t.kernelPart (s g * s h) =
      s.factorKernel g h * t.kernelPart (s (g * h)) := by
    apply Subtype.ext
    change s g * s h * (t (q (s g * s h)))⁻¹ =
      (s g * s h * (s (g * h))⁻¹) * (s (g * h) * (t (q (s (g * h))))⁻¹)
    simp only [q.map_mul, s.map_apply]
    group
  change r (s.factorKernel g h) * r (t.kernelPart (s (g * h))) =
    r (t.kernelPart (s g)) * (g • r (t.kernelPart (s h))) * r (t.factorKernel g h)
  rw [← map_mul, ← he, t.kernelPart_mul, map_mul, map_mul, hr]
  simp only [s.map_apply, t.map_apply]

section Topology

variable [TopologicalSpace W] [IsTopologicalGroup W]
  [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace A]

/-- Over a discrete quotient, the kernel coordinate is continuous. -/
theorem continuous_kernelPart (hq : Continuous q) : Continuous s.kernelPart :=
  (continuous_id.mul ((continuous_of_discreteTopology : Continuous s).comp hq).inv).subtype_mk _

/-- The pushout map is continuous when the quotient and kernel maps are continuous. -/
def toContinuousMonoidHom (hq : Continuous q) (hrc : Continuous r) :
    W →ₜ* (s.cocycle r hr).Extension where
  toMonoidHom := s.toMonoidHom r hr
  continuous_toFun := continuous_induced_rng.mpr
    ((hrc.comp (s.continuous_kernelPart hq)).prodMk hq)

@[simp] theorem projection_toContinuousMonoidHom
    (hq : Continuous q) (hrc : Continuous r) (x : W) :
    NormalizedTwoCocycle.Extension.projection (s.cocycle r hr)
      (s.toContinuousMonoidHom r hr hq hrc x) = q x := rfl

@[simp] theorem toContinuousMonoidHom_kernel
    (hq : Continuous q) (hrc : Continuous r) (n : q.ker) :
    s.toContinuousMonoidHom r hr hq hrc n =
      NormalizedTwoCocycle.Extension.inl (s.cocycle r hr) (r n) :=
  s.toMonoidHom_kernel r hr n

end Topology

end Section

end Langlands.GroupExtensionPushout
