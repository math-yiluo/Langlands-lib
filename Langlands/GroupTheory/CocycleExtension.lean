import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.MulAction

/-! # Extensions constructed from normalized multiplicative two-cocycles -/

namespace Langlands

universe u v

variable (G : Type u) (A : Type v) [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- A multiplicative two-cocycle with value one at the pair of identities. -/
structure NormalizedTwoCocycle where
  toFun : G × G → A
  cocycle : groupCohomology.IsMulCocycle₂ toFun
  normalized : toFun (1, 1) = 1

namespace NormalizedTwoCocycle

variable {G A}

instance : CoeFun (NormalizedTwoCocycle G A) (fun _ => G × G → A) :=
  ⟨toFun⟩

variable (c : NormalizedTwoCocycle G A)

@[simp] theorem one_left (g : G) : c (1, g) = 1 :=
  (groupCohomology.map_one_fst_of_isMulCocycle₂ c.cocycle g).trans c.normalized

@[simp] theorem one_right (g : G) : c (g, 1) = 1 := by
  rw [groupCohomology.map_one_snd_of_isMulCocycle₂ c.cocycle g, c.normalized,
    smul_one]

theorem inv_pair (g : G) : g • c (g⁻¹, g) = c (g, g⁻¹) := by
  have h := c.cocycle g g⁻¹ g
  simpa only [mul_inv_cancel, inv_mul_cancel, c.one_left, c.one_right, one_mul,
    mul_one] using h.symm

/-- The underlying set of the extension, with a separate type for its twisted group law. -/
@[ext]
structure Extension (c : NormalizedTwoCocycle G A) where
  left : A
  right : G

namespace Extension

instance : Mul c.Extension where
  mul x y := ⟨x.left * (x.right • y.left) * c (x.right, y.right), x.right * y.right⟩

instance : One c.Extension := ⟨⟨1, 1⟩⟩

instance : Inv c.Extension where
  inv x := ⟨(x.right⁻¹ • x.left⁻¹) * (c (x.right⁻¹, x.right))⁻¹, x.right⁻¹⟩

@[simp] theorem mul_left (x y : c.Extension) :
    (x * y).left = x.left * (x.right • y.left) * c (x.right, y.right) := rfl

@[simp] theorem mul_right (x y : c.Extension) :
    (x * y).right = x.right * y.right := rfl

@[simp] theorem one_left : (1 : c.Extension).left = 1 := rfl
@[simp] theorem one_right : (1 : c.Extension).right = 1 := rfl

@[simp] theorem inv_left (x : c.Extension) :
    x⁻¹.left = (x.right⁻¹ • x.left⁻¹) * (c (x.right⁻¹, x.right))⁻¹ := rfl

@[simp] theorem inv_right (x : c.Extension) : x⁻¹.right = x.right⁻¹ := rfl

instance : Group c.Extension where
  mul_assoc x y z := by
    apply Extension.ext
    · simp only [mul_left, mul_right, smul_mul', ← mul_smul]
      calc
        _ = (x.left * (x.right • y.left) * ((x.right * y.right) • z.left)) *
            (c (x.right * y.right, z.right) * c (x.right, y.right)) := by ac_rfl
        _ = _ := by rw [c.cocycle]; ac_rfl
    · exact mul_assoc x.right y.right z.right
  one_mul x := Extension.ext (by simp) (by simp)
  mul_one x := Extension.ext (by simp) (by simp)
  inv_mul_cancel x := Extension.ext
    (by simp [mul_comm]) (by simp)

/-- The inclusion of the coefficient group in the extension. -/
def inl : A →* c.Extension where
  toFun a := ⟨a, 1⟩
  map_one' := rfl
  map_mul' a b := Extension.ext (by simp) (by simp)

/-- The projection to the acting group. -/
def projection : c.Extension →* G where
  toFun := Extension.right
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The distinguished set-theoretic section; it need not be a homomorphism. -/
def sectionMap (g : G) : c.Extension := ⟨1, g⟩

@[simp] theorem inl_left (a : A) : (inl c a).left = a := rfl
@[simp] theorem inl_right (a : A) : (inl c a).right = 1 := rfl
@[simp] theorem projection_apply (x : c.Extension) : projection c x = x.right := rfl
@[simp] theorem sectionMap_left (g : G) : (sectionMap c g).left = 1 := rfl
@[simp] theorem sectionMap_right (g : G) : (sectionMap c g).right = g := rfl
@[simp] theorem projection_inl (a : A) : projection c (inl c a) = 1 := rfl
@[simp] theorem projection_sectionMap (g : G) : projection c (sectionMap c g) = g := rfl

theorem inl_injective : Function.Injective (inl c) := by
  intro a b h
  exact congrArg Extension.left h

theorem projection_surjective : Function.Surjective (projection c) :=
  fun g => ⟨sectionMap c g, rfl⟩

theorem range_inl_eq_ker_projection : (inl c).range = (projection c).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hx
    have hx' : x.right = 1 := hx
    exact ⟨x.left, Extension.ext rfl hx'.symm⟩

theorem inl_mul_sectionMap (x : c.Extension) :
    inl c x.left * sectionMap c x.right = x := by
  apply Extension.ext <;> simp

theorem sectionMap_mul (g h : G) :
    sectionMap c g * sectionMap c h =
      inl c (c (g, h)) * sectionMap c (g * h) := by
  apply Extension.ext <;> simp

theorem sectionMap_factorSet (g h : G) :
    sectionMap c g * sectionMap c h * (sectionMap c (g * h))⁻¹ = inl c (c (g, h)) := by
  rw [sectionMap_mul, mul_inv_cancel_right]

theorem mul_inl (x : c.Extension) (a : A) :
    x * inl c a = inl c (x.right • a) * x := by
  apply Extension.ext <;> simp [mul_comm]

theorem conjugate_inl (x : c.Extension) (a : A) :
    x * inl c a * x⁻¹ = inl c (x.right • a) := by
  rw [mul_inl, mul_inv_cancel_right]

/-- The product coordinates on the extension. -/
def equivProd : c.Extension ≃ A × G where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Topology

variable [TopologicalSpace G] [TopologicalSpace A]

instance : TopologicalSpace c.Extension :=
  TopologicalSpace.induced (equivProd c) inferInstance

theorem continuous_left : Continuous (Extension.left : c.Extension → A) :=
  continuous_fst.comp (continuous_induced_dom : Continuous (equivProd c))

theorem continuous_right : Continuous (Extension.right : c.Extension → G) :=
  continuous_snd.comp (continuous_induced_dom : Continuous (equivProd c))

/-- The topology is exactly the product topology in the displayed coordinates. -/
def homeomorphProd : c.Extension ≃ₜ A × G where
  __ := equivProd c
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

theorem continuous_inl : Continuous (inl c) :=
  continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)

theorem continuous_projection : Continuous (projection c) :=
  continuous_right c

theorem continuous_sectionMap : Continuous (sectionMap c) :=
  continuous_induced_rng.mpr (continuous_const.prodMk continuous_id)

variable [IsTopologicalGroup G] [IsTopologicalGroup A] [ContinuousSMul G A]

/-- Continuous cocycles give topological groups with the product topology. -/
theorem topologicalGroup (hc : Continuous c) : IsTopologicalGroup c.Extension where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    exact (((continuous_left c).comp continuous_fst |>.mul
      (((continuous_right c).comp continuous_fst).smul
        ((continuous_left c).comp continuous_snd))).mul
          (hc.comp (((continuous_right c).comp continuous_fst).prodMk
            ((continuous_right c).comp continuous_snd)))).prodMk
      (((continuous_right c).comp continuous_fst).mul
        ((continuous_right c).comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact (((continuous_right c).inv.smul (continuous_left c).inv).mul
      (hc.comp ((continuous_right c).inv.prodMk (continuous_right c))).inv).prodMk
        (continuous_right c).inv

end Topology

end Extension
end NormalizedTwoCocycle
end Langlands
