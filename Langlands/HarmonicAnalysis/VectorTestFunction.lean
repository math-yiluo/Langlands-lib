import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Vector-valued test functions and their canonical tensor maps

Renard II.1.2, equations (II.1.2.3)--(II.1.2.4).
The value space has no topology.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.HarmonicAnalysis.VectorTestFunction

universe uX uV

variable (X : Type uX) [TopologicalSpace X]
variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The actual compact-support submodule of the existing locally constant maps. -/
def compactlySupportedSubmodule : Submodule ℂ (LocallyConstant X V) where
  carrier := {f | HasCompactSupport (f : X → V)}
  zero_mem' := HasCompactSupport.zero
  add_mem' hf hg := hf.add hg
  smul_mem' _ _ hf := hf.smul_left

/-- Renard's `D(X,V)`, with its inherited complex vector space structure. -/
abbrev Space := ↥(compactlySupportedSubmodule X V)

instance : CoeFun (Space X V) (fun _ => X → V) := ⟨fun f => f.1⟩

variable {X V}

@[simp]
theorem mem_compactlySupportedSubmodule (f : LocallyConstant X V) :
    f ∈ compactlySupportedSubmodule X V ↔ HasCompactSupport (f : X → V) := Iff.rfl

namespace Space

theorem locallyConstant (f : Space X V) : IsLocallyConstant (f : X → V) :=
  f.1.isLocallyConstant

theorem hasCompactSupport (f : Space X V) : HasCompactSupport (f : X → V) := f.2

@[ext]
theorem ext {f g : Space X V} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (LocallyConstant.ext h)

@[simp]
theorem zero_apply (x : X) : (0 : Space X V) x = 0 := rfl

@[simp]
theorem add_apply (f g : Space X V) (x : X) : (f + g) x = f x + g x := rfl

@[simp]
theorem smul_apply (c : ℂ) (f : Space X V) (x : X) : (c • f) x = c • f x := rfl

end Space

/-- Forget compact support without changing the underlying locally constant map. -/
def inclusion : Space X V →ₗ[ℂ] LocallyConstant X V :=
  (compactlySupportedSubmodule X V).subtype

@[simp]
theorem inclusion_apply (f : Space X V) (x : X) : inclusion f x = f x := rfl

/-- Agreement with the Library's original scalar Schwartz--Bruhat carrier. -/
def scalarEquiv : SchwartzBruhat X ≃ₗ[ℂ] Space X ℂ where
  toFun f := ⟨⟨f, f.locallyConstant⟩, f.hasCompactSupport⟩
  invFun f := ⟨f, f.locallyConstant, f.hasCompactSupport⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem scalarEquiv_apply (f : SchwartzBruhat X) (x : X) : scalarEquiv f x = f x := rfl

@[simp]
theorem scalarEquiv_symm_apply (f : Space X ℂ) (x : X) :
    scalarEquiv.symm f x = f x := rfl

/-- The original scalar test functions viewed as locally constant functions. -/
def scalarInclusion : SchwartzBruhat X →ₗ[ℂ] LocallyConstant X ℂ :=
  inclusion.comp scalarEquiv.toLinearMap

@[simp]
theorem scalarInclusion_apply (f : SchwartzBruhat X) (x : X) :
    scalarInclusion f x = f x := rfl

/-- The bilinear map `(f,v) ↦ (x ↦ f(x) • v)` on locally constant functions. -/
def smoothBilinear :
    LocallyConstant X ℂ →ₗ[ℂ] V →ₗ[ℂ] LocallyConstant X V where
  toFun f :=
    { toFun v := ⟨fun x => f x • v, f.isLocallyConstant.comp (fun z => z • v)⟩
      map_add' v w := by
        ext x
        exact smul_add (f x) v w
      map_smul' c v := by
        ext x
        exact smul_comm (f x) c v }
  map_add' f g := by
    ext v x
    exact add_smul (f x) (g x) v
  map_smul' c f := by
    ext v x
    exact mul_smul c (f x) v

@[simp]
theorem smoothBilinear_apply (f : LocallyConstant X ℂ) (v : V) (x : X) :
    smoothBilinear f v x = f x • v := rfl

/-- The canonical algebraic tensor map of equation (II.1.2.3). -/
def smoothTensorMap :
    (LocallyConstant X ℂ ⊗[ℂ] V) →ₗ[ℂ] LocallyConstant X V :=
  TensorProduct.lift smoothBilinear

@[simp]
theorem smoothTensorMap_tmul (f : LocallyConstant X ℂ) (v : V) :
    smoothTensorMap (f ⊗ₜ[ℂ] v) = smoothBilinear f v :=
  TensorProduct.lift.tmul _ _

@[simp]
theorem smoothTensorMap_tmul_apply (f : LocallyConstant X ℂ) (v : V) (x : X) :
    smoothTensorMap (f ⊗ₜ[ℂ] v) x = f x • v := rfl

/-- The same bilinear map with the original scalar compact tests as its input. -/
def compactBilinear : SchwartzBruhat X →ₗ[ℂ] V →ₗ[ℂ] Space X V where
  toFun f :=
    { toFun v :=
        ⟨smoothBilinear (scalarInclusion f) v,
          f.hasCompactSupport.comp_left (g := fun z : ℂ => z • v) (zero_smul ℂ v)⟩
      map_add' v w := by
        ext x
        exact smul_add (f x) v w
      map_smul' c v := by
        ext x
        exact smul_comm (f x) c v }
  map_add' f g := by
    ext v x
    exact add_smul (f x) (g x) v
  map_smul' c f := by
    ext v x
    exact mul_smul c (f x) v

@[simp]
theorem compactBilinear_apply (f : SchwartzBruhat X) (v : V) (x : X) :
    compactBilinear f v x = f x • v := rfl

/-- The canonical algebraic tensor map of equation (II.1.2.4). -/
def compactTensorMap : (SchwartzBruhat X ⊗[ℂ] V) →ₗ[ℂ] Space X V :=
  TensorProduct.lift compactBilinear

@[simp]
theorem compactTensorMap_tmul (f : SchwartzBruhat X) (v : V) :
    compactTensorMap (f ⊗ₜ[ℂ] v) = compactBilinear f v :=
  TensorProduct.lift.tmul _ _

@[simp]
theorem compactTensorMap_tmul_apply (f : SchwartzBruhat X) (v : V) (x : X) :
    compactTensorMap (f ⊗ₜ[ℂ] v) x = f x • v := rfl

/-- The two tensor maps commute with the actual inclusions, on every tensor. -/
theorem inclusion_compactTensorMap (t : SchwartzBruhat X ⊗[ℂ] V) :
    inclusion (compactTensorMap t) =
      smoothTensorMap (TensorProduct.map scalarInclusion (LinearMap.id : V →ₗ[ℂ] V) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f v =>
      ext x
      simp
  | add t s ht hs =>
      simp only [map_add, ht, hs]

end Langlands.HarmonicAnalysis.VectorTestFunction
