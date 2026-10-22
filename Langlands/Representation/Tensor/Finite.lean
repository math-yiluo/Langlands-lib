import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.CategoryTheory.Pi.Basic
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Finite tensor actions and external tensor products for block Levi groups. -/

noncomputable section

open scoped TensorProduct
open CategoryTheory

namespace Langlands.FiniteTensor

universe uR uI uG uV uW uX

variable {R : Type uR} [CommRing R] {ι : Type uI}
variable {G : Type uG} [Group G]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
variable {X : ι → Type uX} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]

/-- The actual factorwise action on Mathlib's indexed tensor product. -/
def action (ρ : ∀ i, Representation R G (V i)) :
    Representation R G (PiTensorProduct R V) where
  toFun g := PiTensorProduct.map (fun i => ρ i g)
  map_one' := by
    simp only [map_one, PiTensorProduct.map_one]
  map_mul' g h := by
    simp only [map_mul, PiTensorProduct.map_mul]

@[simp]
theorem action_tprod (ρ : ∀ i, Representation R G (V i))
    (g : G) (v : ∀ i, V i) :
    action ρ g (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => ρ i g (v i)) :=
  PiTensorProduct.map_tprod _ _

/-- Tensoring actual intertwiners gives an actual intertwiner. -/
def map {ρ : ∀ i, Representation R G (V i)} {σ : ∀ i, Representation R G (W i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i)) :
    (action ρ).IntertwiningMap (action σ) where
  toLinearMap := PiTensorProduct.map (fun i => (f i).toLinearMap)
  isIntertwining' g := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      action_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    exact DFunLike.congr_fun ((f i).isIntertwining' g) (v i)

@[simp]
theorem map_tprod {ρ : ∀ i, Representation R G (V i)}
    {σ : ∀ i, Representation R G (W i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i)) (v : ∀ i, V i) :
    map f (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => f i (v i)) :=
  PiTensorProduct.map_tprod _ _

@[simp]
theorem map_id (ρ : ∀ i, Representation R G (V i)) :
    map (fun i => Representation.IntertwiningMap.id (ρ i)) =
      Representation.IntertwiningMap.id (action ρ) := by
  apply Representation.IntertwiningMap.ext
  exact PiTensorProduct.map_id

theorem map_comp {ρ : ∀ i, Representation R G (V i)}
    {σ : ∀ i, Representation R G (W i)} {τ : ∀ i, Representation R G (X i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i))
    (h : ∀ i, (σ i).IntertwiningMap (τ i)) :
    map (fun i => (h i).comp (f i)) = (map h).comp (map f) := by
  apply Representation.IntertwiningMap.ext
  exact PiTensorProduct.map_comp _ _

variable [TopologicalSpace G]

/-- A finite family of open stabilizers fixes the pure tensor. -/
theorem isSmoothVector_tprod [Finite ι] (ρ : ∀ i, Representation R G (V i))
    (v : ∀ i, V i) (hv : ∀ i, IsSmoothVector (ρ i) (v i)) :
    IsSmoothVector (action ρ) (PiTensorProduct.tprod R v) := by
  classical
  let := Fintype.ofFinite ι
  choose K hK using hv
  refine ⟨Finset.univ.inf K, ?_⟩
  intro g
  change action ρ (g : G) (PiTensorProduct.tprod R v) = PiTensorProduct.tprod R v
  rw [action_tprod]
  congr 1
  funext i
  have hle : Finset.univ.inf K ≤ K i := Finset.inf_le (Finset.mem_univ i)
  exact hK i ⟨g, hle g.property⟩

/-- Smoothness follows from pure-tensor spanning and finite intersections of stabilizers. -/
theorem isSmooth_action [Finite ι] (ρ : ∀ i, Representation R G (V i))
    (hρ : ∀ i, IsSmooth (ρ i)) : IsSmooth (action ρ) := by
  intro v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    exact isSmoothVector_smul a (isSmoothVector_tprod ρ v (fun i => hρ i (v i)))
  | add x y hx hy => exact isSmoothVector_add hx hy

/-- The indexed tensor of genuine smooth objects, retaining its natural universe. -/
def smoothObject [Finite ι] (A : ι → SmoothRep.{uR, uG, uV} R G) :
    SmoothRep.{uR, uG, max uR uI uV} R G :=
  ⟨Rep.of (action (fun i => (A i).obj.ρ)),
    isSmooth_action _ (fun i => (A i).property)⟩

section External

variable {H : ι → Type uG} [∀ i, Group (H i)]

/-- The actual external tensor product, through the coordinate homomorphisms. -/
def external (ρ : ∀ i, Representation R (H i) (V i)) :
    Representation R (∀ i, H i) (PiTensorProduct R V) :=
  action (fun i => (ρ i).comp (Pi.evalMonoidHom H i))

@[simp]
theorem external_tprod (ρ : ∀ i, Representation R (H i) (V i))
    (g : ∀ i, H i) (v : ∀ i, V i) :
    external ρ g (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => ρ i (g i) (v i)) :=
  action_tprod _ _ _

/-- External tensor products of the actual factor intertwiners. -/
def externalMap {ρ : ∀ i, Representation R (H i) (V i)}
    {σ : ∀ i, Representation R (H i) (W i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i)) :
    (external ρ).IntertwiningMap (external σ) :=
  map (ρ := fun i => (ρ i).comp (Pi.evalMonoidHom H i))
    (σ := fun i => (σ i).comp (Pi.evalMonoidHom H i))
    (fun i => {
      toLinearMap := (f i).toLinearMap
      isIntertwining' g := (f i).isIntertwining' (g i) })

@[simp]
theorem externalMap_tprod {ρ : ∀ i, Representation R (H i) (V i)}
    {σ : ∀ i, Representation R (H i) (W i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i)) (v : ∀ i, V i) :
    externalMap f (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => f i (v i)) :=
  PiTensorProduct.map_tprod _ _

@[simp]
theorem externalMap_id (ρ : ∀ i, Representation R (H i) (V i)) :
    externalMap (fun i => Representation.IntertwiningMap.id (ρ i)) =
      Representation.IntertwiningMap.id (external ρ) := by
  apply Representation.IntertwiningMap.ext
  exact PiTensorProduct.map_id

theorem externalMap_comp {ρ : ∀ i, Representation R (H i) (V i)}
    {σ : ∀ i, Representation R (H i) (W i)}
    {τ : ∀ i, Representation R (H i) (X i)}
    (f : ∀ i, (ρ i).IntertwiningMap (σ i))
    (h : ∀ i, (σ i).IntertwiningMap (τ i)) :
    externalMap (fun i => (h i).comp (f i)) =
      (externalMap h).comp (externalMap f) := by
  apply Representation.IntertwiningMap.ext
  exact PiTensorProduct.map_comp _ _

variable [∀ i, TopologicalSpace (H i)]

/-- The finite external product is smooth for the actual product topology. -/
theorem isSmooth_external [Finite ι] (ρ : ∀ i, Representation R (H i) (V i))
    (hρ : ∀ i, IsSmooth (ρ i)) : IsSmooth (external ρ) :=
  isSmooth_action _ (fun i =>
    isSmooth_comp (Pi.evalMonoidHom H i) (continuous_apply i) (hρ i))

/-- Actual smooth block factors give an actual smooth representation of their product group. -/
def externalSmoothObject [Finite ι]
    (A : ∀ i, SmoothRep.{uR, uG, uV} R (H i)) :
    SmoothRep.{uR, max uI uG, max uR uI uV} R (∀ i, H i) :=
  ⟨Rep.of (external (fun i => (A i).obj.ρ)),
    isSmooth_external _ (fun i => (A i).property)⟩

/-- External tensor product as a functor between the canonical smooth categories. -/
def externalFunctor [Finite ι] :
    (∀ i, SmoothRep.{uR, uG, uV} R (H i)) ⥤
      SmoothRep.{uR, max uI uG, max uR uI uV} R (∀ i, H i) where
  obj A := externalSmoothObject A
  map f := SmoothRep.ofHom (externalMap (fun i => SmoothRep.hom (f i)))
  map_id A := by
    change SmoothRep.ofHom (A := externalSmoothObject A) (B := externalSmoothObject A)
      (externalMap (fun i => Representation.IntertwiningMap.id (A i).representation)) =
      SmoothRep.ofHom (Representation.IntertwiningMap.id _)
    rw [externalMap_id]
    rfl
  map_comp {A B C} f h := by
    change SmoothRep.ofHom (A := externalSmoothObject A) (B := externalSmoothObject C)
      (externalMap (fun i => (SmoothRep.hom (h i)).comp (SmoothRep.hom (f i)))) =
      SmoothRep.ofHom
        ((externalMap (fun i => SmoothRep.hom (h i))).comp
          (externalMap (fun i => SmoothRep.hom (f i))))
    rw [externalMap_comp]

end External

end Langlands.FiniteTensor
