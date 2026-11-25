import Langlands.LinearAlgebra.Symplectic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.LinearCombination

/-!
# The Heisenberg group of a bilinear form

For a commutative ring `R` in which `2` is invertible, an `R`-module `W` and a bilinear form
`B` on `W`, `HeisenbergGroup B` is the set `W × R` with the product
`(w, t) * (w', t') = (w + w', t + t' + ⅟2 * B w w')`.
When `B` is alternating this is the Heisenberg group of the symplectic module `(W, B)`; its
centre contains the elements `central t = (0, t)`, and `g * h = central (B g.vec h.vec) * (h * g)`.
An isometry of `(W, B)` acts by automorphisms fixing the centre (`mapEquiv`); the isometry group
`LinearMap.BilinForm.isometryGroup B` acts by `isometryAction B` (GKT (2.1)).

With topologies on `R` and `W` the group carries the topology induced from `W × R`
(`homeomorphProd`); it is a topological group when `B` is continuous
(`isTopologicalGroup`), and in particular for a finite module with its module topology over a
topological ring.
-/

namespace Langlands

universe u v

/-- The Heisenberg group of a bilinear form `B` on `W`: the set `W × R` with the product
`(w, t) * (w', t') = (w + w', t + t' + ⅟2 * B w w')` (the group structure needs
`Invertible (2 : R)`). -/
@[ext] structure HeisenbergGroup {R : Type u} {W : Type v} [CommRing R] [AddCommGroup W]
    [Module R W] (B : LinearMap.BilinForm R W) where
  /-- The coordinate in `W`. -/
  vec : W
  /-- The central coordinate. -/
  cen : R

namespace HeisenbergGroup

variable {R : Type u} [CommRing R] {W : Type v} [AddCommGroup W] [Module R W]
  {B : LinearMap.BilinForm R W}

/-- The unit `(0, 0)`. -/
instance : One (HeisenbergGroup B) := ⟨⟨0, 0⟩⟩

/-- The vector of the unit. -/
@[simp] theorem one_vec : (1 : HeisenbergGroup B).vec = 0 := rfl
/-- The central coordinate of the unit. -/
@[simp] theorem one_cen : (1 : HeisenbergGroup B).cen = 0 := rfl

/-- The central element `(0, t)`. -/
def central (t : R) : HeisenbergGroup B := ⟨0, t⟩

/-- The element `(w, 0)`. -/
def ofVec (w : W) : HeisenbergGroup B := ⟨w, 0⟩

/-- The vector of `central t`. -/
@[simp] theorem central_vec (t : R) : (central t : HeisenbergGroup B).vec = 0 := rfl
/-- The central coordinate of `central t`. -/
@[simp] theorem central_cen (t : R) : (central t : HeisenbergGroup B).cen = t := rfl
/-- The vector of `ofVec w`. -/
@[simp] theorem ofVec_vec (w : W) : (ofVec w : HeisenbergGroup B).vec = w := rfl
/-- The central coordinate of `ofVec w`. -/
@[simp] theorem ofVec_cen (w : W) : (ofVec w : HeisenbergGroup B).cen = 0 := rfl

/-- `central 0 = 1`. -/
@[simp] theorem central_zero : (central 0 : HeisenbergGroup B) = 1 := rfl

/-- `ofVec 0 = 1`. -/
@[simp] theorem ofVec_zero : (ofVec 0 : HeisenbergGroup B) = 1 := rfl

section TopologyBasic

variable [TopologicalSpace R] [TopologicalSpace W]

/-- The topology induced from `W × R`. -/
instance : TopologicalSpace (HeisenbergGroup B) :=
  TopologicalSpace.induced (fun g => (g.vec, g.cen)) inferInstance

/-- The Heisenberg group is homeomorphic to `W × R` by its coordinates. -/
def homeomorphProd : HeisenbergGroup B ≃ₜ W × R :=
  Equiv.toHomeomorphOfIsInducing
    { toFun := fun g => (g.vec, g.cen)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    ⟨rfl⟩

/-- The coordinates of `homeomorphProd`. -/
@[simp] theorem homeomorphProd_apply (g : HeisenbergGroup B) : homeomorphProd g = (g.vec, g.cen) :=
  rfl

/-- The vector coordinate is continuous. -/
theorem continuous_vec : Continuous (HeisenbergGroup.vec : HeisenbergGroup B → W) :=
  continuous_fst.comp homeomorphProd.continuous

/-- The central coordinate is continuous. -/
theorem continuous_cen : Continuous (HeisenbergGroup.cen : HeisenbergGroup B → R) :=
  continuous_snd.comp homeomorphProd.continuous

/-- A map into the Heisenberg group is continuous if its two coordinates are. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {f : X → W} {g : X → R}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (⟨f x, g x⟩ : HeisenbergGroup B) :=
  continuous_induced_rng.2 (hf.prodMk hg)

/-- `ofVec` is continuous. -/
theorem continuous_ofVec : Continuous (ofVec : W → HeisenbergGroup B) :=
  continuous_mk continuous_id continuous_const

/-- `central` is continuous. -/
theorem continuous_central : Continuous (central : R → HeisenbergGroup B) :=
  continuous_mk continuous_const continuous_id

end TopologyBasic

section Group

variable [Invertible (2 : R)]

/-- The product `(w, t)(w', t') = (w + w', t + t' + ½ B(w, w'))`. -/
instance : Mul (HeisenbergGroup B) := ⟨fun g h => ⟨g.vec + h.vec, g.cen + h.cen + ⅟2 * B g.vec h.vec⟩⟩
/-- The inverse `(w, t)⁻¹ = (-w, -t + ½ B(w, w))`. -/
instance : Inv (HeisenbergGroup B) := ⟨fun g => ⟨-g.vec, -g.cen + ⅟2 * B g.vec g.vec⟩⟩

/-- The vector of a product. -/
@[simp] theorem mul_vec (g h : HeisenbergGroup B) : (g * h).vec = g.vec + h.vec := rfl
/-- The central coordinate of a product: `t + t' + ½ B(w, w')`. -/
@[simp] theorem mul_cen (g h : HeisenbergGroup B) :
    (g * h).cen = g.cen + h.cen + ⅟2 * B g.vec h.vec := rfl
/-- The vector of an inverse. -/
@[simp] theorem inv_vec (g : HeisenbergGroup B) : g⁻¹.vec = -g.vec := rfl
/-- The central coordinate of an inverse. -/
@[simp] theorem inv_cen (g : HeisenbergGroup B) : g⁻¹.cen = -g.cen + ⅟2 * B g.vec g.vec := rfl

/-- The group structure. -/
instance : Group (HeisenbergGroup B) :=
  Group.ofLeftAxioms
    (fun a b c => by ext <;> simp [add_assoc]; ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp)

/-- `central` is a homomorphism from the additive group of `R`. -/
theorem central_add (s t : R) : (central (s + t) : HeisenbergGroup B) = central s * central t := by
  ext <;> simp

/-- The elements `central t` are central. -/
theorem central_mul_comm (t : R) (g : HeisenbergGroup B) : central t * g = g * central t := by
  ext <;> simp [add_comm]

/-- Every element is a central element times an element of `W`. -/
theorem central_mul_ofVec (g : HeisenbergGroup B) : central g.cen * ofVec g.vec = g := by
  ext <;> simp

/-- `(x, 0)(y, 0) = (0, ½ B(x, y)) (x + y, 0)`. -/
theorem ofVec_mul_ofVec (x y : W) :
    (ofVec x * ofVec y : HeisenbergGroup B) = central (⅟2 * B x y) * ofVec (x + y) := by
  ext <;> simp

/-- The commutation relation: `g h = (0, B g h) h g` when `B` is alternating. -/
theorem mul_eq_central_mul (hB : B.IsAlt) (g h : HeisenbergGroup B) :
    g * h = central (B g.vec h.vec) * (h * g) := by
  ext
  · simp [add_comm]
  · have h2 : (⅟2 : R) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
    simp only [mul_cen, central_cen, central_vec, mul_vec, map_zero, LinearMap.zero_apply,
      mul_zero, add_zero, ← hB.neg_eq g.vec h.vec]
    linear_combination (B g.vec h.vec) * h2

/-- Two elements `(x, 0)`, `(y, 0)` with `B x y ≠ 0` do not commute. -/
theorem not_commute_ofVec (hB : B.IsAlt) {x y : W} (hxy : B x y ≠ 0) :
    ¬ Commute (ofVec x : HeisenbergGroup B) (ofVec y) := by
  intro h
  have h' := mul_eq_central_mul hB (ofVec x : HeisenbergGroup B) (ofVec y)
  rw [h.eq, right_eq_mul] at h'
  exact hxy (congrArg HeisenbergGroup.cen h')

section MapEquiv

/-- An isometry of `(W, B)` acts on the Heisenberg group by `(w, t) ↦ (e w, t)`, fixing the
centre. -/
def mapEquiv (e : W ≃ₗ[R] W) (he : ∀ x y, B (e x) (e y) = B x y) :
    HeisenbergGroup B ≃* HeisenbergGroup B where
  toFun g := ⟨e g.vec, g.cen⟩
  invFun g := ⟨e.symm g.vec, g.cen⟩
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by ext <;> simp [he]

/-- The action of an isometry on coordinates. -/
@[simp] theorem mapEquiv_apply (e : W ≃ₗ[R] W) (he : ∀ x y, B (e x) (e y) = B x y)
    (g : HeisenbergGroup B) : mapEquiv e he g = ⟨e g.vec, g.cen⟩ := rfl

/-- Isometries fix the centre. -/
@[simp] theorem mapEquiv_central (e : W ≃ₗ[R] W) (he : ∀ x y, B (e x) (e y) = B x y) (t : R) :
    mapEquiv e he (central t) = central t := by
  ext <;> simp

/-- The action of an isometry on `ofVec w`. -/
@[simp] theorem mapEquiv_ofVec (e : W ≃ₗ[R] W) (he : ∀ x y, B (e x) (e y) = B x y) (w : W) :
    mapEquiv e he (ofVec w) = ofVec (e w) := rfl

/-- The identity acts trivially. -/
theorem mapEquiv_refl :
    mapEquiv (LinearEquiv.refl R W) (fun _ _ => rfl) = MulEquiv.refl (HeisenbergGroup B) := rfl

/-- The action is compatible with composition. -/
theorem mapEquiv_trans (e e' : W ≃ₗ[R] W) (he : ∀ x y, B (e x) (e y) = B x y)
    (he' : ∀ x y, B (e' x) (e' y) = B x y) :
    mapEquiv (e.trans e') (fun x y => by simp [he, he']) = (mapEquiv e he).trans (mapEquiv e' he') :=
  rfl

variable (B) in
/-- The isometry group of `B` acts on the Heisenberg group by `g · (w, t) = (g w, t)` (GKT (2.1),
p. 47); the action is trivial on the centre (`isometryAction_central`). -/
def isometryAction : LinearMap.BilinForm.isometryGroup B →* MulAut (HeisenbergGroup B) where
  toFun g := mapEquiv g.1 g.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The action of an isometry on coordinates. -/
@[simp] theorem isometryAction_apply (g : LinearMap.BilinForm.isometryGroup B)
    (h : HeisenbergGroup B) : isometryAction B g h = ⟨(g : W ≃ₗ[R] W) h.vec, h.cen⟩ := rfl

/-- Isometries act trivially on the centre. -/
@[simp] theorem isometryAction_central (g : LinearMap.BilinForm.isometryGroup B) (t : R) :
    isometryAction B g (central t) = central t := by
  ext <;> simp [central]

/-- The action of an isometry on `ofVec w`. -/
@[simp] theorem isometryAction_ofVec (g : LinearMap.BilinForm.isometryGroup B) (w : W) :
    isometryAction B g (ofVec w) = ofVec ((g : W ≃ₗ[R] W) w) := rfl

end MapEquiv

end Group

section Topology

variable [TopologicalSpace R] [TopologicalSpace W]

variable [Invertible (2 : R)]

/-- The Heisenberg group of a continuous bilinear form is a topological group. -/
theorem isTopologicalGroup [IsTopologicalRing R] [IsTopologicalAddGroup W]
    (hB : Continuous fun p : W × W => B p.1 p.2) : IsTopologicalGroup (HeisenbergGroup B) := by
  have h1 := (continuous_vec (B := B))
  have h2 := (continuous_cen (B := B))
  have h3 : Continuous fun _ : HeisenbergGroup B => (⅟2 : R) := continuous_const
  exact
    { continuous_mul := continuous_mk ((h1.comp continuous_fst).add (h1.comp continuous_snd))
        (((h2.comp continuous_fst).add (h2.comp continuous_snd)).add
          ((h3.comp continuous_fst).mul
            (hB.comp ((h1.comp continuous_fst).prodMk (h1.comp continuous_snd)))))
      continuous_inv := continuous_mk h1.neg (h2.neg.add (h3.mul (hB.comp (h1.prodMk h1)))) }

/-- Over a topological ring, the Heisenberg group of a finite module with its module topology
is a topological group. -/
instance [IsTopologicalRing R] [IsModuleTopology R W] [Module.Finite R W] :
    IsTopologicalGroup (HeisenbergGroup B) :=
  have := IsModuleTopology.isTopologicalAddGroup R W
  isTopologicalGroup (IsModuleTopology.continuous_bilinear_of_finite_left B)

end Topology

end HeisenbergGroup

end Langlands
