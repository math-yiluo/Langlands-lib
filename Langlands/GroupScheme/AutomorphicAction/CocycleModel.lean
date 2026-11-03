import Langlands.GroupScheme.AutomorphicAction.Cocycles
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Represented conjugation-stable subfunctors of actual cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S} (a : AutomorphicAction H G)

/-- A represented subfunctor of actual cocycles, stable under conjugation and
containing the trivial cocycle. No existence or geometric property is asserted. -/
structure CocycleModel where
  scheme : Over S
  universal : a.Cocycle scheme
  injective : ∀ (T : Over S), Function.Injective
    (fun (x : T ⟶ scheme) => Cocycle.restrict x universal)
  action : SchemeAction G scheme
  equivariant : ∀ {T : Over S} (g : T ⟶ G.X) (x : T ⟶ scheme),
    Cocycle.restrict (action.act g x) universal =
      Cocycle.conjugate g (Cocycle.restrict x universal)
  basepoint : 𝟙_ (Over S) ⟶ scheme
  basepoint_trivial : Cocycle.restrict basepoint universal =
    Cocycle.trivial (𝟙_ (Over S))

namespace CocycleModel

variable {a} (M : a.CocycleModel)

/-- The actual cocycle parametrized by a test point of the model. -/
def cocycle {T : Over S} (x : T ⟶ M.scheme) : a.Cocycle T :=
  Cocycle.restrict x M.universal

theorem cocycle_injective (T : Over S) :
    Function.Injective (M.cocycle (T := T)) :=
  M.injective T

theorem restrict_cocycle {T T' : Over S} (b : T' ⟶ T) (x : T ⟶ M.scheme) :
    Cocycle.restrict b (M.cocycle x) = M.cocycle (b ≫ x) :=
  (Cocycle.restrict_comp x b M.universal).symm

/-- The all-test inclusion of the represented subfunctor into actual cocycles. -/
def inclusion : yoneda.obj M.scheme ⟶ a.cocycleFunctor where
  app T := ↾fun x => M.cocycle x
  naturality {T T'} b := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (M.restrict_cocycle b.unop x).symm

@[simp]
theorem cocycle_basepoint :
    M.cocycle M.basepoint = Cocycle.trivial (𝟙_ (Over S)) :=
  M.basepoint_trivial

@[simp]
theorem cocycle_basepoint_comp (T : Over S) :
    M.cocycle (toUnit T ≫ M.basepoint) = Cocycle.trivial T := by
  rw [← M.restrict_cocycle, M.cocycle_basepoint, Cocycle.restrict_trivial]

/-- The actual conjugation orbit map of the chosen trivial cocycle. -/
def orbit : G.X ⟶ M.scheme :=
  M.action.act (𝟙 G.X) (toUnit G.X ≫ M.basepoint)

/-- The action relation map `(g,x) ↦ (g • x,x)`. -/
def actionRelation : G.X ⊗ M.scheme ⟶ M.scheme ⊗ M.scheme :=
  lift M.action.hom (snd G.X M.scheme)

theorem cocycle_act {T : Over S} (g : T ⟶ G.X) (x : T ⟶ M.scheme) :
    M.cocycle (M.action.act g x) = Cocycle.conjugate g (M.cocycle x) :=
  M.equivariant g x

@[simp]
theorem comp_orbit {T : Over S} (g : T ⟶ G.X) :
    g ≫ M.orbit = M.action.act g (toUnit T ≫ M.basepoint) := by
  rw [orbit, M.action.naturality, Category.comp_id, comp_toUnit_assoc]

/-- The model's orbit map has exactly the canonical coboundary as cocycle. -/
@[simp]
theorem cocycle_comp_orbit {T : Over S} (g : T ⟶ G.X) :
    M.cocycle (g ≫ M.orbit) = a.coboundary g := by
  rw [M.comp_orbit, M.cocycle_act, M.cocycle_basepoint_comp]
  rfl

/-- The exact right-coset fiber equation on every test scheme follows from the
model's all-test injection and the actual cocycle fiber equation. -/
theorem orbit_fibers (T : Over S) (g g' : T ⟶ G.X) :
    g ≫ M.orbit = g' ≫ M.orbit ↔
      g⁻¹ * g' ∈ a.fixedSubgroup.carrier T := by
  rw [← M.cocycle_injective T |>.eq_iff]
  rw [M.cocycle_comp_orbit, M.cocycle_comp_orbit, a.coboundary_eq_iff]

/-- An affine model already provides a separated ambient scheme for the
published homogeneous quotient construction. Its affineness is not asserted. -/
def homogeneousQuotient
    {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    {a : AutomorphicAction H G}
    (M : a.CocycleModel)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom M.scheme.hom]
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hcl : IsClosedSubgroup j) (hsm : Smooth C.X.hom)
    (hrep : a.fixedSubgroup.IsRepresentedBy j) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j :=
  HomogeneousQuotientFromEmbedding.quotientOfMapKernel j hcl hsm M.scheme M.orbit
    (by
      intro T g g'
      rw [hrep.2]
      exact M.orbit_fibers T g g')

end CocycleModel

end Langlands.GroupScheme.AutomorphicAction
