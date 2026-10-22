import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Galois.Action
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The predicate on objects of the slice defining finite étale covers. -/
def coverProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun Y => IsFinite Y.hom ∧ Etale Y.hom

/-- The full category of finite étale schemes over `S`. -/
abbrev Cover (S : Scheme.{u}) := (coverProperty S).FullSubcategory

/-- The fully faithful inclusion into schemes over the base. -/
abbrev inclusion (S : Scheme.{u}) : Cover S ⥤ Over S := (coverProperty S).ι

/-- Regard a finite étale morphism as a cover. -/
def cover {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f] [Etale f] : Cover S :=
  ⟨Over.mk f, ‹IsFinite f›, ‹Etale f›⟩

instance {S : Scheme.{u}} (Y : Cover S) : IsFinite Y.obj.hom := Y.property.1
instance {S : Scheme.{u}} (Y : Cover S) : Etale Y.obj.hom := Y.property.2

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- Actual geometric lifts of `s` into a finite étale cover. Algebraic closure is
not needed to define this set. -/
abbrev Fiber (Y : Cover S) := (Over.mk s ⟶ Y.obj)

/-- The geometric point functor, with morphisms acting by postcomposition. -/
def pointFunctor : Cover S ⥤ Type u :=
  inclusion S ⋙ coyoneda.obj (op (Over.mk s))

@[simp]
theorem pointFunctor_obj (Y : Cover S) : (pointFunctor s).obj Y = Fiber s Y := rfl

@[simp]
theorem pointFunctor_map {Y Z : Cover S} (f : Y ⟶ Z) (x : Fiber s Y) :
    (pointFunctor s).map f x = x ≫ f.hom := rfl

/-- The scheme-theoretic fibre of a cover over `s`. -/
def fiberScheme (Y : Cover S) : Scheme.{u} := pullback Y.obj.hom s

/-- Ω-points of the fibre as morphisms over `Spec Ω`; the structural morphism
of the source is its identity. -/
abbrev FiberPoints (Y : Cover S) :=
  (Over.mk (𝟙 (Spec (.of Ω))) ⟶ Over.mk (pullback.snd Y.obj.hom s))

/-- The universal property of the pullback identifies geometric lifts and
Ω-points of the scheme-theoretic fibre. -/
def fiberEquivPoints (Y : Cover S) : Fiber s Y ≃ FiberPoints s Y where
  toFun x := Over.homMk (pullback.lift x.left (𝟙 _) (by simp)) (by simp)
  invFun x := Over.homMk (x.left ≫ pullback.fst _ _) (by
    have hx : x.left ≫ pullback.snd Y.obj.hom s = 𝟙 _ := Over.w x
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
    simp)
  left_inv x := by
    apply Over.OverMorphism.ext
    simp
  right_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w x).symm

@[simp]
theorem fiberEquivPoints_fst (Y : Cover S) (x : Fiber s Y) :
    (fiberEquivPoints s Y x).left ≫ pullback.fst _ _ = x.left := by
  simp [fiberEquivPoints]

/-- Explicitly retain the pending geometric finiteness obligation as a hypothesis.
This functor has the same point sets and maps as `pointFunctor`. -/
def fiberFunctor (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Cover S ⥤ FintypeCat.{u} :=
  ObjectProperty.lift _ (pointFunctor s) hfin

@[simp]
theorem fiberFunctor_comp_incl (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    fiberFunctor s hfin ⋙ FintypeCat.incl = pointFunctor s := rfl

/-- The automorphism group of the actual finite geometric point functor.
The finiteness proof is an explicit parameter, not a Galois-category assumption. -/
abbrev FundamentalGroup (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :=
  Aut (fiberFunctor s hfin)

/-- Forgetting finite-set packaging identifies this group with automorphisms
of the original, type-valued geometric point functor. -/
def fundamentalGroupEquiv (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    FundamentalGroup s hfin ≃* Aut (pointFunctor s) :=
  ((ObjectProperty.fullyFaithfulι (C := Type u) Finite).whiskeringRight
    (Cover S)).autMulEquivOfFullyFaithful (fiberFunctor s hfin)

variable (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

/-- Evaluation on a cover as a group homomorphism. -/
def evaluation (Y : Cover S) : FundamentalGroup s hfin →* Aut ((fiberFunctor s hfin).obj Y) :=
  ((CategoryTheory.evaluation _ _).obj Y).mapAut (fiberFunctor s hfin)

/-- The intrinsic action on the actual geometric fibre. -/
instance fiberMulAction (Y : Cover S) : MulAction (FundamentalGroup s hfin) (Fiber s Y) :=
  inferInstanceAs (MulAction (Aut (fiberFunctor s hfin)) ((fiberFunctor s hfin).obj Y))

@[simp]
theorem smul_eq (Y : Cover S) (g : FundamentalGroup s hfin) (x : Fiber s Y) :
    g • x = g.hom.app Y x := rfl

/-- Every map of covers intertwines the evaluation actions. -/
theorem smul_naturality {Y Z : Cover S} (f : Y ⟶ Z)
    (g : FundamentalGroup s hfin) (x : Fiber s Y) :
    g • (x ≫ f.hom) = (g • x) ≫ f.hom :=
  PreGaloisCategory.mulAction_naturality (fiberFunctor s hfin) g f x

/-- The finite action functor uses the actual geometric fibres. -/
def actionFunctor : Cover S ⥤ Action FintypeCat.{u} (FundamentalGroup s hfin) :=
  PreGaloisCategory.functorToAction (fiberFunctor s hfin)

@[simp]
theorem actionFunctor_comp_forget :
    actionFunctor s hfin ⋙ forget₂ _ FintypeCat = fiberFunctor s hfin := rfl

open scoped PreGaloisCategory

/-- Discrete topology on each actual geometric fibre. -/
instance fiberTopology (Y : Cover S) : TopologicalSpace (Fiber s Y) := ⊥

instance fiberDiscreteTopology (Y : Cover S) : DiscreteTopology (Fiber s Y) := ⟨rfl⟩

/-- Mathlib's topology is induced by simultaneous evaluation on all finite fibres;
each finite fibre automorphism group carries the discrete topology. -/
theorem fundamentalGroup_topology :
    (inferInstance : TopologicalSpace (FundamentalGroup s hfin)) =
      TopologicalSpace.induced (PreGaloisCategory.autEmbedding (fiberFunctor s hfin))
        inferInstance := rfl

/-- Continuous evaluation action, without any Galois-category hypothesis. -/
instance fiberContinuousSMul (Y : Cover S) :
    ContinuousSMul (FundamentalGroup s hfin) (Fiber s Y) :=
  PreGaloisCategory.continuousSMul_aut_fiber (fiberFunctor s hfin) Y

/-- Evaluation at a single geometric point is continuous. -/
theorem continuous_evaluation (Y : Cover S) (x : Fiber s Y) :
    Continuous (fun g : FundamentalGroup s hfin => g • x) :=
  continuous_id.smul continuous_const

open scoped FintypeCatDiscrete

/-- The actual finite fibres, equipped with their continuous evaluation actions.
This construction does not assert that the functor is an equivalence. -/
def continuousActionFunctor :
    Cover S ⥤ ContAction FintypeCat.{u} (FundamentalGroup s hfin) :=
  ObjectProperty.lift _ (actionFunctor s hfin)
    (fun Y => PreGaloisCategory.continuousSMul_aut_fiber (fiberFunctor s hfin) Y)

@[simp]
theorem continuousActionFunctor_comp_inclusion :
    continuousActionFunctor s hfin ⋙
      (Action.isContinuous FintypeCat.{u} (FundamentalGroup s hfin)).ι =
        actionFunctor s hfin := rfl

/-- Conditional compactness follows from Mathlib's closed-subgroup construction. -/
theorem fundamentalGroup_compact : CompactSpace (FundamentalGroup s hfin) := inferInstance

/-- The evaluation topology is Hausdorff. -/
theorem fundamentalGroup_t2 : T2Space (FundamentalGroup s hfin) := inferInstance

/-- The evaluation topology is totally disconnected. -/
theorem fundamentalGroup_totallyDisconnected :
    TotallyDisconnectedSpace (FundamentalGroup s hfin) := inferInstance

/-- Multiplication and inversion are continuous. -/
theorem fundamentalGroup_isTopologicalGroup :
    IsTopologicalGroup (FundamentalGroup s hfin) := inferInstance

end Langlands.AlgebraicGeometry.FiniteEtale
