import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Pullback on the Ext-defined cohomology of abelian sheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace Langlands.Cohomology.AbelianSheafCohomologyPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  let : ReflectsLimits (forget AddCommGrpCat.{u}) := reflectsLimits_of_reflectsIsomorphisms
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance pullback_additive : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Inverse image carries the constant integer sheaf to the constant integer sheaf. -/
def constantPullbackIso :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
        constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens Y))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X)))

/-- The canonical pullback in sheaf cohomology, allowing a map of coefficients
from the inverse image of the source sheaf. -/
def pullbackMap {A : Y.Sheaf AddCommGrpCat.{u}} {B : X.Sheaf AddCommGrpCat.{u}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj A ⟶ B) (n : ℕ) :
    Sheaf.H.{u} A n →+ Sheaf.H.{u} B n where
  toFun x := (Ext.mk₀ ((constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift ℤ)))).comp
    ((x.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).comp
      (Ext.mk₀ a) (add_zero n)) (zero_add n)
  map_zero' := by simp
  map_add' := by intros; simp

/-- Equivalent coefficient convention, specified by a map into direct image. -/
def pushforwardMap {A : Y.Sheaf AddCommGrpCat.{u}} {B : X.Sheaf AddCommGrpCat.{u}}
    (a : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (n : ℕ) :
    Sheaf.H.{u} A n →+ Sheaf.H.{u} B n :=
  pullbackMap f
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).symm a) n

/-- Covariance in the target coefficient sheaf. -/
lemma pullbackMap_naturality_right {A : Y.Sheaf AddCommGrpCat.{u}}
    {B C : X.Sheaf AddCommGrpCat.{u}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj A ⟶ B)
    (b : B ⟶ C) (n : ℕ) (x : Sheaf.H.{u} A n) :
    pullbackMap f (a ≫ b) n x = Sheaf.H.map b n (pullbackMap f a n x) := by
  simp only [pullbackMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sheaf.H.map_apply,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- Naturality in the source coefficient sheaf. -/
lemma pullbackMap_naturality_left {A A' : Y.Sheaf AddCommGrpCat.{u}}
    {B : X.Sheaf AddCommGrpCat.{u}} (a : A ⟶ A')
    (b : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj A' ⟶ B)
    (n : ℕ) (x : Sheaf.H.{u} A n) :
    pullbackMap f b n (Sheaf.H.map a n x) =
      pullbackMap f ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a ≫ b) n x := by
  simp only [pullbackMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- Pullback commutes with connecting homomorphisms for a map from the
inverse image of a short exact sequence to another short exact sequence. -/
lemma pullbackMap_δ {S : ShortComplex (Y.Sheaf AddCommGrpCat.{u})}
    {T : ShortComplex (X.Sheaf AddCommGrpCat.{u})} (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S.map (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) ⟶ T)
    (n m : ℕ) (h : n + 1 = m) (x : Sheaf.H.{u} S.X₃ n) :
    pullbackMap f a.τ₁ m (Sheaf.H.δ hS n m h x) =
      Sheaf.H.δ hT n m h (pullbackMap f a.τ₃ n x) := by
  change (Ext.mk₀ _).comp
      (((x.comp hS.extClass h).mapExactFunctor
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).comp (Ext.mk₀ a.τ₁) (add_zero m))
      (zero_add m) =
    ((Ext.mk₀ _).comp
      ((x.mapExactFunctor (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).comp
        (Ext.mk₀ a.τ₃) (add_zero n)) (zero_add n)).comp hT.extClass h
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_naturality
      (hS.map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)) hT a,
    ← Ext.comp_assoc_of_second_deg_zero]
  symm
  apply Ext.comp_assoc
  lia

end Langlands.Cohomology.AbelianSheafCohomologyPullback
