import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Relative derivations on schemes

The target is an actual sheaf of modules on the source scheme. The vanishing
condition is expressed on inverse images of opens of the base.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Langlands.Scheme

variable {X Y S : AlgebraicGeometry.Scheme.{u}}

/-- Relative derivations into a sheaf of modules on the source scheme. -/
abbrev RelativeDerivation (f : X ⟶ S) (M : X.Modules) : Type u :=
  PresheafOfModulesOfCommRing.Derivation M.val
    (F := Opens.map f.base) f.c

namespace RelativeDerivation

variable {f : X ⟶ S} {M N P : X.Modules}

/-- Evaluate a relative derivation on a local section. -/
def app (d : RelativeDerivation f M) (U : X.Opens) :
    Γ(X, U) →+ Γ(M, U) := d.d

@[simp]
lemma app_add (d : RelativeDerivation f M) (U : X.Opens) (a b : Γ(X, U)) :
    d.app U (a + b) = d.app U a + d.app U b :=
  map_add _ _ _

@[simp]
lemma app_mul (d : RelativeDerivation f M) (U : X.Opens) (a b : Γ(X, U)) :
    d.app U (a * b) = a • d.app U b + b • d.app U a :=
  d.d_mul a b

lemma app_restrict (d : RelativeDerivation f M) {U V : X.Opens}
    (i : U ⟶ V) (a : Γ(X, V)) :
    d.app U (X.presheaf.map i.op a) = M.presheaf.map i.op (d.app V a) :=
  d.d_map i.op a

@[simp]
lemma app_base (d : RelativeDerivation f M) (U : S.Opens) (a : Γ(S, U)) :
    d.app (f ⁻¹ᵁ U) (f.app U a) = 0 :=
  d.d_app a

/-- Vanishing also holds after restricting a pulled-back base section. -/
@[simp]
lemma app_base_restrict (d : RelativeDerivation f M)
    (U : S.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : Γ(S, U)) :
    d.app V (f.appLE U V h a) = 0 := by
  change d.app V (X.presheaf.map (homOfLE h).op (f.app U a)) = 0
  rw [app_restrict, app_base, map_zero]

/-- Postcompose a relative derivation with a morphism of sheaves of modules. -/
def postcomp (d : RelativeDerivation f M) (α : M ⟶ N) :
    RelativeDerivation f N :=
  PresheafOfModulesOfCommRing.Derivation.postcomp d α.val

@[simp]
lemma postcomp_app (d : RelativeDerivation f M) (α : M ⟶ N)
    (U : X.Opens) (a : Γ(X, U)) :
    (postcomp d α).app U a = α.app U (d.app U a) := rfl

@[simp]
lemma postcomp_id (d : RelativeDerivation f M) :
    postcomp d (𝟙 M) = d := by
  ext U a
  rfl

@[simp]
lemma postcomp_comp (d : RelativeDerivation f M) (α : M ⟶ N) (β : N ⟶ P) :
    postcomp d (α ≫ β) = postcomp (postcomp d α) β := by
  ext U a
  rfl

end RelativeDerivation

/-- The set-valued relative derivation functor on actual sheaves of modules. -/
def relativeDerivationFunctor (f : X ⟶ S) : X.Modules ⥤ Type u where
  obj M := RelativeDerivation f M
  map α := ↾fun d => RelativeDerivation.postcomp d α
  map_id M := by
    apply ConcreteCategory.hom_ext
    intro d
    exact RelativeDerivation.postcomp_id d
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro d
    exact RelativeDerivation.postcomp_comp d α β

end Langlands.Scheme
