import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Algebra structure on canonical global-functions base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules

namespace GlobalFunctionsAlgebra

/-- The algebra structure on actual global functions supplied by the
structure morphism. -/
abbrev algebra {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :
    Algebra R Γ(X, ⊤) :=
  (structureRingHom f).hom.toAlgebra

variable {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S) (g : Y ⟶ X)
  (w : g ≫ f = f' ≫ Spec.map φ)

include w in
/-- The actual pullback of functions commutes with the structure maps in
the Cartesian diagram; this identity only needs the commuting square. -/
lemma structureRingHom_naturality :
    structureRingHom f ≫ g.appTop = φ ≫ structureRingHom f' := by
  calc
    structureRingHom f ≫ g.appTop = structureRingHom (g ≫ f) := by
      simp [structureRingHom]
    _ = φ ≫ structureRingHom f' := structureRingHom_eq_comp φ (g ≫ f) f' w

/-- The canonical algebra map on actual global functions for a commuting
base-change square. -/
def baseChangeMap :
    letI := φ.hom.toAlgebra
    letI := algebra f
    letI := algebra f'
    S ⊗[R] Γ(X, ⊤) →ₐ[S] Γ(Y, ⊤) := by
  letI := φ.hom.toAlgebra
  letI := algebra f
  letI := algebra f'
  letI : Algebra R Γ(Y, ⊤) := ((structureRingHom f').hom.comp φ.hom).toAlgebra
  have : IsScalarTower R S Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : Γ(X, ⊤) →ₐ[R] Γ(Y, ⊤) :=
    { toRingHom := g.appTop.hom
      commutes' := fun r =>
        congrArg (fun a : R ⟶ Γ(Y, ⊤) => a.hom r)
          (structureRingHom_naturality φ f f' g w) }
  exact AlgHom.liftEquiv R S Γ(X, ⊤) Γ(Y, ⊤) ψ

/-- The canonical algebra map sends a pure tensor to the product of the
structure-map image and the actual pullback of the function. -/
lemma baseChangeMap_tmul (s : S) (x : Γ(X, ⊤)) :
    letI := φ.hom.toAlgebra
    letI := algebra f
    letI := algebra f'
    baseChangeMap φ f f' g w (s ⊗ₜ[R] x) =
      (structureRingHom f').hom s * g.appTop x := rfl

end GlobalFunctionsAlgebra

namespace FieldGlobalFunctions

lemma pullbackUnitIso_unit {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward g).map
        (Langlands.Scheme.Modules.pullbackUnitIso g).hom =
      Langlands.Scheme.Modules.unitToPushforwardUnit g := by
  have : (TopologicalSpace.Opens.map g.base).Final := inferInstance
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint
  simpa only [Scheme.Modules.pullbackPushforwardAdjunction,
      Scheme.Modules.pushforward, Langlands.Scheme.Modules.pullbackUnitIso,
      Langlands.Scheme.Modules.unitToPushforwardUnit, asIso_hom,
      Adjunction.homEquiv_unit] using
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      g.toRingCatSheafHom)

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {Y : Scheme.{u}} {S : CommRingCat.{u}}
  (φ : CommRingCat.of k ⟶ S) (f' : Y ⟶ Spec S) (g : Y ⟶ X)
  (h : IsPullback g f' f (Spec.map φ))

lemma baseChangeIso_hom_one_tmul (x : sections f) :
    (baseChangeIso f φ f' g h).hom ((1 : S) ⊗ₜ[k,φ.hom] x) =
      g.appTop x := by
  rw [baseChangeIso_hom]
  change (Langlands.Scheme.Modules.pullbackUnitIso g).hom.app ⊤
      (scalarSectionsBaseChangeMap φ f f' g h.w
        (SheafOfModules.unit X.ringCatSheaf) ((1 : S) ⊗ₜ[k,φ.hom] x)) = _
  rw [scalarSectionsBaseChangeMap_one_tmul]
  exact congrArg (fun a => a.app ⊤ x) (pullbackUnitIso_unit g)

/-- The canonical module comparison agrees on every pure tensor with
multiplication by the base scalar after actual pullback. -/
lemma baseChangeIso_hom_tmul (s : S) (x : sections f) :
    (baseChangeIso f φ f' g h).hom (s ⊗ₜ[k,φ.hom] x) =
      (structureRingHom f').hom s * g.appTop x := by
  have ht : s ⊗ₜ[k,φ.hom] x =
      s • ((1 : S) ⊗ₜ[k,φ.hom] x :
        (ModuleCat.extendScalars φ.hom).obj (sections f)) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ht, map_smul, baseChangeIso_hom_one_tmul]
  rfl

/-- The actual global-functions algebra of a proper field scheme is finite. -/
lemma finite_algebra :
    letI := GlobalFunctionsAlgebra.algebra f
    Module.Finite k Γ(X, ⊤) := by
  let := GlobalFunctionsAlgebra.algebra f
  exact finite f

/-- The canonical module comparison in the ordinary algebra tensor-product
convention. -/
def baseChangeAlgebraLinearEquiv :
    letI := φ.hom.toAlgebra
    letI := GlobalFunctionsAlgebra.algebra f
    letI := GlobalFunctionsAlgebra.algebra f'
    S ⊗[k] Γ(X, ⊤) ≃ₗ[S] Γ(Y, ⊤) := by
  letI := φ.hom.toAlgebra
  letI := GlobalFunctionsAlgebra.algebra f
  letI := GlobalFunctionsAlgebra.algebra f'
  exact (Langlands.Scheme.Modules.extendScalarsAlgebraEquiv
    (CommRingCat.of k) S (sections f)).symm.trans
      (baseChangeIso f φ f' g h).toLinearEquiv

lemma baseChangeAlgebraLinearEquiv_tmul (s : S) (x : Γ(X, ⊤)) :
    letI := φ.hom.toAlgebra
    letI := GlobalFunctionsAlgebra.algebra f
    letI := GlobalFunctionsAlgebra.algebra f'
    baseChangeAlgebraLinearEquiv f φ f' g h (s ⊗ₜ[k] x) =
      (structureRingHom f').hom s * g.appTop x := by
  exact baseChangeIso_hom_tmul f φ f' g h s x

/-- The canonical algebra map is exactly the canonical module comparison. -/
lemma baseChangeMap_toLinearMap :
    letI := φ.hom.toAlgebra
    letI := GlobalFunctionsAlgebra.algebra f
    letI := GlobalFunctionsAlgebra.algebra f'
    (GlobalFunctionsAlgebra.baseChangeMap φ f f' g h.w).toLinearMap =
      (baseChangeAlgebraLinearEquiv f φ f' g h).toLinearMap := by
  let := φ.hom.toAlgebra
  let := GlobalFunctionsAlgebra.algebra f
  let := GlobalFunctionsAlgebra.algebra f'
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    exact (GlobalFunctionsAlgebra.baseChangeMap_tmul φ f f' g h.w s x).trans
      (baseChangeAlgebraLinearEquiv_tmul f φ f' g h s x).symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Canonical affine base change of the actual global-functions algebra
for a proper scheme over an arbitrary field. -/
def baseChangeAlgebraEquiv :
    letI := φ.hom.toAlgebra
    letI := GlobalFunctionsAlgebra.algebra f
    letI := GlobalFunctionsAlgebra.algebra f'
    S ⊗[k] Γ(X, ⊤) ≃ₐ[S] Γ(Y, ⊤) := by
  letI := φ.hom.toAlgebra
  letI := GlobalFunctionsAlgebra.algebra f
  letI := GlobalFunctionsAlgebra.algebra f'
  apply AlgEquiv.ofBijective (GlobalFunctionsAlgebra.baseChangeMap φ f f' g h.w)
  change Function.Bijective
    (GlobalFunctionsAlgebra.baseChangeMap φ f f' g h.w).toLinearMap
  rw [baseChangeMap_toLinearMap f φ f' g h]
  exact (baseChangeAlgebraLinearEquiv f φ f' g h).bijective

lemma baseChangeAlgebraEquiv_tmul (s : S) (x : Γ(X, ⊤)) :
    letI := φ.hom.toAlgebra
    letI := GlobalFunctionsAlgebra.algebra f
    letI := GlobalFunctionsAlgebra.algebra f'
    baseChangeAlgebraEquiv f φ f' g h (s ⊗ₜ[k] x) =
      (structureRingHom f').hom s * g.appTop x :=
  GlobalFunctionsAlgebra.baseChangeMap_tmul φ f f' g h.w s x

end FieldGlobalFunctions

end Langlands.AlgebraicGeometry.Modules
