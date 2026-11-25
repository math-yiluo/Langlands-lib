/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Linear

/-! # Scalar multiplication on a sheafified complex over a basic open

Source: Stacks Project, Tag 01HR (standard opens of an affine scheme),
and Tag 09IR (restriction of the Koszul complex).
(blueprint: lem-k3-basic-open-tilde-scalar-iso).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private lemma scalar_app (A : Type u) [CommRing A] (a : A) (M : ModuleCat.{u} A)
    (U : (Spec (.of A)).Opens)
    (x : ((modulesSpecToSheaf (R := .of A)).obj (tilde M)).obj.obj (.op U)) :
    (tilde.map (a • 𝟙 M)).val.app (.op U) x = a • x := by
  apply Subtype.ext
  funext y
  change IsLocalizedModule.map y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap (R := A) y.1.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap (R := A) y.1.asIdeal.primeCompl M)
    (a • (LinearMap.id : M →ₗ[A] M)) (x.val y) = _
  rw [map_smul, IsLocalizedModule.map_id]
  exact congrArg (fun z : (structureSheafInType A M).obj.obj (.op U) ↦ z.val y)
    (IsScalarTower.algebraMap_smul
      (M := (structureSheafInType A M).obj.obj (.op U))
      ((structureSheafInType A A).obj.obj (.op U)) a x).symm

set_option backward.isDefEq.respectTransparency false in
private lemma restricted_scalar_isIso (A : Type u) [CommRing A] (a : A)
    (M : ModuleCat.{u} A) :
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (PrimeSpectrum.basicOpen a)).map
        (tilde.map (a • 𝟙 M))) := by
  let f := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (PrimeSpectrum.basicOpen a)).map
      (tilde.map (a • 𝟙 M))
  have happ (U) : IsIso (f.val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let : Module A Γ(tilde (R := .of A) M, U.unop.left) :=
      inferInstanceAs (Module A
        (((modulesSpecToSheaf (R := .of A)).obj (tilde M)).obj.obj (.op U.unop.left)))
    have h := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
      (R := .of A) (M := tilde (R := .of A) M) a U.unop.hom.le
    rw [Module.End.isUnit_iff] at h
    change Function.Bijective (fun x ↦
      (tilde.map (a • 𝟙 M)).val.app (.op U.unop.left) x)
    change Function.Bijective (fun x :
      ((modulesSpecToSheaf (R := .of A)).obj (tilde M)).obj.obj (.op U.unop.left) ↦ a • x)
      at h
    convert h using 1 <;> first | rfl | (funext x; exact scalar_app A a M U.unop.left x)
  have : ∀ U, IsIso (f.val.app U) := happ
  let e := PresheafOfModules.isoMk (fun U ↦ asIso (f.val.app U))
    (fun {_ _} g ↦ f.val.naturality g)
  have he : e.hom = f.val := by ext U; rfl
  have : IsIso f.val := he ▸ e.isIso_hom
  have : IsIso ((SheafOfModules.forget _).map f) := ‹IsIso f.val›
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/-- Multiplication by a on any sheafified complex is invertible over D(a).
Source: Stacks Project, Tag 01HR, and the local vanishing argument of Tag 09IR.
(blueprint: lem-k3-basic-open-tilde-scalar-iso).

Proof: On D(a), the image of a is a unit in the structure sheaf. Its inverse
restricts compatibly to every smaller open. In each degree, multiply sections
by that inverse; these linear maps respect restriction, hence give morphisms
of module sheaves. Under tilde, the image of a times the identity is precisely
multiplication by the structure-sheaf section a, by the localization formula
for tilde.map. Both composites are the identity, sectionwise. The inverse
maps commute with the differentials, since the latter are linear over the
structure sheaf. They therefore give the inverse chain map. This argument
applies to arbitrary complexes, without exactness or finite-generation
hypotheses. If D(a) is empty, all module sheaves on it are zero and the
same assertion holds, including a=0 and the zero ring. -/
theorem basicOpen_tilde_scalar_isIso
    (A : Type u) [CommRing A] (a : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso
      (((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace)
        (PrimeSpectrum.basicOpen a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).map
          (a • 𝟙 K))) := by
  let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace)
    (PrimeSpectrum.basicOpen a)).mapHomologicalComplex (ComplexShape.up ℤ)
  have (i : ℤ) : IsIso ((R.map (T.map (a • 𝟙 K))).f i) := by
    change IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (PrimeSpectrum.basicOpen a)).map
        (tilde.map (a • 𝟙 (K.X i))))
    exact restricted_scalar_isIso A a (K.X i)
  exact HomologicalComplex.Hom.isIso_of_components (R.map (T.map (a • 𝟙 K)))

end

end AlgebraicGeometry
