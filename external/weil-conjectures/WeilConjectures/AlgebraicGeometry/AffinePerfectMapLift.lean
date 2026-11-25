/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof
import WeilConjectures.AlgebraicGeometry.PerfectDerivedTensor
import WeilConjectures.AlgebraicGeometry.DerivedTensorStalkVanishing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Affine lifting of maps from perfect complexes

Source: Stacks Project, Tag 08EH, Lemma 36.13.7
(blueprint: lem-sc-affine-perfect-map-lift).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A map from the restriction of a perfect object of an affine scheme to a quasi-compact
open lifts on the whole scheme after a perfect tensor augmentation that is invertible on
the open. Restriction to `U` is first to the localized site and then transported by the
canonical equivalence with the open's site, so `α` is a map in `D(𝒪_U)`. The lifted
object keeps every closed support of the original object, support meaning that every
cohomology sheaf has zero stalks off the closed set.
Source: Stacks Project, Tag 08EH, Lemma 36.13.7
(blueprint: lem-sc-affine-perfect-map-lift).

Proof:
1. The perfect-source RHom of A into E' has quasi-coherent cohomology, with no
   boundedness assumption on E' (lem-sc-rhom-supported-qcoherent). Restriction of
   RHom to U (lem-sc-derived-internal-hom-restrict-open) and the global-sections
   identification (lem-pur-rhom-global-sections) turn alpha into a degree-zero section.
2. Cover U by finitely many principal opens. Apply
   lem-sc-affine-perfect-open-represent-cohomology to this RHom object: a perfect
   Koszul augmentation I to O_X, invertible on U, represents the section.
3. Set A' = A tensor-derived I. It is perfect by lem-sc-perfect-derived-tensor-perfect.
   The tensor-Hom adjunction (lem-sc-affine-perfect-derived-tensor-hom) gives gamma.
   Tensor the augmentation with id_A to obtain beta. Restriction commutes with tensor
   and RHom (lem-sc-derived-internal-hom-restrict-open). Naturality of the adjunction
   identifies gamma restricted to U, composed with the inverse of beta, with alpha.
4. At a point outside a closed support T of A, every cohomology stalk of A is zero, so
   A is zero near that point. Tensoring with I keeps it zero, so A' is supported on T.
-/
theorem exists_perfect_map_lift_of_isAffine
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj) :
    ∃ (A' I : schemeDerivedCategory X) (β : A' ⟶ A) (γ : A' ⟶ E'.obj),
      IsPerfect X A' ∧ IsPerfect X I ∧ IsDerivedTensorAugmentation X A I A' β ∧
      (∃ bU : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj A' ≅
          ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj A,
        bU.hom = ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.map β ∧
        α = bU.inv ≫ ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.map γ) ∧
      ∀ T : Set X, IsClosed T →
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj A).val.presheaf x))) →
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj A').val.presheaf x)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let G := (DerivedCategory.Q (C := C)).objPreimage A
  obtain ⟨P, q, hP, _hflat, hq, _hepi⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) G
  let : QuasiIso q := hq
  let eA : DerivedCategory.Q.obj P ≅ A :=
    asIso (DerivedCategory.Q.map q) ≪≫ (DerivedCategory.Q (C := C)).objObjPreimageIso A
  obtain ⟨J, hJ, hI, u, γ, bU, hβ, hγ⟩ :=
    exists_affine_perfect_tensor_roof X U hU E' A hA α P hP eA
  let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J
    (MonoidalCategory.curriedTensor _))
  let β : B ⟶ A := DerivedCategory.Q.map
    (HomologicalComplex.mapBifunctorMap (𝟙 P) u (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)) ≫
    DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
  refine ⟨B, DerivedCategory.Q.obj J, β, γ, ?_, hI, ?_, ⟨bU, hβ, hγ⟩, ?_⟩
  · exact perfect_derivedTensor X A (DerivedCategory.Q.obj J) hA hI P J hP hJ
      eA (Iso.refl _)
  · refine ⟨P, J, hP, hJ, eA, Iso.refl _, Iso.refl _, u, ?_⟩
    change β = 𝟙 B ≫ β
    exact (Category.id_comp β).symm
  · intro T _hT hT n x hx
    exact derived_tensor_stalk_vanishing X A P J eA hJ x (fun m ↦ hT m x hx) n

end AlgebraicGeometry.Scheme
