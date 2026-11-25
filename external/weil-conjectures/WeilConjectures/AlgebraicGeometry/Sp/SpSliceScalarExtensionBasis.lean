/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sp.SpEllCoefficientTower

import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.SiteModuleSliceSheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Abelian

/-! # Scalar extension preserves a basis on a prescribed slice -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct ChangeOfRings
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

private theorem internalSectionExtensionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) :
    Nonempty ((sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S).functor.obj
        ((Mod.extendScalars a).obj L) ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) a)
        ((sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R).functor.obj L)) := by
  let J := Scheme.ProEt.topology X
  let b := sectionScalarMap.{u + 1, u + 1, u} J a
  let E := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u} b
  let adj := SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u} b
  let α : (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor ⋙ E ⟶
      Mod.extendScalars a ⋙ (sectionModuleEquivalence.{u + 1, u + 1, u} J S).functor :=
    ((mateEquiv (Mod.extendRestrictAdjunction a) adj).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionIso.{u + 1, u + 1, u} J a).hom))
  have : IsIso α := inverseMate_isIso (Mod.extendRestrictAdjunction a) adj
    (scalarRestrictionIso.{u + 1, u + 1, u} J a)
  exact ⟨((asIso α).symm.app L)⟩

private def localTensorBasisIso (X : Scheme.{u})
    {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : A ⟶ B)
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (W : X.ProEt)
    (e : M.over W ≅ (SheafOfModules.unit.{u, u + 1, u + 1} _).over W) :
    (SheafOfModules.slicePresheafRestrictionIndependent.{u + 1, u + 1, u, u, u + 1}
      (J := (Scheme.ProEt.topology X).over W) (Over.forget W)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)).obj
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M) ≅
      ((SheafOfModules.unit.{u, u + 1, u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)).over W).val := by
  let c (V : (Over W)ᵒᵖ) :=
    let f := (a.hom.app (op V.unop.left)).hom
    letI := f.toAlgebra
    (ModuleCat.extendScalars f).mapIso
        ((SheafOfModules.evaluation _ V).mapIso e) ≪≫
      (TensorProduct.AlgebraTensorModule.rid (A.obj.obj (op V.unop.left))
        (B.obj.obj (op V.unop.left)) (B.obj.obj (op V.unop.left))).toModuleIso
  refine PresheafOfModules.isoMk c ?_
  intro U V f
  let : CommRing
      (((Over.forget W).op ⋙ ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj).obj U) :=
    inferInstanceAs (CommRing (A.obj.obj (op U.unop.left)))
  let : CommRing
      (((Over.forget W).op ⋙ ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj).obj U) :=
    inferInstanceAs (CommRing (B.obj.obj (op U.unop.left)))
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have he := PresheafOfModules.naturality_apply e.hom.val f m
  change e.hom.val.app V (M.val.map ((Over.forget W).op.map f) m) =
    A.obj.map ((Over.forget W).op.map f) (e.hom.val.app U m) at he
  have ha := ConcreteCategory.congr_hom
    (a.hom.naturality ((Over.forget W).op.map f)) (e.hom.val.app U m)
  change (a.hom.app (op V.unop.left)).hom
      (A.obj.map ((Over.forget W).op.map f) (e.hom.val.app U m)) =
    B.obj.map ((Over.forget W).op.map f)
      ((a.hom.app (op U.unop.left)).hom (e.hom.val.app U m)) at ha
  let := (a.hom.app (op U.unop.left)).hom.toAlgebra
  let := (a.hom.app (op V.unop.left)).hom.toAlgebra
  change (c V).hom
      (SheafOfModules.changeOfRingsMap a M ((Over.forget W).op.map f)
        ((1 : B.obj.obj (op U.unop.left)) ⊗ₜ[_, (a.hom.app (op U.unop.left)).hom] m)) =
    B.obj.map ((Over.forget W).op.map f)
      ((c U).hom
        ((1 : B.obj.obj (op U.unop.left)) ⊗ₜ[_, (a.hom.app (op U.unop.left)).hom] m))
  erw [SheafOfModules.changeOfRingsMap_tmul a M ((Over.forget W).op.map f)
    (1 : B.obj.obj (op U.unop.left)) m]
  simp only [map_one]
  change (TensorProduct.AlgebraTensorModule.rid (A.obj.obj (op V.unop.left))
      (B.obj.obj (op V.unop.left)) (B.obj.obj (op V.unop.left)))
      ((ModuleCat.extendScalars (a.hom.app (op V.unop.left)).hom).map
        (e.hom.val.app V)
        ((1 : B.obj.obj (op V.unop.left)) ⊗ₜ[_, (a.hom.app (op V.unop.left)).hom]
          M.val.map ((Over.forget W).op.map f) m)) =
    B.obj.map ((Over.forget W).op.map f)
      ((TensorProduct.AlgebraTensorModule.rid (A.obj.obj (op U.unop.left))
        (B.obj.obj (op U.unop.left)) (B.obj.obj (op U.unop.left)))
        ((ModuleCat.extendScalars (a.hom.app (op U.unop.left)).hom).map
          (e.hom.val.app U)
          ((1 : B.obj.obj (op U.unop.left)) ⊗ₜ[_, (a.hom.app (op U.unop.left)).hom] m)))
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
  simp only [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra, mul_one]
  convert (congrArg ((a.hom.app (op V.unop.left)).hom) he).trans ha using 1

/-- An internal module trivialized on one slice remains trivialized there after
extension along a map of commutative coefficient rings.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), rational scalar extension;
sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md, slice calculation.
(blueprint: lem-sp-slice-scalar-extension-basis)

Proof: reconstruct section rings and module actions from the internal rings and
modules. Internal scalar extension is the sheafification of the sectionwise
balanced tensor S tensor_R L. On the slice the presheaf tensor has the same
sections and restriction maps as the restricted global tensor. Sheafification
also restricts to this tensor, since coverings of each slice object are precisely
its coverings in the original site. Thus the restriction of the actual internal
extension identifies with scalar extension of the restricted section module.
Tensor the given basis and its inverse with S; the balancing relations retain
the inverse equations. The multiplication map S tensor_R R -> S has inverse
s -> s tensor 1, and both maps are S-linear. Compose these maps to obtain the
asserted S-linear isomorphism. This requires no flatness, no invertibility of a
prime, and no hypotheses on L away from the specified slice. In particular the
argument also applies to zero coefficient rings and the empty slice. -/
theorem spSliceScalarExtensionBasis (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (W : X.ProEt)
    (e : (spRootBasisSliceSections X R W).obj L ≅
      (SheafOfModules.unit.{u, u + 1, u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R))).over W) :
    Nonempty ((spRootBasisSliceSections X S W).obj ((Mod.extendScalars a).obj L) ≅
      (SheafOfModules.unit.{u, u + 1, u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S))).over W) := by
  let J := Scheme.ProEt.topology X
  let B := sectionRingSheaf.{u + 1, u + 1, u} J S
  let b := sectionScalarMap.{u + 1, u + 1, u} J a
  let M := (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj L
  let Q := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} b M
  let B₀ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let U := (SheafOfModules.unit.{u, u + 1, u + 1} B₀).over W
  obtain ⟨i⟩ := internalSectionExtensionIso X a L
  let j := (SheafOfModules.overFunctor B₀ W).mapIso i
  let t := SheafOfModules.sliceSheafificationComparisonIndependent.{u + 1, u + 1, u, u, u + 1}
    (J := J.over W) (Over.forget W) B₀
  have ht :=
    SheafOfModules.sliceSheafificationComparisonIndependent_isIso.{u + 1, u + 1, u, u, u + 1}
    (J := J.over W) (Over.forget W) B₀
  let F := PresheafOfModules.sheafification.{u + 1} (𝟙 (B₀.over W).obj)
  let k := F.mapIso (localTensorBasisIso.{u} X b M W e)
  let h := asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (B₀.over W).obj)).counit.app U)
  exact ⟨j ≪≫ (asIso (t.app Q)).symm ≪≫ k ≪≫ h⟩

end AlgebraicGeometry.ProEtale
