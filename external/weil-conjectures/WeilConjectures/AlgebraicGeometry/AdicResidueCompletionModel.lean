/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore

/-! # The local completion reflector for the actual residue kernel

Source: Stacks Project, Tags 099L, 099E and 099F.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme

/-- The kernel of the actual residue projection on the slice is of finite type.
Source: Stacks Tags 099L and 099E
(auxiliary; not a blueprint node).
Proof: choose finitely many generators of J. The sectionwise quotient formula for the
completed coefficient sheaf identifies the residue kernel with their span. This remains
the same formula on every object of the slice. The global generating sections on each
further slice give finite local generators of the kernel module. -/
theorem adicResidueKernel_finiteType
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) :
    (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).module.IsFiniteType := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  let T := coefficientProEtaleModelTopology.{u, v} X
  let φ := coefficientMap T A J
  let b (i : Fin r) :
      (((completed T A J).over U).obj ⋙ CategoryTheory.forget CommRingCat).sections :=
    { val := fun V ↦ (algebraSection φ (a i)).val (op V.unop.left)
      property := fun f ↦ (algebraSection φ (a i)).property ((Over.forget U).op.map f) }
  apply ideal_finiteType_of_span (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)) r b
  intro V
  have hk := (kernelIdeal_existsUnique
    (adicResidueLocalProjection.{u, v} X J U 0)).exists.choose_spec V
  change (kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)).sections V = _ at hk
  rw [hk]
  change RingHom.ker ((projection T A J 0).hom.app (op V.left)).hom = _
  rw [((flat_and_quotients T A J).2.1 0 V.left).2]
  let f : A →+* (completed T A J).obj.obj (op V.left) :=
    (φ.hom.app (op V.left)).hom.comp
      ((toSheafify T ((Functor.const _).obj (CommRingCat.of A))).app (op V.left)).hom
  exact span_subtype_images f (J ^ (0 + 1)) a
    (by simpa only [Nat.zero_add, pow_one] using ha)

attribute [local instance] HasDerivedCategory.standard

/-- A genuine augmented Cech model for the residue kernel; its unit is invertible
on every object satisfying the existing local completeness predicate.
Source: Stacks Tags 099E and 099F
(auxiliary; not a blueprint node).
Proof: the preceding finite generation supplies the hypothesis of the existing global
extended-Cech model theorem. Apply its reflector theorem to the same kernel inclusion.
Its completeness hypothesis is definitionally ConstantCompletion.IsComplete, so the
unit-isomorphism clause applies without changing any ideal or coefficient action. -/
theorem adicResidueCompletionModel_exists
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
    ∃ (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R),
      HasLocalExtendedCechDescription R I.module I.inclusion K ε ∧
      ∀ M : AdicResidueLocalDerived.{u, v} X J U,
        IsComplete (adicResidueLocalProjection.{u, v} X J U 0) M →
          IsIso (ringedCechCompletionUnit R K ε M) := by
  dsimp only
  let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  let I := kernelIdeal (adicResidueLocalProjection.{u, v} X J U 0)
  let := HasDerivedCategory.standard (Mod R)
  have hmono : Mono I.inclusion := by
    constructor
    intro N f g hfg
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h ↦ h.val.app V x) hfg
  have : I.module.IsFiniteType := adicResidueKernel_finiteType.{u, v} X J U
  obtain ⟨K, ε, hK⟩ := exists_ringedExtendedCech_global_model _ R I.module I.inclusion
  refine ⟨K, ε, hK, ?_⟩
  intro M hM
  exact (ringedExtendedCech_reflector_properties _ R I.module I.inclusion K ε hK).2.2.2 M hM

end AlgebraicGeometry.Scheme
