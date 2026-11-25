/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.DerivedTensorPrecompositionOpen
import WeilConjectures.AlgebraicGeometry.DerivedTensorPrecompositionProjection
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Transporting a tensor annihilator across a direct-image adjunction

Source: Stacks Project, Tag 0E4G, projection-formula paragraph.
(blueprint: lem-sc-adjoint-tensor-annihilator-transport).
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A perfect tensor annihilator for the adjoint of beta gives a precomposition killing
beta which becomes invertible over the inverse image open.
Source: Stacks Project, Tag 0E4G, projection-formula paragraph.
(blueprint: lem-sc-adjoint-tensor-annihilator-transport).

Proof: Set R = Lf*I tensor P and j = (Lf*i tensor id) followed by the tensor unit
isomorphism. Derived pullback and tensor preserve quasi-coherent cohomology, so R is
an object of D_QCoh(X). The projection formula identifies Rf*R with I tensor Rf*P, compatibly
with their maps to Rf*P: this is naturality of the projection formula in I applied to
i : I -> O_Y and its unit compatibility. Transport this square through hF. Naturality
of the adjunction Hom equivalence in its source identifies the adjoint of j followed
by beta with i tensor id followed by the left unitor and the adjoint of beta. The
latter is zero by hypothesis; the adjunction is additive, so j followed by beta is zero.
On U = f^-1(V), restriction of Lf*i is the derived pullback of the restriction of i.
It is invertible since restriction of i to V is invertible. Tensoring and applying the
unit isomorphism preserve invertibility, giving the asserted property of j. The domain
R is used only existentially in this theorem, not to define any chosen data. The proof
works for zero P or beta and for the empty open; it assumes neither support of Q nor
nonvanishing of beta. -/
theorem adjoint_tensor_annihilator_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (Q : schemeDerivedQCohCategory Y)
    (β : P ⟶ a.obj Q) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i))
    (hkill : i ▷ (F.obj P).obj ≫ (λ_ (F.obj P).obj).hom ≫
      ((adj.homEquiv P Q).symm β).hom = 0) :
    ∃ (R : schemeDerivedCategory X) (j : R ⟶ P.obj),
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map j) ∧ j ≫ β.hom = 0 := by
  obtain ⟨e, hR, hj⟩ := exists_derivedTensor_precomposition_open f V P I hI i hi
  let R : schemeDerivedQCohCategory X :=
    ⟨(derivedPullbackAcrossUniverses f).obj I ⊗ P.obj, hR⟩
  let j : R ⟶ P := ObjectProperty.homMk
    ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
      e.hom ▷ P.obj ≫ (λ_ P.obj).hom)
  obtain ⟨t, ht⟩ := exists_derivedTensor_precomposition_projection f F hF P I hI i e hR
  have hzero : F.map j ≫ (adj.homEquiv P Q).symm β = 0 := by
    apply ObjectProperty.hom_ext
    change (F.map j).hom ≫ ((adj.homEquiv P Q).symm β).hom = 0
    rw [show (F.map j).hom = t ≫ i ▷ (F.obj P).obj ≫
      (λ_ (F.obj P).obj).hom from ht]
    simp only [Category.assoc, hkill, Limits.comp_zero]
  have hcomp : j ≫ β = 0 := by
    have : (F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y)).Additive :=
      Functor.additive_of_iso hF.symm
    have : F.Additive :=
      Functor.additive_of_comp_faithful F (ObjectProperty.ι (schemeDerivedQCohProperty Y))
    rw [← Equiv.apply_symm_apply (adj.homEquiv P Q) β,
      ← adj.homEquiv_naturality_left, hzero, adj.homAddEquiv_zero]
  exact ⟨R.obj, j.hom, hj, congrArg InducedCategory.Hom.hom hcomp⟩

end AlgebraicGeometry
