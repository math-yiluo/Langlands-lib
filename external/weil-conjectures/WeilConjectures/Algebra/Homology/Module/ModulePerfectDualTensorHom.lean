/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-! # Signed finite-free dual tensor and algebraic Hom -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CochainComplex

private noncomputable def modelπ {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + n = q) :
    (moduleHomComplex P N).X n ⟶ (ihom (P.X p)).obj (N.X q) :=
  ModuleCat.ofHom
    { toFun := fun f ↦ f.v p q h
      map_add' := fun f g ↦ HomComplex.Cochain.add_v f g p q h
      map_smul' := fun r f ↦ HomComplex.Cochain.smul_v r f p q h }

private noncomputable def modelToInternalX {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleHomComplex P N).X n ⟶ (internalHomObj P N).X n :=
  Pi.lift fun T : HomComplex.Triplet n ↦
    (T.p * n).negOnePow • modelπ P N n T.p T.q T.hpq

private lemma modelToInternalX_π {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + n = q) :
    modelToInternalX P N n ≫ internalHomπ P N n p q h =
      (p * n).negOnePow • modelπ P N n p q h :=
  Pi.lift_comp_π _ _

private noncomputable def internalToModelX {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (internalHomObj P N).X n ⟶ (moduleHomComplex P N).X n :=
  ModuleCat.ofHom
    { toFun := fun f ↦ HomComplex.Cochain.mk fun p q h ↦
        (p * n).negOnePow • internalHomπ P N n p q h f
      map_add' := fun f g ↦ by
        apply HomComplex.Cochain.ext
        intro p q h
        simp [smul_add]
      map_smul' := fun r f ↦ by
        apply HomComplex.Cochain.ext
        intro p q h
        simp [smul_comm r] }

private lemma internalToModelX_π {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + n = q) :
    internalToModelX P N n ≫ modelπ P N n p q h =
      (p * n).negOnePow • internalHomπ P N n p q h := by
  rfl

private noncomputable def modelXIso {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleHomComplex P N).X n ≅ (internalHomObj P N).X n where
  hom := modelToInternalX P N n
  inv := internalToModelX P N n
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply HomComplex.Cochain.ext
    intro p q h
    have e := modelToInternalX_π P N n p q h
    have e' := congrArg (fun k ↦ k f) e
    change (p * n).negOnePow • internalHomπ P N n p q h
      (modelToInternalX P N n f) = f.v p q h
    rw [show internalHomπ P N n p q h (modelToInternalX P N n f) =
      (p * n).negOnePow • f.v p q h from e']
    simp [smul_smul]
  inv_hom_id := internalHomObj_hom_ext fun p q h ↦ by
    rw [Category.assoc, modelToInternalX_π, Linear.comp_units_smul,
      internalToModelX_π, smul_smul, Int.units_mul_self, one_smul, Category.id_comp]

private lemma modelToInternalX_comm {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) (hnm : n + 1 = m) :
    modelToInternalX P N n ≫ (internalHomObj P N).d n m =
      (moduleHomComplex P N).d n m ≫ modelToInternalX P N m := by
  subst m
  apply internalHomObj_hom_ext
  intro p q h
  rw [Category.assoc, Category.assoc,
    internalHomObj_d_π P N n (n + 1) p q h (p + n) (p + 1) rfl (by omega),
    modelToInternalX_π]
  simp only [Linear.comp_units_smul, Preadditive.comp_sub,
    ← Category.assoc, modelToInternalX_π, Linear.units_smul_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change p.negOnePow •
      ((p * n).negOnePow • (f.v p (p + n) rfl ≫ N.d (p + n) q) -
        ((p + 1) * n).negOnePow • (P.d p (p + 1) ≫ f.v (p + 1) q (by omega))) =
    (p * (n + 1)).negOnePow • (HomComplex.δ n (n + 1) f).v p q h
  rw [HomComplex.δ_v n (n + 1) rfl f p q h (p + n) (p + 1) (by omega) rfl]
  rw [show p * (n + 1) = p * n + p by ring,
    show (p + 1) * n = p * n + n by ring, Int.negOnePow_add, Int.negOnePow_add]
  simp only [Int.negOnePow_succ, Units.neg_smul, smul_add, smul_neg,
    smul_smul, mul_comm, mul_left_comm, sub_eq_add_neg]

private noncomputable def modelIso {R : Type u} [CommRing R]
    (P N : CochainComplex (ModuleCat.{u} R) ℤ) :
    moduleHomComplex P N ≅ internalHomObj P N :=
  HomologicalComplex.Hom.isoOfComponents (modelXIso P N)
    (fun n m h ↦ modelToInternalX_comm P N n m h)

set_option linter.style.haveILetI false in
/-- A bounded finite-free complex has its signed dual tensor as its algebraic
endomorphism complex.

Source: Stacks Project, More on Algebra, Tags 0A6A and 0ATK, finite-projective
Hom calculation; current blueprint `proposition-local-structure-integral-constructible-complexes`,
uniform-bound paragraph.
(blueprint: lem-pe-module-perfect-dual-tensor-hom).

Proof: in dual degree r, projection to the only possibly nonzero target degree
identifies Hom(P,A[0])^r with Hom(P^(-r),A). For each r,s use the finite dual-basis
isomorphism Hom(P^(-r),A) tensor P^s = Hom(P^(-r),P^s). Multiply this map by the
unit (-1)^(r*s). For total degree k, reindex r+s=k by p=-r. Boundedness of P makes
only finitely many factors nonzero, so the direct sum of these isomorphisms is an
isomorphism onto the product defining Hom(P,P)^k. The differential on the dual is
-(-1)^r precomposition with d_P. Its tensor differential is d_dual tensor 1 plus
(-1)^r times 1 tensor d_P. Changing r to r+1 multiplies the evaluation sign by
(-1)^s; changing s to s+1 multiplies it by (-1)^r. The resulting two terms are
exactly d_P f - (-1)^k f d_P, so the degree isomorphisms commute with differentials
and form a complex isomorphism. The zero ring, zero complex and empty support
interval use the identical finite biproduct construction. -/
theorem modulePerfectDualTensorHom_iso {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) :
    Nonempty (CochainComplex.mapBifunctor
      (CochainComplex.moduleHomComplex P
        ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R))) P
      (curriedTensor _) ≅ CochainComplex.moduleHomComplex P P) := by
  letI : ∀ i : ℤ, Module.Finite R (P.X i) := fun i => (_hfree i).1
  letI : ∀ i : ℤ, Module.Free R (P.X i) := fun i => (_hfree i).2
  letI (X₁ X₂ : GradedObject ℤ (ModuleCat.{u} R)) : X₁.HasTensor X₂ := inferInstance
  letI (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat.{u} R)) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  letI (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat.{u} R)) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  letI (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat.{u} R)) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  letI : HasColimitsOfSize.{0, 0} (ModuleCat.{u} R) := hasColimitsOfSizeShrink _
  letI : MonoidalCategory (CochainComplex (ModuleCat.{u} R) ℤ) := inferInstance
  letI : MonoidalClosed (CochainComplex (ModuleCat.{u} R) ℤ) :=
    { closed := fun X =>
        { rightAdj := CochainComplex.internalHom X
          adj := CochainComplex.tensorHomAdjunction X } }
  letI : ∀ i, HasRightDual (P.X i) :=
    fun i => (ModuleCat.isDualizable_of_projective (P.X i)).some
  letI := CochainComplex.exactPairingRightDual P a b
  letI : ExactPairing P.rightDual P :=
    BraidedCategory.exactPairing_swap P P.rightDual
  letI : IsIso (MonoidalClosed.ihomUnitTensorToIhom P P) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom P.rightDual P P
  let e : internalHomObj P
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of R R)) ⊗ P ≅
      internalHomObj P P :=
    asIso (MonoidalClosed.ihomUnitTensorToIhom P P)
  let U := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let eU := modelIso P U
  let eP := modelIso P P
  letI : IsIso eU.hom := CategoryTheory.Iso.isIso_hom eU
  let t : CochainComplex.mapBifunctor (moduleHomComplex P U) P
      (curriedTensor (ModuleCat.{u} R)) ≅
      CochainComplex.mapBifunctor (internalHomObj P U) P
        (curriedTensor (ModuleCat.{u} R)) :=
    ((CategoryTheory.Functor.map₂CochainComplex
      (curriedTensor (ModuleCat.{u} R))).mapIso eU).app P
  exact ⟨t ≪≫ e ≪≫ eP.symm⟩

end CochainComplex
