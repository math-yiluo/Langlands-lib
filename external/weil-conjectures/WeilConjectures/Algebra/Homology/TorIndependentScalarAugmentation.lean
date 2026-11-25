/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.SingleSupportTorAcyclicTensor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Tor-independent scalar augmentation

Source: Stacks Project, Tag 08IB, final affine calculation; Tags 06Y6 and 06XY.
(blueprint: lem-pc-tor-independent-scalar-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat

/-- Scalar extension of a K-flat resolution of B is an augmentation quasi-isomorphism
when A and B are Tor independent over R.
Source: Stacks Project, Tag 08IB, final affine calculation; Tag 06Y6 and Section 06XY.
(blueprint: lem-pc-tor-independent-scalar-augmentation).

Proof: Take a functorial K-flat resolution p:P -> A[0]. Apply the existing
one-term Tor-acyclic tensor lemma to p and B. Its hypothesis is exactly the
positive Tor vanishing in the statement, transported along A[0].X 0 = A.
Thus the termwise tensor of p with B is a quasi-isomorphism. The single-factor
total tensor isomorphism identifies it with p tensor B[0]. The identity linear
equivalence identifies the algebra R-module B with restriction of the B-module B.
K-flatness of F
makes p tensor F a quasi-isomorphism; K-flatness of P makes P tensor f a
quasi-isomorphism. The tensor square commutes by whisker exchange. Its top
and right sides are quasi-isomorphisms, as is its left side, so two-out-of-three
makes A[0] tensor f a quasi-isomorphism. The single-factor comparison identifies
this with termwise tensoring f with A. The composition comparison for functors
identifies the latter with scalar extension to A followed by restriction to R.
Restriction detects quasi-isomorphisms, proving the claim over A. The proof
uses the same argument for unbounded F, zero rings and zero complexes. -/
theorem scalarAugmentation_quasiIso_of_torIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      ((restrictScalars (algebraMap R B)).obj (of B B)))
    (hf : QuasiIso f) :
    QuasiIso (((extendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f) :=
  by
    classical
    have (M : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
        ((curriedTensor (ModuleCat.{u} R)).flip.obj M) :=
      inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight M))
    have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
        (AsSmall.equiv (C := ℤ)).symm
    let C := ModuleCat.{u} R
    let A₀ := (CochainComplex.singleFunctor C (0 : ℤ)).obj (of R A)
    let B₀ := (CochainComplex.singleFunctor C (0 : ℤ)).obj
      ((restrictScalars (algebraMap R B)).obj (of B B))
    let Λ := (Classical.choice (inferInstance :
      Abelian.HasFunctorialFlatResolution C)).reduced
    let P := Λ.resolutionFunctor.obj A₀
    let p := Λ.resolutionNatTrans.app A₀
    have hp : QuasiIso p := inferInstance
    have hP := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le A₀
    have hpB := CochainComplex.quasiIso_tensor_of_single_support_tor_acyclic
      A₀ 0 (fun n hn ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
      (fun i hi ↦ (hTor i hi).of_iso
        (Functor.mapIso (((tensoringRight C).obj (of R B)).leftDerived i)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (of R A))))
      ⟨P, hP⟩ p hp
    let e (K : CochainComplex C ℤ) :=
      CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) (of R B) K
    have hb : QuasiIso (p ▷
        ((HomologicalComplex.single C (.up ℤ) 0).obj (of R B))) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (e P) (e A₀) (by
          exact (CochainComplex.mapBifunctorSingle₂Iso_hom_naturality
            (curriedTensor C) (of R B) p).symm))).2 hpB
    let b : (restrictScalars (algebraMap R B)).obj (of B B) ≅ of R B :=
      (show (restrictScalars (algebraMap R B)).obj (of B B) ≃ₗ[R] of R B from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ (@Algebra.smul_def R B _ _ _ r x).symm }).toModuleIso
    let b₀ := (HomologicalComplex.single C (.up ℤ) 0).mapIso b
    have : QuasiIso (p ▷ B₀) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk ((tensorLeft P).mapIso b₀) ((tensorLeft A₀).mapIso b₀)
          (by exact whisker_exchange p b₀.hom))).2 hb
    have : QuasiIso p := hp
    have : QuasiIso f := hf
    have : QuasiIso (p ▷ F) := hF.whiskerRight hp
    have : QuasiIso (P ◁ f) := hP.whiskerLeft hf
    have he : (p ▷ F) ≫ (A₀ ◁ f) = (P ◁ f) ≫ (p ▷ B₀) :=
      (whisker_exchange p f).symm
    have : QuasiIso ((p ▷ F) ≫ (A₀ ◁ f)) := by
      rw [he]
      infer_instance
    have ht : QuasiIso (A₀ ◁ f) := quasiIso_of_comp_left (p ▷ F) (A₀ ◁ f)
    let a (K : CochainComplex C ℤ) :=
      CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C) (of R A) K
    have hleft : QuasiIso (((tensorLeft (of R A)).mapHomologicalComplex (.up ℤ)).map f) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk (a F) (a B₀) (by
          exact (CochainComplex.mapBifunctorSingle₁Iso_hom_naturality
            (curriedTensor C) (of R A) f).symm))).1 ht
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (((extendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f)
      (restrictScalars (algebraMap R A))).1
    let aR : (restrictScalars (algebraMap R A)).obj (of A A) ≅ of R A :=
      (show (restrictScalars (algebraMap R A)).obj (of A A) ≃ₗ[R] of R A from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ (@Algebra.smul_def R A _ _ _ r x).symm }).toModuleIso
    have : (extendScalars (algebraMap R A)).Additive :=
      (extendRestrictScalarsAdj (algebraMap R A)).left_adjoint_additive
    let c₁ :
        (extendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) ≅
        (tensorLeft ((restrictScalars (algebraMap R A)).obj (of A A))).mapHomologicalComplex
          (.up ℤ) :=
      Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)
    let c :
        (extendScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ) ≅
        (tensorLeft (of R A)).mapHomologicalComplex (.up ℤ) :=
      c₁ ≪≫ NatIso.mapHomologicalComplex ((curriedTensor C).mapIso aR) (.up ℤ)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app F) (c.app B₀) (by exact (c.hom.naturality f).symm))).2 hleft

end ModuleCat
