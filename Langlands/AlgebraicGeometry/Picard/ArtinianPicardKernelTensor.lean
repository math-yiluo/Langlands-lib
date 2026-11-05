import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardObstructionFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual affine elementary Picard kernels as coefficient tensors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardKernelTensor

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardObstructionFinite

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A flat original family remains flat over every actual Artinian test. -/
lemma projection_flat [Flat f] (A : ArtinianTest k K) :
    Flat ((relativeProjection f).app (ArtinianTest.base A)) :=
  inferInstanceAs (Flat (Limits.pullback.fst (ArtinianTest.base A).hom f))

/-- The actual source-ring map to affine sections is flat. -/
lemma testSectionHom_flat [Flat f] (A : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    (testSectionHom f A U).Flat := by
  have := projection_flat f A
  exact (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A.algebra)).inv)).comp
        (((relativeProjection f).app (ArtinianTest.base A)).flat_appLE
          (isAffineOpen_top (Spec (CommRingCat.of A.algebra))) hU le_top)

/-- The actual source-ring algebra structure on sections. -/
@[instance_reducible]
def sectionAlgebra (A : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Algebra A.algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U) :=
  (testSectionHom f A U).toAlgebra

attribute [local instance] sectionAlgebra

/-- The source-ring action commutes with restriction on the actual scheme. -/
lemma testSectionHom_res (A : ArtinianTest k K)
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (a : A.algebra) :
    ((relativeSpace f).obj (ArtinianTest.base A)).presheaf.map (homOfLE h).op
      (testSectionHom f A U a) = testSectionHom f A V a := by
  unfold testSectionHom
  change ((((relativeProjection f).app (ArtinianTest.base A)).appLE ⊤ U le_top ≫
    ((relativeSpace f).obj (ArtinianTest.base A)).presheaf.map (homOfLE h).op)
      ((Scheme.ΓSpecIso (CommRingCat.of A.algebra)).inv a)) = _
  rw [Scheme.Hom.appLE_map]
  rfl

/-- Restriction as an algebra map over the actual Artinian source. -/
def sectionRestriction (A : ArtinianTest k K)
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U) :
    Γ((relativeSpace f).obj (ArtinianTest.base A), U) →ₐ[A.algebra]
      Γ((relativeSpace f).obj (ArtinianTest.base A), V) :=
  { (((relativeSpace f).obj (ArtinianTest.base A)).presheaf.map (homOfLE h).op).hom with
    commutes' := testSectionHom_res f A h }

variable {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out

local instance : Algebra A.algebra K := A.augmentation.toRingHom.toAlgebra
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq
local instance
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U)
      (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :=
  Algebra.TensorProduct.rightAlgebra

/-- Restriction of the fibre section algebra obtained by the residue augmentation. -/
def fibreRestriction
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U) :
    K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U) →ₐ[K]
      K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), V) :=
  Algebra.TensorProduct.map (AlgHom.id K K) (sectionRestriction f A h)

/-- The affine-section kernel is the actual fibre coefficient tensor of the
unchanged elementary kernel. -/
def affineKernelEquiv [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) ⊗[K] Kernel q
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)] Γ(idealModule f q, U) := by
  let : Module.Flat A.algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U) :=
    testSectionHom_flat f A U hU
  exact (ElementaryKernelTensor.kernelTensorEquiv q).trans
    (LinearEquiv.ofEq _ _ (relativeMap_affine_ker f q hq.1 U hU).symm)

@[simp]
lemma affineKernelEquiv_tmul [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (c : K) (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) (x : Kernel q) :
    (affineKernelEquiv f q U hU ((c ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val =
      testSectionHom f A U (c • x).val * r := by
  let : Module.Flat A.algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U) :=
    testSectionHom_flat f A U hU
  change (ElementaryKernelTensor.kernelTensorEquiv q
    ((c ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val = _
  exact ElementaryKernelTensor.kernelTensorEquiv_tmul q c r x

@[simp]
lemma affineKernelEquiv_one_tmul [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) (x : Kernel q) :
    (affineKernelEquiv f q U hU ((1 ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val =
      testSectionHom f A U x.val * r := by
  simpa only [one_smul] using affineKernelEquiv_tmul f q U hU (1 : K) r x

/-- The affine tensor comparison commutes with the actual ideal-module restriction. -/
lemma affineKernelEquiv_res [Flat f]
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) ⊗[K]
      Kernel q) :
    (idealModule f q).presheaf.map (homOfLE h).op (affineKernelEquiv f q U hU t) =
      affineKernelEquiv f q V hV
        (TensorProduct.map (fibreRestriction f h).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    induction y using TensorProduct.inductionOn with
    | tmul c r =>
      apply Subtype.ext
      change ((relativeSpace f).obj (ArtinianTest.base A)).presheaf.map (homOfLE h).op
          (affineKernelEquiv f q U hU ((c ⊗ₜ[A.algebra] r) ⊗ₜ[K] x)).val =
        (affineKernelEquiv f q V hV
          ((c ⊗ₜ[A.algebra] (sectionRestriction f A h r)) ⊗ₜ[K] x)).val
      rw [affineKernelEquiv_tmul, affineKernelEquiv_tmul, map_mul, testSectionHom_res]
      rfl
    | add a b ha hb =>
      simpa only [TensorProduct.add_tmul, LinearEquiv.map_add, LinearMap.map_add,
        map_add ((idealModule f q).presheaf.map (homOfLE h).op).hom]
        using congrArg₂ (· + ·) ha hb
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, LinearMap.map_add,
      map_add ((idealModule f q).presheaf.map (homOfLE h).op).hom]
      using congrArg₂ (· + ·) ha hb

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardKernelTensor
