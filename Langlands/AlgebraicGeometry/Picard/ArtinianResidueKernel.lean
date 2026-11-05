import Langlands.AlgebraicGeometry.Picard.ArtinianResidueSections

/-! # Actual residue-fibre coefficients of elementary Picard kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueKernel

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor
open ArtinianResidueSections ArtinianPicardObstructionFinite

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local notation "i" => residueMap f A

attribute [local instance] sectionAlgebra residueSectionAlgebra

local instance : Algebra A.algebra K := A.augmentation.toRingHom.toAlgebra
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq

local instance
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U)
      (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :=
  Algebra.TensorProduct.rightAlgebra

/-- The actual section-ring action on sections of the residue fibre. -/
@[instance_reducible]
def residueSourceAlgebra
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Algebra Γ((relativeSpace f).obj (ArtinianTest.base A), U)
      Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) :=
  ((i).app U).hom.toAlgebra

attribute [local instance] residueSourceAlgebra

/-- The canonical affine residue-section comparison preserves the actual source action. -/
lemma affineSectionsEquiv_smul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (t : K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    affineSectionsEquiv f A U hU (r • t) = r • affineSectionsEquiv f A U hU t := by
  change affineSectionsEquiv f A U hU (((1 : K) ⊗ₜ[A.algebra] r) * t) =
    (i).app U r * affineSectionsEquiv f A U hU t
  rw [map_mul, affineSectionsEquiv_one_tmul]

/-- Tensor the actual affine residue-section equivalence with the unchanged kernel. -/
def coefficientSectionsEquiv
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) ⊗[K] Kernel q
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)]
        Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K] Kernel q :=
  { (TensorProduct.congr (affineSectionsEquiv f A U hU).toLinearEquiv
      (LinearEquiv.refl K (Kernel q))).toAddEquiv with
    map_smul' := by
      intro r t
      change (TensorProduct.congr (affineSectionsEquiv f A U hU).toLinearEquiv
          (LinearEquiv.refl K (Kernel q))) (r • t) =
        r • (TensorProduct.congr (affineSectionsEquiv f A U hU).toLinearEquiv
          (LinearEquiv.refl K (Kernel q))) t
      induction t using TensorProduct.inductionOn with
      | tmul y x =>
        change affineSectionsEquiv f A U hU (r • y) ⊗ₜ[K] x =
          (r • affineSectionsEquiv f A U hU y) ⊗ₜ[K] x
        rw [affineSectionsEquiv_smul]
      | add a b ha hb =>
        simpa only [smul_add, LinearEquiv.map_add] using congrArg₂ (· + ·) ha hb }

@[simp]
lemma coefficientSectionsEquiv_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (y : K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (x : Kernel q) :
    coefficientSectionsEquiv f q U hU (y ⊗ₜ[K] x) =
      affineSectionsEquiv f A U hU y ⊗ₜ[K] x := rfl

/-- The coefficient-section comparison commutes with actual restriction. -/
lemma coefficientSectionsEquiv_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) ⊗[K]
      Kernel q) :
    TensorProduct.map
        (residueSectionRestriction f
          (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id
        (coefficientSectionsEquiv f q U hU t) =
      coefficientSectionsEquiv f q V hV
        (TensorProduct.map (fibreRestriction f h).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    change residueSectionRestriction f _ (affineSectionsEquiv f A U hU y) ⊗ₜ[K] x =
      affineSectionsEquiv f A V hV (fibreRestriction f h y) ⊗ₜ[K] x
    rw [affineSectionsEquiv_res]
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, LinearMap.map_add]
      using congrArg₂ (· + ·) ha hb

/-- Actual residue-fibre coefficients give the actual elementary ideal sections. -/
def affineKernelResidueEquiv [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K] Kernel q
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)] Γ(idealModule f q, U) :=
  (coefficientSectionsEquiv f q U hU).symm.trans (affineKernelEquiv f q U hU)

@[simp]
lemma affineKernelResidueEquiv_coefficientSectionsEquiv [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (t : (K ⊗[A.algebra] Γ((relativeSpace f).obj (ArtinianTest.base A), U)) ⊗[K]
      Kernel q) :
    affineKernelResidueEquiv f q U hU (coefficientSectionsEquiv f q U hU t) =
      affineKernelEquiv f q U hU t := by
  exact congrArg (affineKernelEquiv f q U hU)
    ((coefficientSectionsEquiv f q U hU).symm_apply_apply t)

/-- A coefficient from an actual source section has its expected ideal product. -/
@[simp]
lemma affineKernelResidueEquiv_one_tmul [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (r : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) (x : Kernel q) :
    (affineKernelResidueEquiv f q U hU ((i).app U r ⊗ₜ[K] x)).val =
      testSectionHom f A U x.val * r := by
  rw [← affineSectionsEquiv_one_tmul f A U hU r,
    ← coefficientSectionsEquiv_tmul, affineKernelResidueEquiv_coefficientSectionsEquiv]
  exact affineKernelEquiv_one_tmul f q U hU r x

/-- The actual residue-fibre kernel comparison commutes with ideal restriction. -/
lemma affineKernelResidueEquiv_res [Flat f]
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (t : Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K]
      Kernel q) :
    (idealModule f q).presheaf.map (homOfLE h).op (affineKernelResidueEquiv f q U hU t) =
      affineKernelResidueEquiv f q V hV
        (TensorProduct.map
          (residueSectionRestriction f
            (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id t) := by
  obtain ⟨s, rfl⟩ := (coefficientSectionsEquiv f q U hU).surjective t
  rw [coefficientSectionsEquiv_res f q h hU hV,
    affineKernelResidueEquiv_coefficientSectionsEquiv,
    affineKernelResidueEquiv_coefficientSectionsEquiv]
  exact affineKernelEquiv_res f q h hU hV s

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueKernel
