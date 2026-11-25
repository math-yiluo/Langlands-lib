/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeakContractibleEquivalences
import WeilConjectures.ProEtaleCoefficients.FiniteProductWContractible
import WeilConjectures.ProEtaleCoefficients.SingleWContractibleCover
import WeilConjectures.ProEtaleCoefficients.SingleAffineHypercover

/-!
# Hypercovers by single w-contractible affines

## References

* Stacks Project, Tag 09A1, part (2)
* Tags 094K, 0DAV and 0DB2
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped Simplicial

namespace AlgebraicGeometry

/-- Hypercovers by single spectra of w-contractible rings.

The simplicial object is valued in `Over U`, so its augmentation is part of its data
and its matching limits are relative to `U`. In degree one the matching object is
`W₀ ×_U W₀`. Covering predicates are tested on the underlying arrows in `X.ProEt`.
-/
theorem exists_proetale_hypercover_single_affine
    (X : Scheme.{u}) (U : X.ProEt)
    (hUqc : CompactSpace U.left) (hUqs : QuasiSeparatedSpace U.left) :
    (∀ (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
      [∀ i, IsWContractibleRing (D i)], IsWContractibleRing (∀ i, D i)) ∧
      (∀ (V : X.ProEt), CompactSpace V.left →
        ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f)
          (g : @Scheme.ProEt.mk X _ f hf ⟶ V),
          IsWContractibleRing D ∧
            Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V) ∧
      ∃ (W : SimplicialObject (Over U)),
        (∀ (r : ℕ),
          ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
            IsWContractibleRing D ∧
              (W _⦋r⦌).left = @Scheme.ProEt.mk X _ f hf ∧
              (∀ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
                (φ : F ⟶ (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left)
                [Epi φ],
                ∃ s : (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left ⟶ F,
                  s ≫ φ = 𝟙 _)) ∧
        Presieve.singleton (W _⦋0⦌).hom ∈
          (Scheme.ProEt.precoverage X) U ∧
        (∀ (r : ℕ),
          ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
            (μ : W _⦋r + 1⦌ ⟶ c.pt),
            Nonempty (IsLimit c) ∧
              Presieve.singleton μ.left ∈ (Scheme.ProEt.precoverage X) c.pt.left ∧
              (∀ (a : SimplicialObject.ProperFaceCategory (r + 1)),
                μ ≫ c.π.app (Opposite.op a) = W.map a.obj.hom.op)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ D _ _
    exact isWContractibleRing_pi_of_finite I D
  · intro V hVqc
    exact exists_single_wContractible_affine_cover X V hVqc
  · obtain ⟨W, hterm, hzero, hmatching⟩ :=
      exists_single_affine_wContractible_hypercover X U hUqc hUqs
    refine ⟨W, ?_, hzero, hmatching⟩
    intro r
    obtain ⟨D, f, hf, hD, hW⟩ := hterm r
    refine ⟨D, f, hf, hD, hW, ?_⟩
    rw [hW]
    let := hD
    let := hf
    exact (Scheme.proetale_weakContractible_equivalences X (Scheme.ProEt.mk f)).2.2 D f

end AlgebraicGeometry
