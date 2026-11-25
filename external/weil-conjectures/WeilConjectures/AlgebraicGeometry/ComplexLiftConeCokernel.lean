/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # ComplexLiftConeCokernel

Source: Stacks Project, Tag 0BCA.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A strict lift of the cone inclusion has the expected reduced cokernel.

Source: Stacks Project, Tag 0BCA, cokernel paragraph.
(blueprint: lem-sc-complex-lift-cone-cokernel).

Proof: Extension of scalars is a left adjoint, so it preserves cokernels,
also on complexes, whose cokernels are computed degreewise. The equality hf
identifies the reduced first arrow, after the middle-object isomorphism e,
with the cone inclusion. Cokernel uniqueness gives an isomorphism from the
reduction of the actual cokernel of f to the cokernel of the cone inclusion.
The cone projection onto E[1] is that cokernel, since in each degree the cone
is the biproduct of the reduced K term and the shifted E term, and the
projection is the second projection. This isomorphism is compatible with
cokernel projections. Transport the biproduct retraction and section across
e and this cokernel isomorphism in each degree to obtain the splitting.
Neither acyclicity nor injectivity of f over R is needed for this argument. -/
theorem complex_lift_cone_cokernel
    (R : Type u) [CommRing R] (I : Ideal R)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (K A : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (δ : E ⟶ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (e : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ≅ CochainComplex.mappingCone δ)
    (f : K ⟶ A)
    (hf : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ e.hom = CochainComplex.mappingCone.inr δ) :
    Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (Limits.cokernel f) ≅ E⟦(1 : ℤ)⟧) ∧
    ∀ i : ℤ, Nonempty
      ((((ShortComplex.cokernelSequence f).map
        (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i)).map
          (ModuleCat.extendScalars (Ideal.Quotient.mk I))).Splitting) := by
  classical
  let D := ModuleCat.{max u v} (R ⧸ I)
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let := Functor.additive_of_preservesBinaryBiproducts F
  let T := CochainComplex.mappingCone.triangleRotateShortComplex δ
  have hT : T.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun i ↦ (CochainComplex.mappingCone.triangleRotateShortComplexSplitting δ i).shortExact)
  let := hT.epi_g
  let ec : Limits.cokernel T.f ≅ T.X₃ :=
    Limits.IsColimit.coconePointUniqueUpToIso (Limits.cokernelIsCokernel T.f)
      hT.gIsCokernel
  let em : Limits.cokernel (G.map f) ≅ Limits.cokernel T.f :=
    Limits.cokernel.mapIso (G.map f) T.f (Iso.refl _) e (by
      change G.map f ≫ e.hom = 𝟙 _ ≫ CochainComplex.mappingCone.inr δ
      simpa only [Category.id_comp] using hf)
  let eB : G.obj (Limits.cokernel f) ≅ E⟦(1 : ℤ)⟧ :=
    Limits.PreservesCokernel.iso G f ≪≫ em ≪≫ ec
  have hcomm : G.map (Limits.cokernel.π f) ≫ eB.hom = e.hom ≫ T.g := by
    dsimp [eB, em, ec]
    rw [← Category.assoc, Limits.PreservesCokernel.π_iso_hom]
    simp only [Category.assoc,
      Limits.cokernel.π_desc_assoc]
    congr 1
    exact Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.cokernelIsCokernel T.f) hT.gIsCokernel Limits.WalkingParallelPair.one
  let eS : (ShortComplex.cokernelSequence f).map G ≅ T :=
    ShortComplex.isoMk (Iso.refl _) e eB
      (by simpa [T, G] using hf.symm) (by simpa [G] using hcomm.symm)
  refine ⟨⟨eB⟩, ?_⟩
  intro i
  have σ := (CochainComplex.mappingCone.triangleRotateShortComplexSplitting δ i).ofIso
    (((HomologicalComplex.eval D (ComplexShape.up ℤ) i).mapShortComplex).mapIso
      eS.symm)
  exact ⟨σ⟩


end AlgebraicGeometry
