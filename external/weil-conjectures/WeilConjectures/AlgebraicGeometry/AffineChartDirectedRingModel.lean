/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Maps

import WeilConjectures.AlgebraicGeometry.AffineOpenDirectedRingSystem
import WeilConjectures.AlgebraicGeometry.AffineChartTensorComparison

/-!
# Directed ring models of base changes of an affine chart

Source: Stacks Project, Limits, Tag 07RP (affine reduction), Tags 01YX and 01YW.
(blueprint: lem-weil-pbc-affine-chart-directed-ring-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem etale_iff_of_chart_factorization
    {X Y Z X' Y' : Scheme.{u}} (g : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion j]
    (q : X ⟶ Z) (h : g ≫ j = q) (p : X' ⟶ Y')
    (e : Arrow.mk g ≅ Arrow.mk p) : Etale q ↔ Etale p := by
  rw [← h]
  exact (MorphismProperty.postcomp_iff (W := @Etale) (W' := @Etale)
    g j inferInstance).trans (MorphismProperty.arrow_mk_iso_iff (P := @Etale) e)

/-- One affine triple has a finitely presented ring model over the upper tail.
The model identifies étaleness at the limit, and étaleness at a stage implies
étaleness of the original chart at that stage.

Source: Stacks Project, Limits, Tag 07RP, affine reduction; Tags 01YX and 01YW;
Schemes, Tags 01JR and 01I4; Morphisms, Tags 01TQ and 02GJ.
(blueprint: lem-weil-pbc-affine-chart-directed-ring-model).

Proof: Let J be the upper tail of I above i₀. For i in J take the affine open
Wᵢ = (Sᵢ → Sᵢ₀)⁻¹(W) and let F(i) = Γ(Wᵢ). The transition maps define F
covariantly. Its initial ring F(i₀) canonically identifies with Γ(W). Take
B = Γ(V), C = Γ(U), with the algebra structures induced by the maps to W.
The restriction of f₀ gives an algebra map φ, finitely presented by
LocallyOfFinitePresentation.finitePresentation_appLE. The preimages of U and V
at any stage identify with U ×[W] Wᵢ and V ×[W] Wᵢ. By the affine pullback
formula these are spectra of F(i) ⊗ B and F(i) ⊗ C; the restricted map is
Spec(id ⊗ φ), as follows by checking both pullback projections. The restricted
limit cone over W is limiting, and Spec takes the ring colimit to this limit.
Hence the same formulas hold at the limit, and restriction/cancellation of the
open inclusion of the target chart proves the first étale equivalence. Given
étaleness of the ring-model map at i, the corresponding restricted chart map is
étale; composing with the open inclusion into Yᵢ gives the last assertion.
No compactness is used,
and no index at which a ring map becomes étale is asserted here. -/
theorem exists_affineChart_directedRingModel
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀)))
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (V : Y₀.left.Opens) (hV : IsAffineOpen V) (eV : V ≤ Y₀.hom ⁻¹ᵁ W)
    (U : X₀.left.Opens) (hU : IsAffineOpen U) (eU : U ≤ f₀.left ⁻¹ᵁ V)
    : ∃ (F : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u}) (B C : CommRingCat.{u})
      (aB : Algebra (F.obj ⟨i₀, le_rfl⟩) B)
      (aC : Algebra (F.obj ⟨i₀, le_rfl⟩) C),
      letI := aB
      letI := aC
      ∃ φ : B →ₐ[F.obj ⟨i₀, le_rfl⟩] C, φ.FinitePresentation ∧
        (letI : Algebra (F.obj ⟨i₀, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
          (colimit.ι F ⟨i₀, le_rfl⟩).hom.toAlgebra
         Etale (((pullback.fst X₀.hom (c.π.app (op i₀))) ⁻¹ᵁ U).ι ≫
           ((Over.pullback (c.π.app (op i₀))).map f₀).left) ↔
         Etale (Spec.map (CommRingCat.ofHom
           (Algebra.TensorProduct.map
             (AlgHom.id (F.obj ⟨i₀, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom))) ∧
        ∀ i : {i : I // i₀ ≤ i},
          (letI : Algebra (F.obj ⟨i₀, le_rfl⟩) (F.obj i) :=
            (F.map (homOfLE i.property)).hom.toAlgebra
           Etale (Spec.map (CommRingCat.ofHom
             (Algebra.TensorProduct.map (AlgHom.id (F.obj ⟨i₀, le_rfl⟩) (F.obj i))
               φ).toRingHom))) →
          Etale (((pullback.fst X₀.hom (D.map (homOfLE i.property).op)) ⁻¹ᵁ U).ι ≫
            ((Over.pullback (D.map (homOfLE i.property).op)).map f₀).left) := by
  obtain ⟨F, e0, hi, eL, hL⟩ :=
    exists_affineOpen_ringSystem_of_isLimit D c hc i₀ W hW
  obtain ⟨B, C, aB, aC, φ, hφ, hcomp⟩ :=
    exists_affineChart_tensorComparison X₀ Y₀ f₀ W hW V hV eV U hU eU
      (F.obj ⟨i₀, le_rfl⟩) e0
  let := aB
  let := aC
  refine ⟨F, B, C, aB, aC, φ, hφ, ?_, ?_⟩
  · let aL : Algebra (F.obj ⟨i₀, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F ⟨i₀, le_rfl⟩).hom.toAlgebra
    obtain ⟨g, hg, ⟨eg⟩⟩ := hcomp c.pt (c.π.app (op i₀)) (colimit F) aL eL hL
    exact etale_iff_of_chart_factorization g _ _ hg _ eg
  · intro i
    let ai : Algebra (F.obj ⟨i₀, le_rfl⟩) (F.obj i) :=
      (F.map (homOfLE i.property)).hom.toAlgebra
    obtain ⟨ei, hei⟩ := hi i
    obtain ⟨g, hg, ⟨eg⟩⟩ :=
      hcomp (D.obj (op i.val)) (D.map (homOfLE i.property).op) (F.obj i) ai ei hei
    exact (etale_iff_of_chart_factorization g _ _ hg _ eg).mpr

end AlgebraicGeometry
