/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import WeilConjectures.Algebra.Homology.HomComplexProjections
/-! # Degreewise ordinary evaluation and coefficient compatibility
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- A small component interface keeps the projection witness out of coproduct rewriting.
def schemeOrdinaryEvaluationGradedComponent {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (p q n : ℤ) (h : q + p = n) :
    letI := SheafOfModules.monoidalCategory R
    (homComplex (R := R) P N).X p ⊗ P.X q ⟶ N.X n :=
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  (β_ ((homComplex (R := R) P N).X p) (P.X q)).hom ≫
    (SheafOfModules.tensorHomEquiv (R := R) (P.X q)
      ((homComplex (R := R) P N).X p) (N.X n)).symm
      ((Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R)))
        P N p q n h)

-- Evaluation into an arbitrary coefficient complex, defined by coproduct descent.
def schemeOrdinaryEvaluationGraded (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (n : ℤ) : (pullbackTensorTotal Y (homComplex (R := Y.sheaf) P N) P).X n ⟶ N.X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := homComplex (R := Y.sheaf) P N) (K₂ := P) (F := curriedTensor _)
    (c := .up ℤ) (j := n) (fun p q h ↦
      schemeOrdinaryEvaluationGradedComponent (C := Opens Y) (J := Opens.grothendieckTopology Y)
        Y.sheaf P N p q n (by change p + q = n at h; omega))

-- Inverse adjunction is natural in the coefficient; keep the projection abstract.
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_component_naturality {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A H B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (α : H ⟶ SheafOfModules.homObj A B') (π : H ⟶ SheafOfModules.homObj A B)
    (g : B ⟶ B') (h : α = π ≫ SheafOfModules.homObjMap (R := R) (𝟙 A) g) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (β_ H A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A H B').symm α =
      ((β_ H A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A H B).symm π) ≫ g := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  rw [Category.assoc]
  congr 1
  apply (SheafOfModules.tensorHomEquiv (R := R) A H B').injective
  simp only [Equiv.apply_symm_apply, SheafOfModules.tensorHomEquiv_comp_homObjMap]
  exact h

-- Descend the abstract component calculation before selecting any product witnesses.
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_graded_naturality {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P H H' N I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (φ : H ⟶ H')
    (π : ∀ (p q n : ℤ), q + p = n → (H.X p ⟶
      SheafOfModules.homObj (P.X q) (N.X n)))
    (π' : ∀ (p q n : ℤ), q + p = n → (H'.X p ⟶
      SheafOfModules.homObj (P.X q) (I.X n)))
    (g : N ⟶ I)
    (hπ : ∀ (p q n : ℤ) (h : q + p = n),
      φ.f p ≫ π' p q n h = π p q n h ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (P.X q)) (g.f n)) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    HomologicalComplex.mapBifunctorDesc
      (K₁ := H) (K₂ := P) (F := curriedTensor _) (c := .up ℤ)
      (j := n) (fun p q h ↦ (β_ ((H).X p) (P.X q)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (P.X q)
          ((H).X p) (I.X n)).symm
          (φ.f p ≫ π' p q n
            (by change p + q = n at h; omega))) =
    HomologicalComplex.mapBifunctorDesc
      (K₁ := H) (K₂ := P) (F := curriedTensor _) (c := .up ℤ)
      (j := n) (fun p q h ↦ (β_ ((H).X p) (P.X q)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (P.X q)
          ((H).X p) (N.X n)).symm
          (π p q n (by change p + q = n at h; omega))) ≫ g.f n := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq' : p + q = n := hpq
  simp only [HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  apply evaluation_component_naturality R
  exact hπ p q n (by omega)

set_option backward.isDefEq.respectTransparency.types false in
/-- Degreewise ordinary evaluation commutes with a map to the fixed coefficient resolution.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation localization proof step 2.
(blueprint: lem-pc-scheme-ordinary-evaluation-graded-augmentation).

Proof: Fix total degree n. Use coproduct extensionality for the total tensor,
so it suffices to compare the composites from each summand with indices p,q
satisfying p+q=n. The component formula for schemeTensorHomUncurry identifies
the left composite with symmetry followed by inverse tensor-Hom adjunction
of Hom(P,g)^p followed by the projection to Hom(P^q,I^n), where I is the
fixed resolution of N. The coefficient naturality formula for the Hom
projections, applied with the identity of P and g, replaces this composite
by the projection to Hom(P^q,N^n) followed by homObjMap(id,g^n).
Naturality of the tensor-Hom equivalence in its coefficient identifies its
inverse with inverse adjunction of the latter projection followed by g^n.
Associativity and the coproduct descent equation give precisely the right
composite, proving the degreewise equality. This uses no differential
compatibility or monicity; it is an equality of graded maps for arbitrary
P,N and any coefficient map g to the fixed resolution. If either complex
is zero, or the scheme is empty, the same coproduct equations still apply.
The evaluation maps are explicit coproduct descents of the fixed product
projections; no evaluation map is chosen from an existence assertion. -/
theorem schemeOrdinaryEvaluationGraded_augmentation (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (g : N ⟶ (schemeHomKInjectiveResolution Y).obj N) (n : ℤ) :
    (schemeTensorHomUncurry Y (homComplex (R := Y.sheaf) P N) P N
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map g)).f n =
        schemeOrdinaryEvaluationGraded Y P N n ≫ g.f n := by
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
  have hπ (p q n : ℤ) (h : q + p = n) :
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map g).f p ≫
          π P ((schemeHomKInjectiveResolution Y).obj N) p q n h =
        π P N p q n h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X q)) (g.f n) := by
    have h := (Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))).2.2
        P P N ((schemeHomKInjectiveResolution Y).obj N) (𝟙 P) g p q n h
    simpa only [op_id, (homComplexFunctor (R := Y.sheaf)).map_id,
      NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f] using h
  exact evaluation_graded_naturality Y.sheaf P (homComplex (R := Y.sheaf) P N)
    (homComplex (R := Y.sheaf) P ((schemeHomKInjectiveResolution Y).obj N)) N
    ((schemeHomKInjectiveResolution Y).obj N)
    (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map g) (π P N)
    (π P ((schemeHomKInjectiveResolution Y).obj N)) g hπ n
end AlgebraicGeometry
