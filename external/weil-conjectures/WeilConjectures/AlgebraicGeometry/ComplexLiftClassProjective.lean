/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.AcyclicLift
import WeilConjectures.AlgebraicGeometry.ComplexLiftAcyclicEnlargement
import WeilConjectures.AlgebraicGeometry.ProjectiveClassReducedSplitting

/-!
# Lifting a derived complex for a projective class

Source: Stacks Project, More on Algebra, Lemma 15.75.2 (Tag 0BCA)
(blueprint: lem-sc-complex-lift-class-projective).
-/

@[expose] public section

universe u v w w'

open CategoryTheory

namespace AlgebraicGeometry

/-- Stacks Project, More on Algebra, Tag 0BCA, lemma-lift-complex
(blueprint: lem-sc-complex-lift-class-projective).

Reduction is Mathlib's extension of scalars to `R ⧸ I`, including the differential.
The class condition is expressed for any model of a binary direct sum. The hypothesis
on the derived reduction is included in `hK`: a bounded-above projective representative
computes derived tensor product by ordinary termwise extension of scalars.

Proof:
1. Choose the representative in (5). By (1) its terms are projective, hence flat.
   Apply `lem-pc-module-bounded-flat-kflat` and `lem-pur-derived-change-of-rings`
   to compute derived reduction. By (4), E is bounded above and projective; use
   `lem-pc-ring-derived-map-representative` to represent the derived isomorphism
   by a quasi-isomorphism from E to the reduced representative.
2. Its cone C is bounded above and acyclic. Each term is a sum of two reductions,
   hence a reduction of a class member by (2).
3. Apply `lem-sc-complex-lift-acyclic-projective` to lift C to an acyclic class
   complex A with a termwise surjective reduction map to C.
4. Use `lem-pc-ring-derived-map-representative` to lift the cone inclusion to a map
   from the representative to A up to homotopy. Lift the homotopy through the
   termwise surjection by projectivity and subtract its boundary to obtain strict
   commutation. Its reduction is a split injection with class-reduction cokernel.
5. Such a map between class members is split injective: lift the projection onto
   the reduced cokernel to a class member by projectivity. By (3) it is surjective
   and splits. Its kernel is in the class by (2). The projection of the original
   map onto this kernel is an isomorphism modulo I, hence surjective by (3),
   and splits by (1). Its kernel T is in the class by (2) and has zero reduction.
   Zero is in the class as a summand; (3) applied to zero to T gives T = 0.
6. The cokernel complex Q is bounded above with class terms. Since A is acyclic,
   Q shifted by -1 represents K. The termwise split sequence remains exact after
   reduction; its cokernel is E shifted by 1, so Q shifted by -1 reduces to E
   as a complex, with all differentials respected. -/
theorem complex_lift_class_projective
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hsurj : ∀ (P₁ P₂ : ModuleCat.{max u v} R) (f : P₁ ⟶ P₂),
      P₁ ∈ Pclass → P₂ ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P))
    (hK : ∃ K₀ : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, K₀.IsStrictlyLE b) ∧ (∀ i : ℤ, K₀.X i ∈ Pclass) ∧
      Nonempty (DerivedCategory.Q.obj K₀ ≅ K) ∧
      Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) ≅ DerivedCategory.Q.obj E)) :
    ∃ P₀ : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, P₀.IsStrictlyLE b) ∧ (∀ i : ℤ, P₀.X i ∈ Pclass) ∧
      Nonempty (DerivedCategory.Q.obj P₀ ≅ K) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀ ≅ E) := by
  obtain ⟨K₀, hKbound, hKterms, ⟨eK⟩, hderived⟩ := hK
  obtain ⟨C, hCbound, hCacyclic, hCterms, henlarge⟩ :=
    exists_complex_lift_acyclic_enlargement R I Pclass E hproj hclosed
      K₀ hKbound hKterms hEbound hEterms hderived
  have hsummand : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      P₁ ∈ Pclass → P₁₂ ∈ Pclass →
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) → P₂ ∈ Pclass := by
    intro P₁ P₂ P₁₂ h₁ h₁₂ e
    exact ((hclosed P₁ P₂ P₁₂ e).1 ⟨h₁, h₁₂⟩).2
  obtain ⟨A, hAbound, hAacyclic, hAterms, eA⟩ :=
    CochainComplex.exists_acyclic_lift_mod_ideal R I (fun P ↦ P ∈ Pclass)
      hproj hsummand hsurj C hCbound hCacyclic hCterms
  obtain ⟨S, hfirst, hexact, hepi, hacyclic, hmiddle, hbound, ⟨eE⟩, hsplit⟩ :=
    henlarge A hAbound hAacyclic hAterms eA
  have hdegree (i : ℤ) :
      (S.map (HomologicalComplex.eval _ _ i)).ShortExact ∧ S.X₃.X i ∈ Pclass := by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hEterms (i + 1)
    exact projective_class_reduced_splitting R I Pclass hproj hclosed hsurj
      (S.map (HomologicalComplex.eval _ _ i))
      (hexact.map (HomologicalComplex.eval _ _ i))
      (by exact (HomologicalComplex.eval _ _ i).map_epi S.g)
      (by change S.X₁.X i ∈ Pclass; rw [hfirst]; exact hKterms i)
      (hmiddle i) (hsplit i)
      ⟨P, hP, ⟨(HomologicalComplex.eval _ _ i).mapIso eE ≪≫ eP⟩⟩
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact S (fun i ↦ (hdegree i).1)
  have hzero : Limits.IsZero (DerivedCategory.Q.obj S.X₂) := by
    let : Zero (CochainComplex (ModuleCat.{max u v} R) ℤ) := Limits.HasZeroObject.zero' _
    have hq : QuasiIso (0 : (0 : CochainComplex (ModuleCat.{max u v} R) ℤ) ⟶ S.X₂) := by
      constructor
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        (HomologicalComplex.ExactAt.of_isZero
          ((HomologicalComplex.eval _ _ i).map_isZero (Limits.isZero_zero _)))).2 (hacyclic i)
    exact (DerivedCategory.Q.map_isZero (Limits.isZero_zero _)).of_iso
      (asIso (DerivedCategory.Q.map (0 : (0 : CochainComplex
        (ModuleCat.{max u v} R) ℤ) ⟶ S.X₂))).symm
  have hδ : IsIso (DerivedCategory.triangleOfSESδ hS) :=
    ((DerivedCategory.triangleOfSES hS).isZero₂_iff_isIso₃
      (DerivedCategory.triangleOfSES_distinguished hS)).1 hzero
  let eδ : DerivedCategory.Q.obj S.X₃ ≅ (DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
    asIso (DerivedCategory.triangleOfSESδ hS)
  let e₀ : DerivedCategory.Q.obj (S.X₃⟦(-1 : ℤ)⟧) ≅ K :=
    (DerivedCategory.Q.commShiftIso (-1)).app S.X₃ ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso eδ ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).app
        (DerivedCategory.Q.obj S.X₁) ≪≫
      DerivedCategory.Q.mapIso (eqToIso hfirst) ≪≫ eK
  refine ⟨S.X₃⟦(-1 : ℤ)⟧, ?_, ?_, ⟨e₀⟩, ?_⟩
  · obtain ⟨b, hb⟩ := hbound
    exact ⟨b + 1, S.X₃.isStrictlyLE_shift b (-1) (b + 1) (by omega)⟩
  · intro i
    exact (hdegree (i + -1)).2
  · let : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
    let F := (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    exact ⟨(F.commShiftIso (-1)).app S.X₃ ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso eE ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (by decide)).app E⟩

end AlgebraicGeometry
