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
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeProperties
import WeilConjectures.AlgebraicGeometry.ComplexLiftStrictMap
import WeilConjectures.AlgebraicGeometry.ComplexLiftConeCokernel

/-! # Acyclic enlargement with prescribed reduced cokernel

Source: Stacks Project, More on Algebra, Tag 0BCA.
-/

@[expose] public section

universe u v w w'

open CategoryTheory

namespace AlgebraicGeometry

private theorem exists_quasiIso_of_derived_iso
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (K L : CochainComplex D ℤ) [K.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, QuasiIso f := by
  obtain ⟨f, heq⟩ := CochainComplex.IsKProjective.exists_Q_map_eq K L e.hom
  refine ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso D f).mp ?_⟩
  rw [heq]
  infer_instance

private theorem reduced_term_projective
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R) (hP : Projective P) :
    Projective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P) := by
  exact (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).map_projective P hP

private theorem cokernel_bounded_above
    {D : Type*} [Category D] [Abelian D]
    {K A : CochainComplex D ℤ} (f : K ⟶ A)
    (hA : ∃ b : ℤ, A.IsStrictlyLE b) :
    ∃ b : ℤ, (Limits.cokernel f).IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := hA
  let := hb
  refine ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩
  intro i hi
  let π := (Limits.cokernel.π f).f i
  have : Epi π := inferInstance
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (cancel_epi π).mp
  exact (A.isZero_of_isStrictlyLE b i hi).eq_of_src _ _

/-- Construct an acyclic cone and a cokernel sequence for any acyclic lift of it.

Source: Stacks Project, More on Algebra, Tag 0BCA, cone and dotted-arrow paragraphs.
(blueprint: lem-sc-complex-lift-acyclic-enlargement).

Proof: Reduced class members are projective by extension of scalars. Represent the
supplied derived isomorphism by a quasi-isomorphism from E to the reduction of K₀,
using bounded projective complexes. Its mapping cone C is bounded above, acyclic,
and has terms reducing class members, by closure under binary sums. For any
bounded-above acyclic class complex A supplied with a reduction
isomorphism to C, regard C as an R-complex.
The quotient map A -> C is degreewise surjective and a quasi-isomorphism. Lift the
map K₀ -> C through it in the homotopy category, using K-projectivity of K₀. Lift
the correcting homotopy degreewise by projectivity and subtract its boundary.
This gives a strictly commuting map f : K₀ -> A whose reduction is the cone
inclusion. Take B to be the actual cokernel complex of f. The cokernel sequence is
right exact and B is bounded above. Extension of scalars preserves cokernels;
the cokernel of the cone inclusion is E[1]. This identifies the reduction of B
with E[1], and the reduced sequence splits in each degree. No injectivity of f
before reduction is asserted here; that is the separate class-splitting step. -/
theorem exists_complex_lift_acyclic_enlargement
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (K₀ : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hKbound : ∃ b : ℤ, K₀.IsStrictlyLE b)
    (hKterms : ∀ i : ℤ, K₀.X i ∈ Pclass)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P))
    (hderived : Nonempty (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀) ≅ DerivedCategory.Q.obj E)) :
    ∃ C : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ,
      (∃ b : ℤ, C.IsStrictlyLE b) ∧ C.Acyclic ∧
      (∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
        Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≅ C.X i)) ∧
      ∀ A : CochainComplex (ModuleCat.{max u v} R) ℤ,
        (∃ b : ℤ, A.IsStrictlyLE b) → A.Acyclic →
        (∀ i : ℤ, A.X i ∈ Pclass) →
        Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A ≅ C) →
        ∃ S : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ),
          S.X₁ = K₀ ∧ S.Exact ∧ Epi S.g ∧ S.X₂.Acyclic ∧
          (∀ i : ℤ, S.X₂.X i ∈ Pclass) ∧ (∃ b : ℤ, S.X₃.IsStrictlyLE b) ∧
          Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj S.X₃ ≅ E⟦(1 : ℤ)⟧) ∧
          ∀ i : ℤ, Nonempty
            (((S.map (HomologicalComplex.eval (ModuleCat.{max u v} R)
              (ComplexShape.up ℤ) i)).map
                (ModuleCat.extendScalars (Ideal.Quotient.mk I))).Splitting) := by
  classical
  obtain ⟨eD⟩ := hderived
  obtain ⟨bE, hbE⟩ := hEbound
  let := hbE
  have hEproj : ∀ i : ℤ, Projective (E.X i) := by
    intro i
    obtain ⟨P, hP, ⟨eP⟩⟩ := hEterms i
    exact Projective.of_iso eP.symm (reduced_term_projective R I P (hproj P hP))
  let := hEproj
  let := CochainComplex.isKProjective_of_projective E bE
  obtain ⟨δ, hδ⟩ := exists_quasiIso_of_derived_iso E _ eD.symm
  let := hδ
  obtain ⟨hCbound, hCacyclic, hCterms⟩ := complex_lift_cone_properties R I Pclass E K₀
    hclosed hKbound hKterms ⟨bE, hbE⟩ hEterms δ
  refine ⟨CochainComplex.mappingCone δ, hCbound, hCacyclic, hCterms, ?_⟩
  intro A hAbound hAacyclic hAterms hAC
  obtain ⟨eAC⟩ := hAC
  obtain ⟨f, hf⟩ := exists_complex_lift_strict_map R I K₀ A hKbound
    (fun i ↦ hproj (K₀.X i) (hKterms i)) _ hCacyclic eAC
    (CochainComplex.mappingCone.inr δ)
  obtain ⟨hBiso, hsplit⟩ := complex_lift_cone_cokernel R I E K₀ A δ eAC f hf
  refine ⟨ShortComplex.cokernelSequence f, rfl, ShortComplex.cokernelSequence_exact f,
    inferInstance, hAacyclic, hAterms, ?_, hBiso, hsplit⟩
  exact cokernel_bounded_above f hAbound

end AlgebraicGeometry
