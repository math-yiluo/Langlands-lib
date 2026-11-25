/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonTriangleFiveTermDiagram
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

/-- A cochain representative with the explicit acyclic-tensor characterization of K-flatness.
Source: Stacks Project, Tag 06Y6, using the source library's functorial flat resolution.
Apply its reduced resolution to a preimage of X, then compose the localized augmentation
with the preimage isomorphism. The homotopy quotient characterization gives acyclic tensor
preservation. This helper is proved without any postponed statement.
(blueprint: lem-pc-localized-tensor-comparison-closure-triangles-core). -/
private theorem exists_kFlat_representative
    (A : Type u) [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    ∃ U : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj U ≅ X) ∧
      ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic := by
  classical
  have (M : ModuleCat.{u} A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let E := DerivedCategory.Q.objPreimage X
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  let U := Λ.resolutionFunctor.obj E
  let s := Λ.resolutionNatTrans.app E
  have hs : QuasiIso s := inferInstance
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat A) s).2 hs
  have hU := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le E
  refine ⟨U, ⟨asIso (DerivedCategory.Q.map s) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩, ?_⟩
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hU
  intro V hV
  have hV' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic V).2 hV
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V U (curriedTensor _))).1 (hU _ hV').2

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The fixed-representative and fixed-model step in the triangle closure argument.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: tensor the distinguished triangle with the K-flat representative and apply the
base-derived tensor model.  The resulting source and target long exact cohomology
sequences are connected by the canonical comparison maps.  Flatness of C over
A tensor_R B makes extension exact.  Naturality, including the connecting maps and
shifts, gives a morphism of exact sequences; the five lemma at the chosen degree
proves the displayed comparison is an isomorphism.  The construction is independent
of the chosen representative and model by the counit and associator identities.
(blueprint: lem-pc-localized-tensor-comparison-closure-triangles-core). -/
theorem localizedTensorComparisonProperty_triangle_core
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h1 : localizedTensorComparisonProperty R A B C Q N t T.obj₁)
    (h2 : localizedTensorComparisonProperty R A B C Q N t T.obj₂)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ T.obj₃))
    (hUK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  obtain ⟨U₁, hU₁, hK₁⟩ := exists_kFlat_representative A T.obj₁
  obtain ⟨U₂, hU₂, hK₂⟩ := exists_kFlat_representative A T.obj₂
  obtain ⟨m₁⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (U₁ ⊗ Q) C
  obtain ⟨m₂⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (U₂ ⊗ Q) C
  obtain ⟨S, D, φ, hS, hD, ⟨e₀⟩, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, ⟨e₄⟩⟩ :=
    exists_localizedTensorComparison_triangle_five_term_diagram
      R A B C Q N t hC hQ T hT U hU hUK mU
        U₁ U₂ hU₁ hU₂ hK₁ hK₂ m₁ m₂ i
  have h₀ : IsIso (ComposableArrows.app' φ 0) :=
    (Arrow.isIso_iff_isIso_of_isIso e₀.hom).2 (h1 U₁ hU₁ hK₁ m₁ i)
  have h₁ : IsIso (ComposableArrows.app' φ 1) :=
    (Arrow.isIso_iff_isIso_of_isIso e₁.hom).2 (h2 U₂ hU₂ hK₂ m₂ i)
  have h₃ : IsIso (ComposableArrows.app' φ 3) :=
    (Arrow.isIso_iff_isIso_of_isIso e₃.hom).2 (h1 U₁ hU₁ hK₁ m₁ (i + 1))
  have h₄ : IsIso (ComposableArrows.app' φ 4) :=
    (Arrow.isIso_iff_isIso_of_isIso e₄.hom).2 (h2 U₂ hU₂ hK₂ m₂ (i + 1))
  have h₂ : IsIso (ComposableArrows.app' φ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hS hD φ
      inferInstance h₁ h₃ inferInstance
  exact (Arrow.isIso_iff_isIso_of_isIso e₂.hom).1 h₂

end ModuleCat
