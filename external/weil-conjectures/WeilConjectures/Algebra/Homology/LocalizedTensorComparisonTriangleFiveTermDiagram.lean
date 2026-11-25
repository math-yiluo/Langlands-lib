/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.Algebra.Homology.KFlatConeTrianglePresentation
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonConeRows
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare

/-! # Exact five-term diagrams for localized tensor comparison

Source: Stacks Project, Tags 06Y6, 0BYJ and 0DJA(1).
(blueprint: lem-pc-localized-tensor-comparison-triangle-five-term-diagram).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

-- Check the row projections on abstract arrows, before substituting homology maps.
private def homMk₄OfSquares {D : Type*} [Category* D]
    {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : D}
    (s₀ : X₀ ⟶ X₁) (s₁ : X₁ ⟶ X₂) (s₂ : X₂ ⟶ X₃) (s₃ : X₃ ⟶ X₄)
    (d₀ : Y₀ ⟶ Y₁) (d₁ : Y₁ ⟶ Y₂) (d₂ : Y₂ ⟶ Y₃) (d₃ : Y₃ ⟶ Y₄)
    (a₀ : X₀ ⟶ Y₀) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂)
    (a₃ : X₃ ⟶ Y₃) (a₄ : X₄ ⟶ Y₄)
    (w₀ : s₀ ≫ a₁ = a₀ ≫ d₀) (w₁ : s₁ ≫ a₂ = a₁ ≫ d₁)
    (w₂ : s₂ ≫ a₃ = a₂ ≫ d₂) (w₃ : s₃ ≫ a₄ = a₃ ≫ d₃) :
    ComposableArrows.mk₄ s₀ s₁ s₂ s₃ ⟶ ComposableArrows.mk₄ d₀ d₁ d₂ d₃ :=
  ComposableArrows.homMk₄ a₀ a₁ a₂ a₃ a₄ w₀ w₁ w₂ w₃

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison is a morphism of exact five-term cohomology sequences.
No component is assumed or asserted to be invertible.

Source: Stacks Project, Tag 06Y6 (exactness of derived tensor), Tag 0BYJ
(functorial associativity), and Tag 0DJA(1) (the tensor comparison).

Proof: use exists_kFlat_cone_triangle_presentation to present T as the
localization of the actual cone of a chain map f between K-flat P₁ and P₂.
This is a proved construction: apply a functorial flat resolution to a cone
presentation of T, use naturality of its augmentation and the triangle axiom,
and check K-flatness of the cone by tensor-cone acyclicity. Choose base-derived
models of P₁ tensor Q, P₂ tensor Q and cone(f) tensor Q locally in this
existential proof; no definition chooses data from mere existence.

The intermediate exists_localizedTensorComparison_cone_rows supplies the
exact localized source row and four comparison squares for this chain map.
Its target connecting map is fixed to homologyδOfTriangle of the concrete
triangle obtained by scalar extension and tensoring with N. The separate,
proved tensorConeTriangle_five_term_exact supplies target exactness: scalar
extension and tensor each identify the image of a cone with another cone;
three Mathlib homology exactness lemmas give the five-term exact row. This
argument needs no flatness or K-flatness on N. Combine the four squares using
ComposableArrows.homMk₄, with the five specified comparisons as its components.

Finally extract the three object isomorphisms from the cone-presentation
triangle isomorphism, and compose with the prescribed representative
isomorphisms. Apply exists_localizedTensorComparison_representative_square
five times (the first two representatives occur in two degrees). Each source
and target isomorphism and commuting square gives Arrow.isoMk. This theorem
already accepts arbitrary prescribed models, so no separate model-independence
step is needed in this transport. The rows remain those constructed for the
actual cone; their component arrows are identified with the requested ones.
No comparison-isomorphism hypothesis or five lemma is used. Zero rings, zero
maps, split cones, unbounded complexes and arbitrary degrees are included.
(blueprint: lem-pc-localized-tensor-comparison-triangle-five-term-diagram). -/
theorem exists_localizedTensorComparison_triangle_five_term_diagram
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ T.obj₃))
    (hUK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C)
    (U₁ U₂ : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU₁ : Nonempty (DerivedCategory.Q.obj U₁ ≅ T.obj₁))
    (hU₂ : Nonempty (DerivedCategory.Q.obj U₂ ≅ T.obj₂))
    (hK₁ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U₁ (curriedTensor _)).Acyclic)
    (hK₂ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U₂ (curriedTensor _)).Acyclic)
    (m₁ : BaseDerivedTensorCohomologyModel R A B (U₁ ⊗ Q) C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B (U₂ ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
      (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
        m.localizedComparison j ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
    ∃ (S D : ComposableArrows (ModuleCat.{u} C) 4) (φ : S ⟶ D),
      S.Exact ∧ D.Exact ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 0) ≅ Arrow.mk (cmp U₁ m₁ i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 1) ≅ Arrow.mk (cmp U₂ m₂ i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 2) ≅ Arrow.mk (cmp U mU i)) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 3) ≅ Arrow.mk (cmp U₁ m₁ (i + 1))) ∧
      Nonempty (Arrow.mk (ComposableArrows.app' φ 4) ≅ Arrow.mk (cmp U₂ m₂ (i + 1))) := by
  classical
  dsimp only
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
      m.localizedComparison j ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
  obtain ⟨P₁, P₂, f, hP₁, hP₂, hP₃, ⟨eT⟩⟩ :=
    exists_kFlat_cone_triangle_presentation A T hT
  let P₃ := CochainComplex.mappingCone f
  obtain ⟨mP₁⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (P₁ ⊗ Q) C
  obtain ⟨mP₂⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (P₂ ⊗ Q) C
  obtain ⟨mP₃⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (P₃ ⊗ Q) C
  obtain ⟨s₀, s₁, s₂, s₃, hS, w₀, w₁, w₂, w₃⟩ :=
    exists_localizedTensorComparison_cone_rows R A B C Q N t hC
      P₁ P₂ f mP₁ mP₂ mP₃ i
  let d₂ := CochainComplex.homologyδOfTriangle
    (tensorConeTriangle
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))) f N) i (i + 1)
  let S := ComposableArrows.mk₄ s₀ s₁ s₂ s₃
  let D := ComposableArrows.mk₄
    (HomologicalComplex.homologyMap (F.map f ▷ N) i)
    (HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f) ▷ N) i)
    d₂ (HomologicalComplex.homologyMap (F.map f ▷ N) (i + 1))
  have hD : D.Exact := tensorConeTriangle_five_term_exact
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))) f N i
  let φ : S ⟶ D := homMk₄OfSquares s₀ s₁ s₂ s₃
    (HomologicalComplex.homologyMap (F.map f ▷ N) i)
    (HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f) ▷ N) i)
    d₂ (HomologicalComplex.homologyMap (F.map f ▷ N) (i + 1))
    (cmp P₁ mP₁ i) (cmp P₂ mP₂ i) (cmp P₃ mP₃ i)
    (cmp P₁ mP₁ (i + 1)) (cmp P₂ mP₂ (i + 1)) w₀ w₁ w₂ w₃
  have transport (P V : CochainComplex (ModuleCat.{u} A) ℤ)
      (hP : ∀ W : CochainComplex (ModuleCat.{u} A) ℤ, W.Acyclic →
        (CochainComplex.mapBifunctor W P (curriedTensor _)).Acyclic)
      (hV : ∀ W : CochainComplex (ModuleCat.{u} A) ℤ, W.Acyclic →
        (CochainComplex.mapBifunctor W V (curriedTensor _)).Acyclic)
      (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj V)
      (mP : BaseDerivedTensorCohomologyModel R A B (P ⊗ Q) C)
      (mV : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) :
      Nonempty (Arrow.mk (cmp P mP j) ≅ Arrow.mk (cmp V mV j)) := by
    obtain ⟨es, ed, he⟩ := exists_localizedTensorComparison_representative_square
      R A B C Q N t hQ P V hP hV e mP mV j
    refine ⟨Arrow.isoMk es ed ?_⟩
    change es.hom ≫ cmp V mV j = cmp P mP j ≫ ed.hom
    dsimp only [cmp]
    simpa only [Category.assoc] using he.symm
  obtain ⟨eU₁⟩ := hU₁
  obtain ⟨eU₂⟩ := hU₂
  obtain ⟨eU⟩ := hU
  let e₁ : DerivedCategory.Q.obj P₁ ≅ DerivedCategory.Q.obj U₁ :=
    Pretriangulated.Triangle.π₁.mapIso eT ≪≫ eU₁.symm
  let e₂ : DerivedCategory.Q.obj P₂ ≅ DerivedCategory.Q.obj U₂ :=
    Pretriangulated.Triangle.π₂.mapIso eT ≪≫ eU₂.symm
  let e₃ : DerivedCategory.Q.obj P₃ ≅ DerivedCategory.Q.obj U :=
    Pretriangulated.Triangle.π₃.mapIso eT ≪≫ eU.symm
  refine ⟨S, D, φ, hS, hD, ?_, ?_, ?_, ?_, ?_⟩
  · exact transport P₁ U₁ hP₁ hK₁ e₁ mP₁ m₁ i
  · exact transport P₂ U₂ hP₂ hK₂ e₂ mP₂ m₂ i
  · exact transport P₃ U hP₃ hUK e₃ mP₃ mU i
  · exact transport P₁ U₁ hP₁ hK₁ e₁ mP₁ m₁ (i + 1)
  · exact transport P₂ U₂ hP₂ hK₂ e₂ mP₂ m₂ (i + 1)

end ModuleCat
