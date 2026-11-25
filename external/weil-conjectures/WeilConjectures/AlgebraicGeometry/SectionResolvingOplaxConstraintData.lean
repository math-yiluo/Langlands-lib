/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.SectionKFlatTensorComparison
public import WeilConjectures.AlgebraicGeometry.SectionOplaxTotalComparison
public import WeilConjectures.Topology.ProfiniteCondensedRing

/-! # Fixed data for resolving oplax constraint diagrams

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E; agent refinement
of the representative-square constraint computation
(auxiliary; not a blueprint node).

The generic diagram expressions below are specialized to the fixed section tensor,
localization and resolution comparisons. They introduce no chosen maps or replacement
operations. Vertex maps point from derived vertices to localized cochain models and
are precisely the inverses of the C_i in the node's proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

section Diagram
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B))

/-- The inverse of the nested left representative map.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def leftModel (P Q H : A) :=
  (s P Q ⊗ₘ 𝟙 (q.obj H)) ≫ s (P ⊗ Q) H

/-- The inverse of the nested right representative map.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def rightModel (P Q H : A) :=
  (𝟙 (q.obj P) ⊗ₘ s Q H) ≫ s P (Q ⊗ H)

/-- The inverse of d: L of the inverse representative comparison followed by epsilon.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def pairModel (P Q : A) := L.map (s P Q) ≫ ε.app (P ⊗ Q)

/-- The prescribed comparison C_0 inverse at associativity vertex 0.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex0 (P Q H : A) :=
  L.map (leftModel q s P Q H) ≫ ε.app ((P ⊗ Q) ⊗ H)

/-- The prescribed comparison C_1 inverse at associativity vertex 1.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex1 (P Q H : A) :=
  L.map (rightModel q s P Q H) ≫ ε.app (P ⊗ (Q ⊗ H))

/-- The prescribed comparison C_2 inverse at associativity vertex 2.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex2 (P Q H : A) :=
  (ε.app P ⊗ₘ pairModel (F := F) (L := L) (q := q) (r := r) s ε Q H) ≫ t (F.obj P) (F.obj (Q ⊗ H))

/-- The prescribed comparison C_3 inverse at associativity vertex 3.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex3 (P Q H : A) :=
  (ε.app P ⊗ₘ (ε.app Q ⊗ₘ ε.app H)) ≫
    rightModel r t (F.obj P) (F.obj Q) (F.obj H)

/-- The prescribed comparison C_4 inverse at associativity vertex 4.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex4 (P Q H : A) :=
  (pairModel (F := F) (L := L) (q := q) (r := r) s ε P Q ⊗ₘ ε.app H) ≫ t (F.obj (P ⊗ Q)) (F.obj H)

/-- The prescribed comparison C_5 inverse at associativity vertex 5.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def vertex5 (P Q H : A) :=
  ((ε.app P ⊗ₘ ε.app Q) ⊗ₘ ε.app H) ≫
    leftModel r t (F.obj P) (F.obj Q) (F.obj H)

/-- Exactly the pair equation and regular-unit equation in the node.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def RepresentativeEquations (P : ObjectProperty A) : Prop :=
  (∀ A B : P.FullSubcategory,
    μ (q.obj A.obj) (q.obj B.obj) ≫ (ε.app A.obj ⊗ₘ ε.app B.obj) ≫
        t (F.obj A.obj) (F.obj B.obj) =
      pairModel (F := F) (L := L) (q := q) (r := r) s ε A.obj B.obj ≫ r.map (β A.obj B.obj)) ∧
  v = ε.app (𝟙_ A) ≫ r.map unit

/-- The path around the right-associated branch of the derived associator diagram.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def upperPath (P Q H : C) :=
  L.map (α_ P Q H).hom ≫ μ (P) (Q ⊗ H) ≫ L.obj P ◁ μ (Q) (H)

/-- The path around the left-associated branch of the derived associator diagram.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def lowerPath (P Q H : C) :=
  μ (P ⊗ Q) (H) ≫ μ (P) (Q) ▷ L.obj H ≫ (α_ (L.obj P) (L.obj Q) (L.obj H)).hom

/-- Each vertex comparison is invertible, so the same inverse is used on every edge.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def VertexInvertibility (P Q H : A) : Prop :=
  IsIso (vertex0 (F := F) (L := L) (q := q) (r := r) s ε P Q H) ∧
  IsIso (vertex1 (F := F) (L := L) (q := q) (r := r) s ε P Q H) ∧
  IsIso (vertex2 (F := F) (L := L) (q := q) (r := r) s t ε P Q H) ∧
  IsIso (vertex3 (F := F) (L := L) (q := q) (r := r) t ε P Q H) ∧
  IsIso (vertex4 (F := F) (L := L) (q := q) (r := r) s t ε P Q H) ∧
  IsIso (vertex5 (F := F) (L := L) (q := q) (r := r) t ε P Q H)

/-- All six edge squares with the specified comparison at each intermediate vertex.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def EdgeIdentification (P Q H : A) : Prop :=
  (L.map (α_ (q.obj P) (q.obj Q) (q.obj H)).hom ≫ vertex1 (F := F) (L := L) (q := q) (r := r) s
      ε P Q H =
    vertex0 (F := F) (L := L) (q := q) (r := r) s ε P Q H ≫ r.map (F.map (α_ P Q H).hom)) ∧
  (μ (q.obj P) (q.obj Q ⊗ q.obj H) ≫ vertex2 (F := F) (L := L) (q := q) (r := r) s t ε P Q H =
    vertex1 (F := F) (L := L) (q := q) (r := r) s ε P Q H ≫ r.map (β P (Q ⊗ H))) ∧
  (L.obj (q.obj P) ◁ μ (q.obj Q) (q.obj H) ≫ vertex3 (F := F) (L := L) (q := q) (r := r) t ε P Q H =
    vertex2 (F := F) (L := L) (q := q) (r := r) s t ε P Q H ≫ r.map (F.obj P ◁ β Q H)) ∧
  (μ (q.obj P ⊗ q.obj Q) (q.obj H) ≫ vertex4 (F := F) (L := L) (q := q) (r := r) s t ε P Q H =
    vertex0 (F := F) (L := L) (q := q) (r := r) s ε P Q H ≫ r.map (β (P ⊗ Q) H)) ∧
  (μ (q.obj P) (q.obj Q) ▷ L.obj (q.obj H) ≫ vertex5 (F := F) (L := L) (q := q) (r := r) t ε P Q H =
    vertex4 (F := F) (L := L) (q := q) (r := r) s t ε P Q H ≫ r.map (β P Q ▷ F.obj H)) ∧
  ((α_ (L.obj (q.obj P)) (L.obj (q.obj Q)) (L.obj (q.obj H))).hom ≫ vertex3 (F := F) (L := L)
      (q := q) (r := r) t ε P Q H =
    vertex5 (F := F) (L := L) (q := q) (r := r) t ε P Q H ≫ r.map ((α_ (F.obj P) (F.obj Q)
      (F.obj H)).hom))

/-- Both whole paths equal the localized displayed cochain composites, and commute.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def AssociativityPaths (P Q H : A) : Prop :=
  (upperPath L μ (q.obj P) (q.obj Q) (q.obj H) ≫ vertex3 (F := F) (L := L) (q := q) (r := r) t
      ε P Q H =
    vertex0 (F := F) (L := L) (q := q) (r := r) s ε P Q H ≫ r.map
      (F.map (α_ P Q H).hom ≫ β P (Q ⊗ H) ≫ F.obj P ◁ β Q H)) ∧
  (lowerPath L μ (q.obj P) (q.obj Q) (q.obj H) ≫ vertex3 (F := F) (L := L) (q := q) (r := r) t
      ε P Q H =
    vertex0 (F := F) (L := L) (q := q) (r := r) s ε P Q H ≫ r.map
      (β (P ⊗ Q) H ≫ β P Q ▷ F.obj H ≫ (α_ (F.obj P) (F.obj Q) (F.obj H)).hom)) ∧
  upperPath L μ (q.obj P) (q.obj Q) (q.obj H) =
    lowerPath L μ (q.obj P) (q.obj Q) (q.obj H)

/-- The regular left unitor with the fixed unit comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def regularLeft (M : C) := (eA.inv ▷ M) ≫ (λ_ M).hom

/-- The regular right unitor with the fixed unit comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def regularRight (M : C) := (M ◁ eA.inv) ≫ (ρ_ M).hom

/-- The second left-unit vertex comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def leftVertex1 (P : A) := (ε.app (𝟙_ A) ⊗ₘ ε.app P) ≫ t (F.obj (𝟙_ A)) (F.obj P)

/-- The third left-unit vertex comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def leftVertex2 (P : A) := (𝟙 (r.obj (𝟙_ B)) ⊗ₘ ε.app P) ≫ t (𝟙_ B) (F.obj P)

/-- The derived left-unit composite using the given v.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def leftUnitPath (M : C) :=
  μ (q.obj (𝟙_ A)) (M) ≫ v ▷ L.obj M ≫ regularLeft r eB (L.obj M)

/-- The second right-unit vertex comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def rightVertex1 (P : A) := (ε.app P ⊗ₘ ε.app (𝟙_ A)) ≫ t (F.obj P) (F.obj (𝟙_ A))

/-- The third right-unit vertex comparison.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def rightVertex2 (P : A) := (ε.app P ⊗ₘ 𝟙 (r.obj (𝟙_ B))) ≫ t (F.obj P) (𝟙_ B)

/-- The derived right-unit composite using the given v.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def rightUnitPath (M : C) :=
  μ (M) (q.obj (𝟙_ A)) ≫ L.obj M ◁ v ≫ regularRight r eB (L.obj M)

/-- Both unit edge squares and whole paths, with common outside comparisons.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def UnitIdentification (P : A) : Prop :=
  (IsIso (pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P)) ∧
  (IsIso (leftVertex1 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (ε.app P)) ∧
  (μ (q.obj (𝟙_ A)) (q.obj P) ≫ leftVertex1 (F := F) (L := L) (q := q) (r := r) t ε P =
      pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P ≫ r.map (β
      (𝟙_ A) P)) ∧
  ((v ▷ L.obj (q.obj P)) ≫ leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P = leftVertex1
      (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (unit ▷ F.obj P)) ∧
  (regularLeft r eB (L.obj (q.obj P)) ≫ ε.app P =
    leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (λ_ (F.obj P)).hom) ∧
  (leftUnitPath (L := L) (q := q) (r := r) eB μ v (q.obj P) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P ≫ r.map (β (𝟙_ A) P ≫ unit ▷
      F.obj P ≫ (λ_ (F.obj P)).hom)) ∧
  (L.map (regularLeft q eA (q.obj P)) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P ≫ r.map (F.map (λ_ P).hom)) ∧
  (leftUnitPath (L := L) (q := q) (r := r) eB μ v (q.obj P) = L.map (regularLeft q eA (q.obj P))) ∧
  (IsIso (pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A))) ∧
  (IsIso (rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (ε.app P)) ∧
  (μ (q.obj P) (q.obj (𝟙_ A)) ≫ rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P =
      pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A) ≫ r.map (β P
      (𝟙_ A))) ∧
  ((L.obj (q.obj P) ◁ v) ≫ rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P =
      rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (F.obj P ◁ unit)) ∧
  (regularRight r eB (L.obj (q.obj P)) ≫ ε.app P =
    rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (ρ_ (F.obj P)).hom) ∧
  (rightUnitPath (L := L) (q := q) (r := r) eB μ v (q.obj P) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A) ≫ r.map (β P (𝟙_ A) ≫ F.obj P ◁
      unit ≫ (ρ_ (F.obj P)).hom)) ∧
  (L.map (regularRight q eA (q.obj P)) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A) ≫ r.map (F.map (ρ_ P).hom)) ∧
  (rightUnitPath (L := L) (q := q) (r := r) eB μ v (q.obj P) = L.map (regularRight q eA (q.obj P)))

/-- Invertibility and edge squares for the regular units, before composing whole paths.
Source: Stacks 07A4, resolving-model unit calculation
(auxiliary; not a blueprint node). -/
def UnitEdgeIdentification (P : A) : Prop :=
  (IsIso (pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P)) ∧
  (IsIso (leftVertex1 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (ε.app P)) ∧
  (μ (q.obj (𝟙_ A)) (q.obj P) ≫ leftVertex1 (F := F) (L := L) (q := q) (r := r) t ε P =
      pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P ≫ r.map (β
      (𝟙_ A) P)) ∧
  ((v ▷ L.obj (q.obj P)) ≫ leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P = leftVertex1
      (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (unit ▷ F.obj P)) ∧
  (regularLeft r eB (L.obj (q.obj P)) ≫ ε.app P =
    leftVertex2 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (λ_ (F.obj P)).hom) ∧
  (L.map (regularLeft q eA (q.obj P)) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε (𝟙_ A) P ≫ r.map (F.map (λ_ P).hom)) ∧
  (IsIso (pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A))) ∧
  (IsIso (rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P)) ∧
  (IsIso (ε.app P)) ∧
  (μ (q.obj P) (q.obj (𝟙_ A)) ≫ rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P =
      pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A) ≫ r.map (β P
      (𝟙_ A))) ∧
  ((L.obj (q.obj P) ◁ v) ≫ rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P =
      rightVertex1 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (F.obj P ◁ unit)) ∧
  (regularRight r eB (L.obj (q.obj P)) ≫ ε.app P =
    rightVertex2 (F := F) (L := L) (q := q) (r := r) t ε P ≫ r.map (ρ_ (F.obj P)).hom) ∧
  (L.map (regularRight q eA (q.obj P)) ≫ ε.app P =
    pairModel (F := F) (L := L) (q := q) (r := r) s ε P (𝟙_ A) ≫ r.map (F.map (ρ_ P).hom))

end Diagram

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] tensorComparison qTensor totalComparison tensor

/-- The fixed tensor comparison with its normalized source and target types retained.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def modelTensor (T : Scheme.{u}) (P Q : CochainComplex (modules Λ T) ℤ) :
    (tensor Λ T).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (P ⊗ Q) :=
  (qTensor Λ T).app (P, Q)

attribute [local semireducible] tensor

/-- The specified localized regular-module isomorphism e.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
def regular (T : Scheme.{u}) :
    tensorUnit Λ T ≅ DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ T) ℤ)) :=
  sectionLocalizationComparison Λ T (𝟙_ (CochainComplex (internalModules Λ T) ℤ)) ≪≫
    DerivedCategory.Q.mapIso (totalUnitComparison Λ T)

/-- The fixed transported section derived monoidal structure, with no new choice.
Source: Stacks 07A4 and 0G7E, explicit resolving-model diagram computation
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def derivedMonoidal (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (modules Λ T)) :=
  transportedDerivedMonoidal Λ T

/-- The tensor transformation type for the fixed section derived tensor.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
abbrev SectionTensorArrow {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  tensor Λ Y ⋙ derivedPullback Λ f ⟶
    ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X

/-- Both nested totals, their constituent binary totals, and all their pullbacks resolve.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def ResolvingClosure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : CochainComplex (modules Λ Y) ℤ) : Prop :=
  (∀ A ∈ [P ⊗ Q, Q ⊗ H, (P ⊗ Q) ⊗ H, P ⊗ (Q ⊗ H)],
    KFlatSectionComparison.sectionResolving Λ Y A) ∧
  (∀ A ∈ [P, Q, H, P ⊗ Q, Q ⊗ H, (P ⊗ Q) ⊗ H, P ⊗ (Q ⊗ H)],
    KFlatSectionComparison.sectionResolving Λ X ((totalSectionPull Λ f).obj A))

/-- The RepresentativeEquations formula specialized to the fixed section models.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def SectionHypotheses {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    :=
  @RepresentativeEquations (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom
      (sectionTotalIso Λ f · · |>.hom) (sectionTotalUnit Λ f) (fun M N => μ.app (M, N)) v
      (KFlatSectionComparison.sectionResolving Λ Y)

/-- The VertexInvertibility formula specialized to the fixed section models.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def SectionVertices {X Y : Scheme.{u}} (f : X ⟶ Y)
    :=
  @VertexInvertibility (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom

/-- The EdgeIdentification formula specialized to the fixed section models.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def SectionEdges {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    :=
  @EdgeIdentification (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom
      (sectionTotalIso Λ f · · |>.hom) (fun M N => μ.app (M, N))

/-- The AssociativityPaths formula specialized to the fixed section models.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def SectionAssociativity {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    :=
  @AssociativityPaths (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom
      (sectionTotalIso Λ f · · |>.hom) (fun M N => μ.app (M, N))

/-- The UnitIdentification formula specialized to the fixed section models.
Source: Stacks 07A4 and 0G7E, prescribed resolving-model comparisons
(auxiliary; not a blueprint node). -/
def SectionUnits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    :=
  @UnitIdentification (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom
      (sectionTotalIso Λ f · · |>.hom) (sectionTotalUnit Λ f)
    (cast (by rfl) (regular Λ Y)) (cast (by rfl) (regular Λ X))
      (fun M N => μ.app (M, N)) v

/-- The unit edge squares specialized to the fixed section models.
Source: Stacks 07A4, resolving-model unit calculation
(auxiliary; not a blueprint node). -/
def SectionUnitEdges {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    :=
  @UnitEdgeIdentification (CochainComplex (modules Λ Y) ℤ) (CochainComplex (modules Λ X) ℤ)
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (modelTensor Λ Y) (modelTensor Λ X) (pullback Λ f).mapDerivedCategoryFactors.hom
      (sectionTotalIso Λ f · · |>.hom) (sectionTotalUnit Λ f)
    (cast (by rfl) (regular Λ Y)) (cast (by rfl) (regular Λ X))
      (fun M N => μ.app (M, N)) v

/-- The inverse fixed tensor comparison, retaining the transported tensor types.
Source: Stacks 07A4, fixed gamma/theta/e conjugation
(auxiliary; not a blueprint node). -/
def internalModelTensor (T : Scheme.{u})
    (M N : DerivedCategory (internalModules Λ T)) :
    (tensor Λ T).obj ((derivedEquivalence Λ T).functor.obj M,
      (derivedEquivalence Λ T).functor.obj N) ⟶
      (derivedEquivalence Λ T).functor.obj (M ⊗ N) :=
  (tensorComparison Λ T).inv.app (M, N)

/-- Internal natural tensor transformations for the final conditional clause.
Source: Stacks 07A4, fixed gamma/theta/e conjugation
(auxiliary; not a blueprint node). -/
abbrev InternalTensorArrow {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.postcompose₂.obj (internalDerivedPullback Λ f)).obj
        (CondensedRing.derivedTensor Λ Y) ⟶
    (((Functor.whiskeringLeft₂ _).obj (internalDerivedPullback Λ f)).obj
      (internalDerivedPullback Λ f)).obj (CondensedRing.derivedTensor Λ X)

/-- The RepresentativeEquations formula for the internal and section diagrams, with gamma/theta/e.
Source: Stacks 07A4, fixed gamma/theta/e conjugation
(auxiliary; not a blueprint node). -/
def Conjugation {X Y : Scheme.{u}} (f : X ⟶ Y) (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (δ : InternalTensorArrow Λ f)
    (w : (internalDerivedPullback Λ f).obj
        (𝟙_ (DerivedCategory (internalModules Λ Y))) ⟶
      𝟙_ (DerivedCategory (internalModules Λ X)))
    :=
  @RepresentativeEquations (DerivedCategory (internalModules Λ Y)) (DerivedCategory
      (internalModules Λ X))
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (internalDerivedPullback Λ f) (derivedPullback Λ f)
    (derivedEquivalence Λ Y).functor (derivedEquivalence Λ X).functor
    (internalModelTensor Λ Y) (internalModelTensor Λ X) (derivedPullComparison Λ f).inv (fun M
      N => (δ.app M).app N) w (fun M N => μ.app (M, N)) ((derivedPullback Λ f).map
      (cast (by rfl) (regular Λ Y).hom) ≫ v ≫ (cast (by rfl) (regular Λ X).inv)) ⊤

/-- The EdgeIdentification formula for the internal and section diagrams, with gamma/theta/e.
Source: Stacks 07A4, fixed gamma/theta/e conjugation
(auxiliary; not a blueprint node). -/
def InternalEdges {X Y : Scheme.{u}} (f : X ⟶ Y) (μ : SectionTensorArrow Λ f)
    (δ : InternalTensorArrow Λ f)
    :=
  @EdgeIdentification (DerivedCategory (internalModules Λ Y)) (DerivedCategory (internalModules
      Λ X))
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (internalDerivedPullback Λ f) (derivedPullback Λ f)
    (derivedEquivalence Λ Y).functor (derivedEquivalence Λ X).functor
    (internalModelTensor Λ Y) (internalModelTensor Λ X) (derivedPullComparison Λ f).inv (fun M
      N => (δ.app M).app N) (fun M N => μ.app (M, N))

/-- The UnitIdentification formula for the internal and section diagrams, with gamma/theta/e.
Source: Stacks 07A4, fixed gamma/theta/e conjugation
(auxiliary; not a blueprint node). -/
def InternalUnits {X Y : Scheme.{u}} (f : X ⟶ Y) (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (δ : InternalTensorArrow Λ f)
    (w : (internalDerivedPullback Λ f).obj
        (𝟙_ (DerivedCategory (internalModules Λ Y))) ⟶
      𝟙_ (DerivedCategory (internalModules Λ X)))
    :=
  @UnitIdentification (DerivedCategory (internalModules Λ Y)) (DerivedCategory (internalModules
      Λ X))
    (DerivedCategory (modules Λ Y)) (DerivedCategory (modules Λ X)) _ _ _ _ _ _
    (derivedMonoidal Λ Y) (derivedMonoidal Λ X)
    (internalDerivedPullback Λ f) (derivedPullback Λ f)
    (derivedEquivalence Λ Y).functor (derivedEquivalence Λ X).functor
    (internalModelTensor Λ Y) (internalModelTensor Λ X) (derivedPullComparison Λ f).inv (fun M
      N => (δ.app M).app N) w (Iso.refl _) (Iso.refl _) (fun M N => μ.app (M, N))
      ((derivedPullback Λ f).map (cast (by rfl) (regular Λ Y).hom) ≫
        v ≫ (cast (by rfl) (regular Λ X).inv))

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
