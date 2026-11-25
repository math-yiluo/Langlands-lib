/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxClosure
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxEdgeIdentifications

/-! # Resolving model edge squares

Source: Stacks Project, Tags 07A4 and 0G7E; the corresponding explicit
representative calculation of the resolving constraint diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- The nested resolving models, and the six edge squares.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E; Steps 1–7 of
lem-pd-section-resolving-oplax-constraint-diagrams.

Proof: apply K-flat tensor closure to P,Q and Q,H, then to their outer pairs.
Ringed-topos pullback preserves K-flatness and flat terms, so every listed pullback
is resolving. The specified tensor comparison and the resolution counit are
invertible on these models; tensoring and composing them proves invertibility of
each vertex. For the source associator use the normalized associator equation for
qTensor and naturality of the resolution counit. For the two outer splitting edges,
use naturality of μ along modelTensor in the unresolved tensor input, then apply
the assumed representative equation to P,Q⊗H and P⊗Q,H. For the inner splitting
edges apply that equation to Q,H and P,Q, respectively, then use naturality of the
target modelTensor. Bifunctoriality of tensor identifies the resulting composites
with the prescribed vertices. The target associator square follows from its
naturality in the three resolution counits and the normalized target qTensor
associator equation. These calculations use the same vertex map on both adjacent
edges and apply to arbitrary integer-indexed direct-sum totals.
(auxiliary; not a blueprint node). -/
theorem section_resolving_oplax_model_edges {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    ∀ P Q H : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      ResolvingClosure Λ f P.obj Q.obj H.obj ∧
        SectionEdges Λ f μ P.obj Q.obj H.obj := by
  intro P Q H
  exact ⟨section_resolving_oplax_closure Λ f P.obj Q.obj H.obj
      P.property Q.property H.property,
    section_resolving_oplax_edge_identifications Λ f μ v h P.obj Q.obj H.obj⟩

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
