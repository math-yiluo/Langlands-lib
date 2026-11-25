/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.RightAdjointTensorComparisonProjection
import WeilConjectures.AlgebraicGeometry.RightAdjointTensorComparisonComponents

/-! # The pinned projection isomorphisms yield a natural right-adjoint tensor comparison.

Source: Stacks Project, Tag 0A9U.
(blueprint: lem-sc-right-adjoint-tensor-comparison-natural).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The pinned projection isomorphisms yield a natural right-adjoint tensor comparison.
Source: Stacks Project, Duality for Schemes, Section 48.8, equation (48.8.0.1),
and Tag 0A9U, first two sentences of proof.
(blueprint: lem-sc-right-adjoint-tensor-comparison-natural).

Proof. A proper map is quasi-compact and quasi-separated, so the unbounded
quasi-coherent projection formula applies to K and c(O_Y). Its canonical map is
exactly the pullback-adjunction mate of the inverse monoidal comparison followed
by the counit. Invert this map to obtain pf; the required equation pins its inverse
and hence makes pf unique. The formula is natural in K by naturality of the
monoidal comparison and pullback counit. Compose pf with tensoring the right
adjunction counit and the right unitor. Naturality of this composite and naturality
of adj.homEquiv yield a natural transformation with the displayed components.
The source functor is the actual lift of pullback followed by tensorRight, justified
by hTensor. No invertibility of this right-adjoint comparison is asserted. This
construction also applies to zero objects and does not require hsums. -/
theorem rightAdjointTensorComparison_natural
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c) :
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
    ∃ τ : F ⟶ c, ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by
  dsimp
  obtain ⟨pf, hpf⟩ := exists_rightAdjointTensorComparison_projection f hRf hO a c
  obtain ⟨τ, hτ⟩ := rightAdjointTensorComparison_components f hRf hO hTensor a c adj pf hpf
  refine ⟨τ, ?_⟩
  intro K
  refine ⟨pf K, hpf K, ?_⟩
  exact hτ K

end AlgebraicGeometry
