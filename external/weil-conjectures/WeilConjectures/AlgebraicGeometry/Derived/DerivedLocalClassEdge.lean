/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Derived.DerivedResolutionEdgeLocal
import WeilConjectures.AlgebraicGeometry.Derived.DerivedResolutionEdgeSingle
import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleDirectImageUnitIso

/-! # The natural local-class edge and its single-complex normalization
Source: Stacks Project, cohomology.tex, Tags 0BKJ, 0D5X and 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Sheafifying the local Leray/class maps gives a natural module edge, normalized on
single complexes by the right-derived unit.
Source: Stacks Project, cohomology.tex, Tags 0BKJ and 0D5X (local classes and Leray),
and Tag 079W (the right-derived unit on the same resolution).
(blueprint: lem-weil-pbc-local-class-edge-single-normalization).

Proof: On a fixed K-injective resolution I of K, the local Leray comparison identifies
a local hypercohomology class with the same cocycle on the inverse-image open. Map this
cocycle to its class in the cohomology sheaf of I. Restriction and scalar multiplication
commute with the cycle inclusion and boundary quotient; the scalar on the inverse-image
open is restricted along g-sharp. Hence this is a morphism of presheaves of modules.
Sheafify it and use the fixed localHypercohomologySheafificationAt identification to
obtain e_K. The sheafification unit gives exactly the first displayed equation.
A derived morphism is represented by a map between K-injective resolutions. The cycle
and boundary quotient maps commute with that map, so the displayed local comparison is
natural; uniqueness of sheafification gives the second equation for e.
For M in degree q, choose a resolution r:M[-q] -> I concentrated in degrees at least q.
Left exactness of direct image identifies the kernel in the first resolution degree
with the direct image of M; hence the degree-q unit is an isomorphism.
The right-derived unit sends a section m to the cocycle r^q(m). Local Leray preserves
that cocycle and the local-class map sends it to its class. Transport along H^q(r)
identifies this with m. The single/homology isomorphisms on the source and target give
the third displayed equation. Since sheafification is unique, the calculation does not
depend on the particular resolution and agrees with the fixed resolution in the data
module. The argument is unchanged for q negative, the zero module, or an empty open.
No derived pullback, derived adjunction, or truncated counit is used in this construction. -/
theorem exists_topEdgeLocalClassEdge {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ) :
    let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
    let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
    ∃ e : ∀ K : schemeDerivedCategory T,
        HS.obj ((schemeDerivedDirectImage g).obj K) ⟶
          (Scheme.Modules.pushforward g).obj (HT.obj K),
      (∀ (K : schemeDerivedCategory T) (V : (TopologicalSpace.Opens S)ᵒᵖ),
        (RingedSpace.topEdgeLocalClass S.toRingedSpace q
          ((schemeDerivedDirectImage g).obj K)).app V ≫
            ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map (e K)).hom.app V =
          (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
            (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V) ∧
      (∀ {K K' : schemeDerivedCategory T} (k : K ⟶ K'),
        HS.map ((schemeDerivedDirectImage g).map k) ≫ e K' =
          e K ≫ (Scheme.Modules.pushforward g).map (HT.map k)) ∧
      (∀ M : T.Modules,
        IsIso (HS.map (topEdgeSingleDirectImageMap g q M)) ∧
        HS.map (topEdgeSingleDirectImageMap g q M) ≫
            e ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).hom.app
              ((Scheme.Modules.pushforward g).obj M) ≫
            (Scheme.Modules.pushforward g).map
              ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).inv.app M)) := by
  refine ⟨resolutionLocalClassEdge g q, ?_, ?_, ?_⟩
  · exact resolutionLocalClassEdge_local g q
  · intro K K' k
    exact resolutionLocalClassEdge_naturality g q k
  · intro M
    exact ⟨topEdgeSingleDirectImageMap_isIso_homology g q M,
      resolutionLocalClassEdge_single g q M⟩

end AlgebraicGeometry
