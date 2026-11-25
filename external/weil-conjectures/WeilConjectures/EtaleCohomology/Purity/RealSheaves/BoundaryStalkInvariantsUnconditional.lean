/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants

/-!
# Boundary stalks of direct images of lisse Weil sheaves

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected, and `ℱ` a lisse Weil sheaf on `U₀` with Weil fundamental
representation `(V, ρ)`. At every boundary point `z` with closed point `x`, the boundary stalk
`(j_* ℱ)_x̄` is the module of inertia invariants `V ^ (I_z)`, the Frobenius of the stalk
corresponding to the residue Frobenius lift `ρ (Frob_z)`
(`exists_equivalence_isLisse_stalk_directImage_boundaryStalk_eq_invariants`).
This is blueprint `lemma-boundary-stalk--1` (subsection `lemma-boundary-stalk--2`): it combines
the existence of strictly henselian neighbourhoods of boundary points
(`AlgebraicGeometry.WeilGroup.exists_boundaryNeighbourhood_conj`) with the computation of the
boundary stalk through such a neighbourhood
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_stalk_directImage_boundaryStalk_of_conj`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale WeilSheaf

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [IsIntegral C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [Smooth (C ↘ Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U] [j.IsOver (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]
include τ GC in
/-- Blueprint `lemma-boundary-stalk--1` (subsection `lemma-boundary-stalk--2`), together with
`definition-weil-representation--1`.

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, `U₀`
geometrically connected, with the boundary datum of actual inertia groups and residue Frobenius
lifts (`AlgebraicGeometry.WeilGroup.boundaryDatum`). There is a lisse sheaf–representation
equivalence `ℱ ↦ (V, ρ)` for `W(U₀)`, identifying the stalk `ℱ_x̄` with its local Frobenius with
`V` with `ρ (Frob_x)` at the closed points of `U₀`, such that at every boundary point `z` with
closed point `x` the boundary stalk `(j_* ℱ)_x̄` is isomorphic to the inertia invariants
`V ^ (I_z)`, the Frobenius of the stalk corresponding to the residue Frobenius lift `ρ (Frob_z)`.
-/
theorem exists_equivalence_isLisse_stalk_directImage_boundaryStalk_eq_invariants :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
          (x : U.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ
            ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
        (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
        ∃ f : (((directImage j).obj F.obj).stalk x).carrier ≃ₗ[PadicAlgCl l]
            (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
              (e.functor.obj F).obj.ρ z,
          ∀ v, (f ((((directImage j).obj F.obj).stalk x).frobenius v) :
              (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ ((boundaryDatum (p := C ↘ Spec (.of K)) j sU GU
              (comp_over j _) τ GC).residueFrobenius z) (f v) :=
  exists_equivalence_isLisse_stalk_directImage_boundaryStalk_of_conj j sU GU τ GC
    fun z x hx ↦ exists_boundaryNeighbourhood_conj j sU GU τ GC z x hx

end AlgebraicGeometry.WeilGroup
