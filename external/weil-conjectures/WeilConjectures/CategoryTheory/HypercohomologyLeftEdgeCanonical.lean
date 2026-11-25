/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
import WeilConjectures.CategoryTheory.HypercohomologyLeftEdgeNaturality
import WeilConjectures.CategoryTheory.HypercohomologyLeftEdgeSingle

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Canonical lift case of the hypercohomology left-edge cocycle equation.
Source: Stacks Project, derived.tex, Tag 015J; this is the representative
calculation for the canonical cycle lift.
(blueprint: lem-pc-hypercohomology-edge-cocycle-canonical)

The canonical lift is the map on cycles induced by left exactness.  The proof
uses a Cartan--Eilenberg resolution and computes the degree-zero representative
of the truncation edge; the resulting quotient is the image under `G` of the
cycles-to-homology quotient.  This is the fixed-lift special case of the
cocycle equation and is strictly simpler because no uniqueness argument for a
supplied lift is involved.
-/
theorem cochainHypercohomologyLeftEdge_canonical
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex B ℕ) (n : ℕ) :
    (let T := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
     let c := T.liftCycles (G.map (K.iCycles n)) (n + 1) (by simp)
       (by
         change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
         rw [← G.map_comp, K.iCycles_d, G.map_zero])
     c ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge K n =
       G.map (K.homologyπ n)) := by
  let S := (HomologicalComplex.single B (ComplexShape.up ℕ) n).obj (K.cycles n)
  let GS := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S
  let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let f : S ⟶ K := HomologicalComplex.mkHomFromSingle (K.iCycles n)
    (fun k _ ↦ K.iCycles_d n k)
  let a := GS.liftCycles
    (G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) n (K.cycles n)).inv)
    (n + 1) (by simp) (by
      change _ ≫ G.map (S.d n (n + 1)) = 0
      simp [S])
  let c := T.liftCycles (G.map (K.iCycles n)) (n + 1) (by simp)
    (by
      change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
      rw [← G.map_comp, K.iCycles_d, G.map_zero])
  have ha : a ≫ HomologicalComplex.cyclesMap
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map f) n = c := by
    apply (cancel_mono (T.iCycles n)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i]
    dsimp only [a, c]
    rw [GS.liftCycles_i_assoc, T.liftCycles_i]
    change G.map _ ≫ G.map (f.f n) = _
    rw [← G.map_comp]
    simp only [f, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  have hf :
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) n
        (K.cycles n)).inv ≫ HomologicalComplex.homologyMap f n = K.homologyπ n := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
      Category.assoc, HomologicalComplex.homologyπ_naturality]
    have hcyc :
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) n
          (K.cycles n)).inv ≫ HomologicalComplex.cyclesMap f n = 𝟙 (K.cycles n) := by
      apply (cancel_mono (K.iCycles n)).1
      rw [Category.assoc, HomologicalComplex.cyclesMap_i]
      dsimp only [f]
      rw [HomologicalComplex.mkHomFromSingle_f,
        HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
        Iso.inv_hom_id_assoc, Category.id_comp]
    rw [← Category.assoc, hcyc, Category.id_comp]
  have hn := cochainHypercohomologyLeftEdge_naturality G f n
  have hs := cochainHypercohomologyLeftEdge_single G (K.cycles n) n
  change c ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge K n = _
  rw [← ha, Category.assoc, ← HomologicalComplex.homologyπ_naturality_assoc,
    hn]
  have hs' : a ≫ GS.homologyπ n ≫ G.cochainHypercohomologyLeftEdge S n =
      G.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) n
        (K.cycles n)).inv := by
    apply (cancel_mono
      (G.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) n
        (K.cycles n)).hom)).1
    simpa only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id] using hs
  simpa only [Category.assoc, ← G.map_comp, hf] using
    congrArg (· ≫ G.map (HomologicalComplex.homologyMap f n)) hs'

end CategoryTheory.Functor
