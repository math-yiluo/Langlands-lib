/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoodsPointwise

/-!
# Étaleness along a closed subscheme from its infinitesimal neighbourhoods

Source: More on Morphisms, Lemma 0A43 (part (2))
(blueprint: lem-weil-pbc-etale-infinitesimal-neighbourhoods).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: More on Morphisms, Lemma 0A43 (part (2));
(blueprint: lem-weil-pbc-etale-infinitesimal-neighbourhoods).

Given a finite type morphism between locally Noetherian schemes and a closed subscheme
of the target, if every infinitesimal base change is étale, then the morphism is étale
on an open neighbourhood of the inverse image of the closed subscheme.

Proof (the six steps of the blueprint node):
1. Finite type gives local finite type (def-weil-finite-type-morphism), so the locally
   Noetherian target (pqf-def-locnoeth) allows the Artinian lifting criterion at every
   source point. Fix x over Z, and form the base changes with their two projections
   (def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers,
   def-pc-fibre-product, def-pc-base-change).
2. For a small extension B' -> B and a compatible lifting diagram at x
   (lem-weil-pbc-smooth-artinian-lifting-at-point), choose an affine neighbourhood of g(x)
   (def-weil-affine-spectrum). The defining ideal of Z maps into the maximal ideal of B'.
   This maximal ideal is nilpotent because B' is Artinian local, so the map from Spec B'
   factors through some Z_n. The pullback property lifts the map from Spec B to X_n.
   The small extension has square-zero kernel (def-sbc-first-order-thickening).
   Since X_n -> Z_n is étale, it is smooth
   (lem-weil-pbc-etale-smooth-zero-dimensional-fibres), hence formally smooth
   (def-sbc-smooth-morphisms, def-sbc-formally-smooth). Lift to X_n, then compose with
   its projection to X to obtain the required lift of the original diagram.
3. The Artinian lifting criterion (lem-weil-pbc-smooth-artinian-lifting-at-point)
   now gives an open neighbourhood U_x on which g is smooth (def-sbc-smooth-morphisms).
4. The closed immersion Z_0 -> S preserves the residue field at g(x)
   (def-weil-residue-field). Pullback transitivity identifies the fibre of g there
   with that of X_0 -> Z_0 (def-pc-fibre-product, def-pc-base-change). Its dimension
   at x is zero because X_0 -> Z_0 is étale
   (lem-weil-pbc-etale-smooth-zero-dimensional-fibres, def-kun-dimension).
5. Smoothness near x and zero fibre dimension give a smaller open W_x containing x
   on which g is étale (lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension,
   def-weil-etale-morphism; Morphisms, Definition 02GI).
6. Take W to be the union of these W_x for all x over Z, or the empty open if there
   are no such points. This contains the inverse image of Z. Étaleness is local on
   the source, so g restricted to W is étale (lem-weil-pbc-etale-local-on-source,
   def-weil-etale-morphism; Morphisms, Lemma 02GJ).
-/
theorem etale_on_open_of_etale_infinitesimal_neighbourhoods
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι))) :
    ∃ W : X.Opens,
      (g : X → S) ⁻¹' Set.range (i : Z → S) ⊆ (W : Set X) ∧ Etale (W.ι ≫ g) := by
  classical
  let I := {x : X // (g : X → S) x ∈ Set.range (i : Z → S)}
  choose U hU hEU using fun x : I =>
    etale_infinitesimal_pointwise g i J hJ h_etale x.1 x.2
  let W : X.Opens := ⨆ x : I, U x
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    let y' : I := ⟨x, hx⟩
    exact (le_iSup U y') (hU y')
  · apply IsZariskiLocalAtSource.of_openCover (Scheme.Opens.iSupOpenCover U)
    intro x
    simpa [W, Scheme.Opens.iSupOpenCover] using hEU x

end AlgebraicGeometry
