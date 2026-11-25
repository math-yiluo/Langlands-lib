/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBoundaryCohomology
import WeilConjectures.SixFunctors.Etale.Gabber
import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

private theorem finite_middle_of_exact {A B C : Type*}
    [AddGroup A] [AddGroup B] [AddGroup C] [Finite A] [Finite C]
    (a : A →+ B) (b : B →+ C) (h : Function.Exact a b) : Finite B := by
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite C
  let _ := AddGroup.fintypeOfKerEqRange a b h.addMonoidHom_ker_eq
  infer_instance

/-- Unconditional finiteness of all cohomology groups is invariant under restriction
and extension by zero across a dense open of a curve.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and finite boundary term.
(blueprint: lem-pbc-a3-dense-open-cohomology-finiteness).

Proof: Write G = j_!j^*F and B = i_*i^*F for the reduced closed complement. The dense
open contains all generic points of X. The Noetherian complement has dimension zero
and is a finite union of k-rational points. H^0(B) is a finite product of finite stalk
modules: constructibility gives finite generation and the coefficient ring is finite.
All positive cohomology of B vanishes. The open-closed short exact sequence gives
0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0 and bijections above degree one.
If all H^q(F) are finite, H^0(G) injects into H^0(F), and H^1(G) has finite kernel
(a quotient of H^0(B)) and finite image in H^1(F). Conversely H^0(F) has finite kernel
H^0(G) and finite image in H^0(B), and H^1(F) is a quotient of H^1(G). In higher degrees
use the bijections. The zero boundary for U=X and empty X gives the same argument.
Neither a prime annihilator nor properness is required. -/
theorem dense_open_cohomology_finiteness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)) ↔
    (∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q)) := by
  -- The reduced closed complement supplies the third term of the excision sequence.
  let I := Scheme.IdealSheafData.vanishingIdeal U.compl
  have hi : Set.range I.subschemeι.base = (Set.range U.ι.base)ᶜ := by
    simp only [I, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι,
      TopologicalSpace.Opens.coe_compl]
  let E := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let S := (openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι I.subschemeι
    (disjoint_range_of_range_eq_compl U.ι I.subschemeι hi) F).map E
  have hS : S.ShortExact :=
    shortExact_map_forget₂ Λ
      (shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι I.subschemeι F hi)
  obtain ⟨hB0, hBpos⟩ := dense_open_boundary_cohomology Λ f F U hU
  have hB : ∀ q : ℕ, Finite (Sheaf.H S.X₃ q) := by
    intro q
    cases q with
    | zero => exact hB0
    | succ q =>
      have : Subsingleton (Sheaf.H S.X₃ (q + 1)) := hBpos (q + 1) (by omega)
      infer_instance
  have := hS.mono_f
  have h0 : Function.Injective (Sheaf.H.map S.f 0) :=
    CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono _ S.f
  -- Apply finite-kernel/finite-image arguments directly, without choosing higher isomorphisms.
  change (∀ q : ℕ, Finite (Sheaf.H S.X₂ q)) ↔
    (∀ q : ℕ, Finite (Sheaf.H S.X₁ q))
  constructor
  · intro h q
    cases q with
    | zero =>
      have := h 0
      exact Finite.of_injective (Sheaf.H.map S.f 0) h0
    | succ q =>
      have := h (q + 1)
      have := hB q
      exact finite_middle_of_exact (Sheaf.H.δSucc hS q) (Sheaf.H.map S.f (q + 1))
        (Sheaf.H.exact_δSucc_map hS q)
  · intro h q
    have := h q
    have := hB q
    exact finite_middle_of_exact (Sheaf.H.map S.f q) (Sheaf.H.map S.g q)
      (Sheaf.H.exact_map_map hS q)

end AlgebraicGeometry.IsCurve
