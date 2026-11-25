/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent

/-!
# Strictly henselian neighbourhoods of boundary points

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `z` a boundary point and `x` the corresponding closed point of `C₀`. A *strictly henselian
neighbourhood* of the boundary point (`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`) is the
data used to compute the boundary stalk `(j_* F)_x̄` of a lisse Weil sheaf
(blueprint `lemma-boundary-stalk--1`):

* a weakly étale `h : Spec A ⟶ C̄` from the spectrum of a strictly henselian local ring, with a
  lift of the geometric point `x̄` through the closed point (for instance the strict
  henselization `A = (B_Q)^{I_Q}` of the chart at `z`, `B` the integral closure of its ring in
  the separable closure `Ω` of `k(C)`, `Q` the chosen point over `z` and `I_Q` its inertia
  group);
* its punctured part `Spec A ×_C̄ Ū`, identified as a pro-étale `Ū`-scheme with
  `k : Spec K' ⟶ Ū` for a subfield `K' = Ω^{I_Q}` of `Ω` containing `k(C)`, such that
  `Spec Ω ⟶ Spec K' ⟶ Ū` is the geometric generic point and the Galois group `Gal(Ω / K')` is
  the inertia group `I_Q`;
* a lift `α` of the Frobenius `Frᵐ`, `m = deg x`, to `Spec A`, compatible with the lift of `x̄`
  and with the residue Frobenius lift `σ_F ∈ Gal(Ω / k(C))` at `z` acting on `Spec Ω`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [Smooth (C ↘ Spec (.of K))] [IsIntegral C]
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] [j.IsOver (Spec (.of K))]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of K)))

/-- **A strictly henselian neighbourhood of a boundary point** `z` with closed point `x`,
relative to a Galois automorphism `σ_F` of `Ω` over `k(C)` (the residue Frobenius lift at `z`):
the data used to compute the boundary stalk `(j_* F)_x̄` as the inertia invariants of the generic
stalk, Frobenius-equivariantly (blueprint `lemma-boundary-stalk--1`). -/
structure BoundaryNeighbourhood
    (I : Subgroup Gal(Ω/C.functionField)) (σF : Gal(Ω/C.functionField)) (x : C.finitePoints) where
  /-- The ring of the neighbourhood. -/
  A : Type u
  [commRing : CommRing A]
  [isStrictlyHenselianLocalRing : IsStrictlyHenselianLocalRing A]
  /-- The weakly étale neighbourhood `Spec A ⟶ C̄`. -/
  h : Spec (.of A) ⟶ (C ↘ Spec (.of K)).geometricFiber
  [weaklyEtale : WeaklyEtale h]
  /-- The lift of `x̄` to `Spec A`. -/
  t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
    ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x)).obj (ProEt.mk h)
  /-- The lift of `x̄` lies over the closed point of `Spec A`. -/
  ht : (t.left ≫ pullback.fst h _) (IsLocalRing.closedPoint (AlgebraicClosure K)) =
    IsLocalRing.closedPoint A
  /-- The field of the punctured neighbourhood. -/
  K' : Type u
  [field : Field K']
  [algebra : Algebra K' Ω]
  [isSeparable : Algebra.IsSeparable K' Ω]
  [normal : Normal K' Ω]
  /-- `K'` contains the function field. -/
  exists_algebraMap_eq (a : C.functionField) : ∃ b : K', algebraMap K' Ω b = algebraMap _ Ω a
  /-- The punctured neighbourhood `Spec K' ⟶ Ū`. -/
  k : Spec (.of K') ⟶ (U ↘ Spec (.of K)).geometricFiber
  [weaklyEtale_k : WeaklyEtale k]
  /-- `Spec A ×_C̄ Ū` is `Spec K'`. -/
  e : ProEt.mk k ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j̄)).obj (ProEt.mk h)
  /-- `Spec Ω ⟶ Spec K' ⟶ Ū` is the geometric generic point. -/
  specFieldMap_comp : specFieldMap K' Ω ≫ k = genericGeomPoint (U ↘ Spec (.of K)) j
  /-- The Galois group `Gal(Ω / K')` is the inertia group. -/
  mem_iff (σ : Gal(Ω/C.functionField)) :
    σ ∈ I ↔ ∀ b : K', σ (algebraMap K' Ω b) = algebraMap K' Ω b
  /-- A lift of the Frobenius to `Spec A`. -/
  α : Spec (.of A) ⟶ Spec (.of A)
  hα : α ≫ h = h ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^
    (C ↘ Spec (.of K)).degreeOver x.1).asIso.hom
  /-- The lift of the Frobenius is compatible with the lift of `x̄`. -/
  hcα : (specGeometricFrobenius K ^ (C ↘ Spec (.of K)).degreeOver x.1).asIso.hom ≫
      (t.left ≫ pullback.fst h _) = (t.left ≫ pullback.fst h _) ≫ α
  /-- The lift of the Frobenius is compatible with `σ_F` on the generic point. -/
  hεα : Spec.map (CommRingCat.ofHom (σF : Ω →+* Ω)) ≫
      (specFieldMap K' Ω ≫ e.hom.left ≫ pullback.fst h (j̄)) =
    (specFieldMap K' Ω ≫ e.hom.left ≫ pullback.fst h (j̄)) ≫ α

end AlgebraicGeometry.WeilGroup
