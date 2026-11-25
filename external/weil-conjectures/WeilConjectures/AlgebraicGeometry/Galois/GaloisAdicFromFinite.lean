/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicRationalProperties
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicAlgebraicProperties

set_option linter.privateModule false

/-! # Adic reconstruction from finite Galois modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor
  Padic Padic.coefficientExtensionIntegers Representation.IsContinuousIntegral
  Representation.IsContinuousCoefficient Representation.IsLAdic
  IsLisseIntegralDiagram galoisUnderlyingSetSheaf

section ConstructionConsequences

variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  (d : GaloisLisseAdicData y G c l Q)

-- The normalized stalk and tensor comparisons have large dependent module types.
private theorem integralEvaluation_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisIntegralEvaluationAction y G c l Q d := by
  unfold galoisIntegralEvaluationAction
  intro E F n
  have hi := GaloisAdicCanonicalConstruction.inverseLimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  rcases hi with ⟨V, hV⟩
  rcases hV with ⟨α, hα⟩
  rcases hα with ⟨C, hC⟩
  rcases hC with ⟨e, _, hp, hfinite⟩
  have hf := hfinite n
  rcases hf with ⟨h, hκ⟩
  rcases hκ with ⟨κ, hgerm, haction⟩
  refine ⟨h, κ, hgerm, ?_⟩
  intro g z
  have hproj (w : ((d.eI E).functor.obj F).obj.V) :
      (α.hom.app (op n)) ((e.inv ≫ C.π.app (op n)).hom w) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          ((d.τI E).hom.app F w) := by
    exact congrArg (fun f ↦ f w) (hp n)
  calc
    _ = κ ((α.hom.app (op n))
        ((e.inv ≫ C.π.app (op n)).hom (((d.eI E).functor.obj F).obj.ρ g z))) :=
      congrArg κ (hproj _).symm
    _ = κ ((α.hom.app (op n))
        ((V.obj (op n)).ρ g ((e.inv ≫ C.π.app (op n)).hom z))) :=
      congrArg (fun w ↦ κ ((α.hom.app (op n)) w))
        (Rep.hom_comm_apply (e.inv ≫ C.π.app (op n)) g z)
    _ = _ := haction g _
    _ = _ := congrArg (fun w ↦ (c.γ g).asIso.hom.app
      (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n)) h) (κ w)) (hproj z)

end ConstructionConsequences

end AlgebraicGeometry.Scheme
