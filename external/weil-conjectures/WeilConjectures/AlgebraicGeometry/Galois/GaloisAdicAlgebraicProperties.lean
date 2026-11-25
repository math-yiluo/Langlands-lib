/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicAlgebraicMonoidal
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import Mathlib.CategoryTheory.Abelian.Transfer
import WeilConjectures.CategoryTheory.Monoidal.PrescribedMonoidal

set_option linter.privateModule false

/-! # Algebraic and coefficient clauses of the adic correspondence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped MonoidalCategory

namespace AlgebraicGeometry.Scheme

section Consequences

variable
    {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q)

private theorem algebraicSheavesAbelian_of_representations
    (h : galoisAlgebraicRepresentationsAbelian y G c l Q d) :
    galoisAlgebraicSheavesAbelian y G c l Q d := by
  obtain ⟨a⟩ := h
  let : Abelian (galoisAdicRepresentations l Q d.P d.δ) := a
  let : Preadditive (LisseAlgebraicSheaf l Y Q) :=
    .ofFullyFaithful d.eA.fullyFaithfulFunctor
  let : HasFiniteProducts (LisseAlgebraicSheaf l Y Q) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence d.eA.functor⟩
  exact ⟨abelianOfEquivalence d.eA.functor⟩

private theorem algebraicMonoidal_of_comparisons
    (hT : galoisAlgebraicTensor y G c l Q d)
    (hU : galoisAlgebraicUnit y G c l Q d) :
    galoisAlgebraicMonoidal y G c l Q d := by
  classical
  choose e he using hT
  let T := d.eA.functor ⋙ ObjectProperty.ι _
  apply Monoidal.nonempty_prescribedMonoidal T (Functor.FullyFaithful.ofFullyFaithful T)
    (lisseAlgebraicTensor l Y Q) (lisseAlgebraicUnit l Y Q)
  · intro F H
    exact Rep.mkIso
      { toLinearEquiv := e F H
        isIntertwining' := fun g ↦ LinearMap.ext (fun z ↦ he F H g z) }
  · exact hU.some.symm

end Consequences

end AlgebraicGeometry.Scheme
