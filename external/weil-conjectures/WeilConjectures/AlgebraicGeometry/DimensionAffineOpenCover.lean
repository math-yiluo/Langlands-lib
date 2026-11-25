/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Dimension
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Ideal.Height

/-!
# Dimension from an affine open cover

Source: Stacks Project, Properties, Lemma 04MU; Schemes, Lemma 01HV;
Algebra, Lemma 00KG (blueprint: lem-pc-dimension-affine-open-cover).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-dimension-affine-open-cover) Let the nonempty scheme `X` be covered by
open subschemes `U i`, each isomorphic to the spectrum of the commutative ring `A i`.
Its dimension, defined as the supremum of the Krull dimensions of its local rings, is the
supremum of the Krull dimensions of these rings (Stacks, Tags 04MU, 01HV, 00KG).

Proof: For each chart, the scheme isomorphism identifies its ring of global sections with
`A i`, hence their Krull dimensions agree. The points of the chart correspond bijectively
to primes of its ring of sections. The stalk at each point is the localization at the
corresponding prime, whose dimension is the height of that prime. Taking the supremum over
the chart gives its ring dimension by the supremum-of-heights formula, including the empty
chart, whose ring has dimension bottom. Finally, the opens cover `X`, so regroup the
supremum of local-ring dimensions over all points by charts. -/
theorem Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover
    (X : Scheme.{u}) [Nonempty X] {I : Type v} (U : I → X.Opens)
    (hcover : ⨆ i, U i = ⊤) (A : I → CommRingCat.{u})
    (hiso : ∀ i, (U i : Scheme.{u}) ≅ Spec (A i)) :
    X.dim = ⨆ i, ringKrullDim (A i) := by
  let f (i : I) : Spec (A i) ⟶ X := (hiso i).inv ≫ (U i).ι
  have hstalk (i : I) (p : Spec (A i)) :
      ringKrullDim (X.presheaf.stalk (f i p)) = (p.asIdeal.height : WithBot ℕ∞) := by
    let : Algebra (A i) ((Spec (A i)).presheaf.stalk p) :=
      StructureSheaf.stalkAlgebra (A i) p
    let : IsLocalization.AtPrime ((Spec (A i)).presheaf.stalk p) p.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk (A i) p
    calc
      ringKrullDim (X.presheaf.stalk (f i p)) =
          ringKrullDim ((Spec (A i)).presheaf.stalk p) :=
        ringKrullDim_eq_of_ringEquiv
          (asIso ((f i).stalkMap p)).commRingCatIsoToRingEquiv
      _ = (p.asIdeal.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal _
  have hdim (i : I) :
      ringKrullDim (A i) = ⨆ p : Spec (A i), (p.asIdeal.height : WithBot ℕ∞) := by
    change ringKrullDim (A i) = ⨆ p : PrimeSpectrum (A i), _
    simpa only [ringKrullDim, PrimeSpectrum.height_eq_orderHeight] using
      (Order.krullDim_eq_iSup_height (α := PrimeSpectrum (A i)))
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, U i from hcover.symm ▸ trivial)
    let p : Spec (A i) := (hiso i).hom ⟨x, hx⟩
    have hp : f i p = x := by
      simp [f, p]
    rw [← hp, hstalk]
    apply le_trans _ (le_iSup (fun i ↦ ringKrullDim (A i)) i)
    rw [hdim i]
    exact le_iSup (fun p : Spec (A i) ↦ (p.asIdeal.height : WithBot ℕ∞)) p
  · refine iSup_le fun i ↦ ?_
    rw [hdim]
    refine iSup_le fun p ↦ ?_
    rw [← hstalk]
    exact le_iSup (fun x : X ↦ ringKrullDim (X.presheaf.stalk x)) (f i p)

end AlgebraicGeometry
