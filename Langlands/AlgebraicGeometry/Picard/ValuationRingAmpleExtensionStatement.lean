import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Ample line bundles on the generic fibre of an abelian scheme over a valuation ring

A specialization of Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, LNM 119, Théorème XI 1.4 (Grothendieck), to the base `Spec R` of a valuation
domain `R`. This module states the proposition and does not prove it. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `R` be a valuation domain of arbitrary rank with fraction field `K`, and let `A` be an
abelian scheme over `Spec R`. If the generic fibre `A ×_{Spec R} Spec K` carries an ample line
bundle, then some line bundle on the total space of `A` has ample pullback to the generic fibre
along the first projection. This proposition is a statement target, not a proof. -/
def ValuationRingAmpleExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R))),
    (∃ L : LineBundle (pullback A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        L.IsAmple) →
      ∃ M : LineBundle A.X.left,
        ((LineBundle.pullback
          (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M).IsAmple

end Langlands.AbelianScheme
