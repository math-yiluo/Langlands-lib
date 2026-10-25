import Langlands.ClassField.Global.IdeleFiniteInvariantRestrictionStatement
import Langlands.ClassField.Global.IdeleFinitePlaceIndependence
import Langlands.Global.CompletionPadicTower

/-! # Finite idele invariant restriction from the local restriction law -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hRes : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeRestriction)

include hRes in
/-- The local restriction law gives finite idele restriction at the actual completions. -/
theorem finiteIdeleInvariantRestriction_of_relativeRestriction :
    FiniteIdeleInvariantRestriction I := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _ v w q _ _ _
  have := IsGalois.tower_top_of_isGalois F K E
  dsimp only
  intro c
  have := isGalois_adicCompletion v q
  have := isGalois_adicCompletion w q
  have := FiniteExtension.local_finite v w
  have := FiniteExtension.local_finite v q
  have := FiniteExtension.local_finite w q
  let := (padicField v).algebra
  let := (towerPadicField v w).algebra
  have := towerPadicField_isScalarTower v w
  have h := hRes (residuePrime v) (padicField v) (towerPadicField v w)
    (q.adicCompletion E) (ideleLocalMap v q 2 c)
  rw [relative_towerPadicField v w I] at h
  change (I (residuePrime w)).relative (padicField w) (q.adicCompletion E)
      (ideleLocalMap w q 2 (relativeIdeleRestriction F K E 2 c)) =
    Module.finrank (v.adicCompletion F) (w.adicCompletion K) •
      (I (residuePrime v)).relative (padicField v) (q.adicCompletion E)
        (ideleLocalMap v q 2 c)
  rw [ideleLocalMap_relativeIdeleRestriction v w q]
  exact h

/-- The finite restriction target follows from the supplied local restriction law. -/
theorem finiteIdeleInvariantRestrictionStatement :
    FiniteIdeleInvariantRestrictionStatement.{u} :=
  fun I hRes => finiteIdeleInvariantRestriction_of_relativeRestriction I hRes

include hRes in
/-- Local inflation and restriction imply restriction for the actual total family. -/
theorem totalIdeleInvariantMaps_restriction_of_localLaws
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages) :
    (totalIdeleInvariantMaps I hI).RestrictionCompatible :=
  totalIdeleInvariantMaps_restriction I hI
    (finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility I hInf)
    (finiteIdeleInvariantRestriction_of_relativeRestriction I hRes)

end Langlands.ClassField.Global
