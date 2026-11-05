import Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient
import Langlands.AlgebraicGeometry.Picard.ProperLocalAdicRankOnePromotion
import Langlands.AlgebraicGeometry.Picard.LineBundleStalkFlatness
import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Rank-one promotion from ordinary adic pullbacks -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open FormalLineBundle Modules
open Modules.AdicStalkQuotient

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- Every point on the closed fibre lifts to every actual maximal-adic thickening. -/
lemma exists_adicPoint_of_closedFibre (x : X) (hx : f x = IsLocalRing.closedPoint R)
    (n : ℕ) : ∃ y : adicSpace f (IsLocalRing.maximalIdeal R) n,
      adicProjection f (IsLocalRing.maximalIdeal R) n y = x := by
  have hb : IsLocalRing.closedPoint R ∈
      Set.range (adicBaseProjection (IsLocalRing.maximalIdeal R) n) := by
    apply (mem_range_SpecMap_quotient_iff _ _).mpr
    exact Ideal.pow_le_self (by omega)
  obtain ⟨s, hs⟩ := hb
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := adicBaseProjection (IsLocalRing.maximalIdeal R) n) x s (hx.trans hs.symm)
  exact ⟨y, hy⟩

/-- The maximal ideal extends to a proper ideal at a closed-fibre point. -/
lemma extendedMaximalIdeal_ne_top (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    (IsLocalRing.maximalIdeal R).map (baseStalkHom f x) ≠ ⊤ := by
  obtain ⟨y, rfl⟩ := exists_adicPoint_of_closedFibre f x hx 0
  have h := RingHom.ker_ne_top
    ((adicProjection f (IsLocalRing.maximalIdeal R) 0).stalkMap y).hom
  simpa only [ker_adicProjection_stalkMap, zero_add, pow_one] using h

/-- Rank one of the ordinary adic pullback supplies an actual quotient-stalk frame. -/
def adicQuotientStalkFrame (M : X.Modules) (n : ℕ)
    (hM : IsLocallyFreeRankOne
      ((Scheme.Modules.pullback (adicProjection f (IsLocalRing.maximalIdeal R) n)).obj M))
    (y : adicSpace f (IsLocalRing.maximalIdeal R) n) :
    (stalk M (adicProjection f (IsLocalRing.maximalIdeal R) n y) ⧸
      (((IsLocalRing.maximalIdeal R).map
        (baseStalkHom f (adicProjection f (IsLocalRing.maximalIdeal R) n y))) ^ (n + 1) •
          (⊤ : Submodule (X.presheaf.stalk (adicProjection f (IsLocalRing.maximalIdeal R) n y))
            (stalk M (adicProjection f (IsLocalRing.maximalIdeal R) n y))))) ≃ₗ[
      X.presheaf.stalk (adicProjection f (IsLocalRing.maximalIdeal R) n y)]
      (X.presheaf.stalk (adicProjection f (IsLocalRing.maximalIdeal R) n y) ⧸
        ((IsLocalRing.maximalIdeal R).map
          (baseStalkHom f (adicProjection f (IsLocalRing.maximalIdeal R) n y))) ^ (n + 1)) := by
  let p := adicProjection f (IsLocalRing.maximalIdeal R) n
  letI := (p.stalkMap y).hom.toAlgebra
  letI := relativeStalkModule p ((Scheme.Modules.pullback p).obj M) y
  have : IsScalarTower (X.presheaf.stalk (p y))
      ((adicSpace f (IsLocalRing.maximalIdeal R) n).presheaf.stalk y)
      (stalk ((Scheme.Modules.pullback p).obj M) y) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact (pullbackStalkQuotientEquiv f M (IsLocalRing.maximalIdeal R) n y).symm.trans
    (((hM.stalkLinearEquiv y).restrictScalars (X.presheaf.stalk (p y))).trans
      (quotientStalkAlgEquiv f (IsLocalRing.maximalIdeal R) n y).symm.toLinearEquiv)

/-- A finitely presented actual module whose ordinary maximal-adic pullbacks
are all locally rank one is an actual line bundle on the whole source. -/
def lineBundleOfAdicPullbacks [IsLocallyNoetherian X] [UniversallyClosed f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hM : ∀ n : ℕ, IsLocallyFreeRankOne
      ((Scheme.Modules.pullback (adicProjection f (IsLocalRing.maximalIdeal R) n)).obj M)) :
    LineBundle X :=
  lineBundleOfClosedFibreAdicStalkQuotients f M (by
    intro x hx
    refine ⟨(IsLocalRing.maximalIdeal R).map (baseStalkHom f x),
      extendedMaximalIdeal_ne_top f x hx, ?_⟩
    intro n
    obtain ⟨y, rfl⟩ := exists_adicPoint_of_closedFibre f x hx n
    exact ⟨adicQuotientStalkFrame f M n (hM n) y⟩)

/-- The promoted line bundle has the original module sheaf as its underlying object. -/
@[simp]
lemma lineBundleOfAdicPullbacks_obj [IsLocallyNoetherian X] [UniversallyClosed f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hM : ∀ n : ℕ, IsLocallyFreeRankOne
      ((Scheme.Modules.pullback (adicProjection f (IsLocalRing.maximalIdeal R) n)).obj M)) :
    (lineBundleOfAdicPullbacks f M hM).obj = M := rfl

end Langlands.AlgebraicGeometry.Picard
