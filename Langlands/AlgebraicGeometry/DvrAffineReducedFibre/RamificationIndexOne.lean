import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.ResiduePreservingNormalization
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! # The local uniformizer test from ramification index one -/

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section LocalQuotient

variable (S C : Type*) [CommRing S] [IsLocalRing S] [CommRing C] [Algebra S C]
    (q : Ideal C) [q.IsPrime]

local notation "D" => Localization.AtPrime q

/-- If the length defining the ramification index is one and the prime lies
over the closed point, the extended base maximal ideal is maximal. -/
theorem map_maximalIdeal_eq_of_ramificationIdx_eq_one
    (hq : q.under S = maximalIdeal S) (he : q.ramificationIdx S = 1) :
    (maximalIdeal S).map (algebraMap S D) = maximalIdeal D := by
  rw [Ideal.ramificationIdx_def, hq, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at he
  exact he

/-- The localized quotient of ramification index one is the residue field
of that local ring, when the prime is over the closed point. -/
def localizedQuotientEquivResidue_of_ramificationIdx_eq_one
    (hq : q.under S = maximalIdeal S) (he : q.ramificationIdx S = 1) :
    (D ⧸ (maximalIdeal S).map (algebraMap S D)) ≃+* ResidueField D :=
  Ideal.quotEquivOfEq (map_maximalIdeal_eq_of_ramificationIdx_eq_one S C q hq he)

end LocalQuotient

section DVR

variable (S C : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing C] [Algebra S C]

/-- Ramification index one at every maximal ideal over the closed point
gives the uniformizer test if every maximal ideal is over that point. -/
theorem uniformizerAtMaximalLocalizations_of_ramificationIdx_eq_one {t : S} (ht : Irreducible t)
    (hcontain : ∀ (q : Ideal C), q.IsMaximal → algebraMap S C t ∈ q)
    (hidx : ∀ (q : Ideal C), q.IsMaximal → q.ramificationIdx S = 1) :
    UniformizerAtMaximalLocalizations C (algebraMap S C t) := by
  intro q hq
  have : q.IsPrime := hq.isPrime
  have hne : q.under S ≠ ⊥ := by
    intro hbot
    have hm : t ∈ q.under S := hcontain q hq
    exact ht.ne_zero (Ideal.mem_bot.mp (hbot ▸ hm))
  have hp : (q.under S).IsPrime := inferInstance
  have h := map_maximalIdeal_eq_of_ramificationIdx_eq_one S C q
    (IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)) (hidx q hq)
  rwa [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    IsScalarTower.algebraMap_apply S C (Localization.AtPrime q)] at h

/-- If every maximal ideal lies over the closed point and has ramification
index one, the residue tensor over the base DVR is reduced. -/
theorem isReduced_residueTensor_of_ramificationIdx_eq_one {t : S} (ht : Irreducible t)
    (hcontain : ∀ (q : Ideal C), q.IsMaximal → algebraMap S C t ∈ q)
    (hidx : ∀ (q : Ideal C), q.IsMaximal → q.ramificationIdx S = 1) :
    IsReduced (ResidueField S ⊗[S] C) := by
  have := isReduced_principalQuotient_of_uniformizerAtMaximalLocalizations
    (uniformizerAtMaximalLocalizations_of_ramificationIdx_eq_one S C ht hcontain hidx)
  let e := residueTensorEquivPrincipalQuotient S C ht.maximalIdeal_eq
  exact isReduced_of_injective e.toRingHom e.injective

end DVR

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
