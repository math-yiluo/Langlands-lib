import Langlands.AlgebraicGeometry.GroupoidCoactionFiniteEffectiveCover
import Langlands.AlgebraicGeometry.GroupoidCoactionGenericSupport

/-! # Noetherian vanishing for relations with finite effective covers -/

universe u

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

/-- All relations with a finite effective cover over this ring have
degree-one vanishing for finite coefficient coactions. -/
def FiniteCoveredRelationsVanishing (B : Type u) [CommRing B] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra B C] (t : B →+* C),
    RingEtaleEquivalenceRelation t → FiniteEffectiveCover t →
      FiniteCoactionVanishing.{u, u} t

/-- Quotient-stability of finite effective covers closes the support
induction for every Noetherian base ring. -/
theorem finiteCoveredRelationsVanishing_of_quotientCovers
    (hquot : ∀ (S C : Type u) [CommRing S] [CommRing C] [Algebra S C]
      (t : S →+* C) (_X : FiniteEffectiveCover t)
      (I : Ideal S) (hI : IsInvariantIdeal t I),
      Nonempty (FiniteEffectiveCover
        (RingEtaleEquivalenceRelation.quotientTarget I hI.symm)))
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    FiniteCoveredRelationsVanishing B := by
  apply noetherian_quotient_induction FiniteCoveredRelationsVanishing ?_ B
  intro S _ _ ih C _ _ t hE X
  apply finiteCoactionVanishing_of_quotients hE
  · intro _ _
    exact hasFiniteSupportVanishingStep_of_cover hE X.relation X.e X.cartesian
      X.ε X.ε_target X.comap_surjective
  · intro I hI0 hI
    obtain ⟨Y⟩ := hquot S C t X I hI
    exact ih I hI0 _ _ (hE.quotient I hI.symm) Y

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
  {t : B →+* C}

/-- Finite-coefficient vanishing for all finitely covered relations over a
Noetherian ring implies acyclicity for every coefficient coaction. -/
theorem isAcyclic_of_finiteCoveredRelationsVanishing [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t) (X : FiniteEffectiveCover t)
    (hvan : FiniteCoveredRelationsVanishing B)
    {M : Type u} [AddCommGroup M] [Module B M] (θ : GroupoidCoaction t M) :
    θ.IsAcyclic := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  apply isAcyclic_of_oneCohomologyVanishes θ
  exact oneCohomologyVanishes_of_finiteCoactionVanishing hE (hvan C t hE X) θ

end Langlands.AlgebraicGeometry.GroupoidCoaction
