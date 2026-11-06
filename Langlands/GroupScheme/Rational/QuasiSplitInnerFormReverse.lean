import Langlands.GroupScheme.Rational.QuasiSplitInnerFormSeparableClosure
import Langlands.GroupScheme.Rational.InnerDiscrepancySymmetry
import Langlands.GroupScheme.Adjoint.QuasiSplitProof

/-! # Finite-Galois assembly from reverse separable-closure innerness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitInnerForm

variable {k : Type u} [Field k]
    {G H A B : GroupScheme (Spec (CommRingCat.of k))}

/-- A natural local family over the separable closure supplies a finite-Galois
presentation; quasi-splitness of its supplied adjoint is derived. -/
def ofSeparableClosureLocal (hG : IsConnectedReductive G) (hH : IsQuasiSplit H)
    (p : H ⟶ B) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso H G (Over.mk (algebraBaseMap k (SeparableClosure k))))
    (he : e.HasInnerDiscrepancy hp.innerAction) : QuasiSplitInnerForm G := by
  refine ofSeparableClosure hG hH p hp
    (adjointQuotientQuasiSplitStatement k H B p hp hH) e.toBaseChangeIso ?_
  rw [LocalGroupIso.ofBaseChangeIso_toBaseChangeIso]
  exact he

/-- Starting with the reverse local family, construct its inverse innerness and
the finite-Galois quasi-split inner-form presentation. -/
def ofReverseSeparableClosure (hH : IsQuasiSplit H)
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (p : H ⟶ B) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k (SeparableClosure k))))
    (he : e.HasInnerDiscrepancy hq.innerAction) : QuasiSplitInnerForm G :=
  ofSeparableClosureLocal hq.isConnectedReductive hH p hp e.symm
    (hq.hasInnerDiscrepancy_symm hp e he)

/-- The assembled presentation retains the supplied quasi-split model. -/
@[simp] theorem ofReverseSeparableClosure_model (hH : IsQuasiSplit H)
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (p : H ⟶ B) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k (SeparableClosure k))))
    (he : e.HasInnerDiscrepancy hq.innerAction) :
    (ofReverseSeparableClosure hH q hq p hp e he).model = H := rfl

/-- The assembled presentation retains the supplied full-centre quotient target. -/
@[simp] theorem ofReverseSeparableClosure_adjoint (hH : IsQuasiSplit H)
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (p : H ⟶ B) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k (SeparableClosure k))))
    (he : e.HasInnerDiscrepancy hq.innerAction) :
    (ofReverseSeparableClosure hH q hq p hp e he).adjoint = B := rfl

end Langlands.GroupScheme.QuasiSplitInnerForm
