import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Adjoint.LocalIsomorphism

/-! # Symmetry of actual inner discrepancies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A B : GroupScheme S} {U : Over S}
    (e : LocalGroupIso G H U) (a : AutomorphicAction A G)
    (b : AutomorphicAction B H) (d : LocalGroupIso A B U)
    (hd : ∀ {T : Over S} (c : T ⟶ U) (x : T ⟶ A.X) (g : T ⟶ G.X),
      e.toFun c (a.act x g) = b.act (d.toFun c x) (e.toFun c g))

include d hd

/-- Inverting an equivariant local family transports its discrepancy by the
induced acting-group family and inversion. -/
theorem RepresentsDiscrepancy.symm_of_equivariant
    {T : Over S} {c c' : T ⟶ U} {x : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a c c' x) :
    e.symm.RepresentsDiscrepancy b c c' (d.toFun c x⁻¹) := by
  intro W t h
  change (e.toFun (t ≫ c)).symm (b.act (t ≫ d.toFun c x⁻¹) h) =
    (e.toFun (t ≫ c')).symm h
  apply (e.toFun (t ≫ c)).injective
  rw [MulEquiv.apply_symm_apply, ← d.naturality, GrpObj.comp_inv]
  have hh := hx t ((e.toFun (t ≫ c')).symm h)
  rw [MulEquiv.apply_symm_apply] at hh
  calc
    b.act (d.toFun (t ≫ c) (t ≫ x)⁻¹) h =
        b.act (d.toFun (t ≫ c) (t ≫ x)⁻¹)
          (e.toFun (t ≫ c) (a.act (t ≫ x) ((e.toFun (t ≫ c')).symm h))) :=
      congrArg (b.act (d.toFun (t ≫ c) (t ≫ x)⁻¹)) hh.symm
    _ = e.toFun (t ≫ c)
        (a.act (t ≫ x)⁻¹ (a.act (t ≫ x) ((e.toFun (t ≫ c')).symm h))) :=
      (hd (t ≫ c) (t ≫ x)⁻¹ _).symm
    _ = e.toFun (t ≫ c) ((e.toFun (t ≫ c')).symm h) := by
      rw [a.act_inv_act]

/-- Innerness of a local discrepancy passes to the inverse equivariant family. -/
theorem HasInnerDiscrepancy.symm_of_equivariant
    (he : e.HasInnerDiscrepancy a) : e.symm.HasInnerDiscrepancy b := by
  intro T c c'
  obtain ⟨x, hx⟩ := he c c'
  exact ⟨d.toFun c x⁻¹, RepresentsDiscrepancy.symm_of_equivariant e a b d hd hx⟩

/-- Construct the natural cocycle for an inverse family from forward innerness. -/
def innerCocycleSymm (hb : b.IsFaithful) (he : e.HasInnerDiscrepancy a) :
    Cocycle B U :=
  e.symm.innerCocycle b hb (HasInnerDiscrepancy.symm_of_equivariant e a b d hd he)

/-- The constructed inverse cocycle has the actual discrepancy equation. -/
theorem innerCocycleSymm_hasDiscrepancy
    (hb : b.IsFaithful) (he : e.HasInnerDiscrepancy a) :
    e.symm.HasDiscrepancy b (e.innerCocycleSymm a b d hd hb he) :=
  e.symm.innerCocycle_hasDiscrepancy b hb
    (HasInnerDiscrepancy.symm_of_equivariant e a b d hd he)

/-- Its value is the transported inverse of the forward canonical cocycle. -/
theorem innerCocycleSymm_toFun (ha : a.IsFaithful)
    (hb : b.IsFaithful) (he : e.HasInnerDiscrepancy a)
    {T : Over S} (c c' : T ⟶ U) :
    (e.innerCocycleSymm a b d hd hb he).toFun c c' =
      d.toFun c ((e.innerCocycle a ha he).toFun c c')⁻¹ := by
  apply RepresentsDiscrepancy.unique e.symm b hb
  · exact ((HasInnerDiscrepancy.symm_of_equivariant e a b d hd he) c c').choose_spec
  · exact RepresentsDiscrepancy.symm_of_equivariant e a b d hd (he c c').choose_spec

end LocalGroupIso

namespace IsAdjointQuotient

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H A B : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} {p : H ⟶ B}
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)
    (e : LocalGroupIso G H (Over.mk (algebraBaseMap k K)))

/-- Actual adjoint innerness passes to the inverse local family. -/
theorem hasInnerDiscrepancy_symm (he : e.HasInnerDiscrepancy hq.innerAction) :
    e.symm.HasInnerDiscrepancy hp.innerAction :=
  LocalGroupIso.HasInnerDiscrepancy.symm_of_equivariant e hq.innerAction hp.innerAction
    (hq.localIso hp e) (hq.localIso_innerAction hp e) he

/-- The inverse natural adjoint cocycle is constructed, rather than supplied. -/
def symmInnerCocycle (he : e.HasInnerDiscrepancy hq.innerAction) :
    Cocycle B (Over.mk (algebraBaseMap k K)) :=
  e.symm.innerCocycle hp.innerAction hp.innerAction_isFaithful
    (hq.hasInnerDiscrepancy_symm hp e he)

/-- The constructed cocycle represents the inverse family's actual discrepancy. -/
theorem symmInnerCocycle_hasDiscrepancy
    (he : e.HasInnerDiscrepancy hq.innerAction) :
    e.symm.HasDiscrepancy hp.innerAction (hq.symmInnerCocycle hp e he) :=
  e.symm.innerCocycle_hasDiscrepancy hp.innerAction hp.innerAction_isFaithful
    (hq.hasInnerDiscrepancy_symm hp e he)

/-- Explicit all-test comparison of the forward and inverse adjoint cocycles. -/
theorem symmInnerCocycle_toFun (he : e.HasInnerDiscrepancy hq.innerAction)
    {T : Over (Spec (CommRingCat.of k))}
    (c c' : T ⟶ Over.mk (algebraBaseMap k K)) :
    (hq.symmInnerCocycle hp e he).toFun c c' =
      (hq.localIso hp e).toFun c
        ((e.innerCocycle hq.innerAction hq.innerAction_isFaithful he).toFun c c')⁻¹ :=
  e.innerCocycleSymm_toFun hq.innerAction hp.innerAction (hq.localIso hp e)
    (hq.localIso_innerAction hp e) hq.innerAction_isFaithful
    hp.innerAction_isFaithful he c c'

end IsAdjointQuotient
end Langlands.GroupScheme
