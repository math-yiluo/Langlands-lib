import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! Actual whole-Levi conjugation on exact finite-length smooth K0. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear SmoothRep

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (hw : ConjugatesLevi (F := F) B C w)

/-- Actual inverse-conjugation transport preserves finite group-algebra length. -/
theorem transportFunctor_preservesFiniteLength :
    PreservesFiniteLength (transportFunctor.{uF, uV} B C w hw) :=
  pullbackFunctor_preservesFiniteLength (leviConjugationContinuous w hw).symm

/-- Actual whole-Levi transport preserves every short exact sequence. -/
theorem transportFunctor_preservesShortExact :
    PreservesFiniteLengthShortExact (transportFunctor.{uF, uV} B C w hw) := by
  intro A D E f g _ _ _ h
  exact h

/-- Actual inverse Levi conjugation induces an integer-linear equivalence of
the saturated exact finite-length smooth Grothendieck groups. -/
def leviTransportK0 :
    B.FiniteLengthGrothendieckGroup.{uV, uF} F ≃ₗ[ℤ]
      C.FiniteLengthGrothendieckGroup.{uV, uF} F :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv
    (leviConjugationContinuous w hw).symm

/-- The forward map is the exact K0 map of the existing transport functor. -/
theorem leviTransportK0_toLinearMap :
    (leviTransportK0.{uF, uV} F B C w hw).toLinearMap =
      SmoothRep.FiniteLengthGrothendieckGroup.map
        (transportFunctor.{uF, max uF uV} B C w hw)
        (transportFunctor_preservesFiniteLength F B C w hw)
        (transportFunctor_preservesShortExact F B C w hw) := rfl

/-- The map computes the class of the literal transported smooth object. -/
theorem leviTransportK0_finiteLengthClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F)) (hA : A.HasFiniteLength)
    (hOut : ((transportFunctor B C w hw).obj A).HasFiniteLength) :
    leviTransportK0.{uF, uV} F B C w hw (B.finiteLengthClass F A hA) =
      C.finiteLengthClass F ((transportFunctor B C w hw).obj A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation
    (leviConjugationContinuous w hw).symm A hA hOut

/-- Composing actual Levi transports multiplies their conjugating permutations
in the order of their actions, on every virtual class. -/
theorem leviTransportK0_comp {D : BlockShape n} {v u : Equiv.Perm (Fin n)}
    (hv : ConjugatesLevi (F := F) C D v)
    (hu : ConjugatesLevi (F := F) B D u) (h : v * w = u) :
    (leviTransportK0.{uF, uV} F C D v hv).toLinearMap.comp
        (leviTransportK0.{uF, uV} F B C w hw).toLinearMap =
      (leviTransportK0.{uF, uV} F B D u hu).toLinearMap := by
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F)
  intro A
  have hC := transportFunctor_preservesFiniteLength F B C w hw A.val A.property
  have hD := transportFunctor_preservesFiniteLength F C D v hv
    ((transportFunctor B C w hw).obj A.val) hC
  have hU := transportFunctor_preservesFiniteLength F B D u hu A.val A.property
  change leviTransportK0 F C D v hv
      (leviTransportK0 F B C w hw (B.finiteLengthClass F A.val A.property)) =
    leviTransportK0 F B D u hu (B.finiteLengthClass F A.val A.property)
  rw [leviTransportK0_finiteLengthClass F B C w hw A.val A.property hC,
    leviTransportK0_finiteLengthClass F C D v hv _ hC hD,
    leviTransportK0_finiteLengthClass F B D u hu A.val A.property hU]
  apply SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ A.val) (fun m => by
    change transport C D v hv (transport B C w hw A.val.representation) m =
      transport B D u hu A.val.representation m
    rw [transport_transport hw hv hu h])

/-- A block-preserving permutation acts trivially on exact K0, through the
actual action of its Levi permutation matrix. -/
theorem leviTransportK0_eq_id_of_mem_blockWeyl
    (hb : w ∈ Geometric.blockWeyl B)
    (hw' : ConjugatesLevi (F := F) B B w) :
    (leviTransportK0.{uF, uV} F B B w hw').toLinearMap =
      LinearMap.id (R := ℤ) (M := B.FiniteLengthGrothendieckGroup.{uV, uF} F) := by
  apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F)
  intro A
  have hB := transportFunctor_preservesFiniteLength F B B w hw' A.val A.property
  change leviTransportK0 F B B w hw' (B.finiteLengthClass F A.val A.property) =
    B.finiteLengthClass F A.val A.property
  rw [leviTransportK0_finiteLengthClass F B B w hw' A.val A.property hB]
  exact SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv _ _
    (transportWeylEquiv w hb hw' A.val.representation)

end Langlands.CuspidalSupport
