import Langlands.Global.CompletionResidue

noncomputable section

open scoped Valued
open NumberField IsDedekindDomain

universe u

namespace Langlands.Global.CompletionResidue

variable (K : Type u) [Field K] [NumberField K] (p : FinitePlace K)

/-- The norm and adic integer rings are identified by the identity on the completion. -/
def normIntegersEquivAdic :
    LocalGalois.baseIntegers (FiniteCompletion K p) ≃+* p.adicCompletionIntegers K where
  toFun x := ⟨x, Valued.toNormedField.norm_le_one_iff.mp x.property⟩
  invFun x := ⟨x, Valued.toNormedField.norm_le_one_iff.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] theorem normIntegersEquivAdic_coe
    (x : LocalGalois.baseIntegers (FiniteCompletion K p)) :
    (normIntegersEquivAdic K p x : p.adicCompletion K) = x := rfl

@[simp] theorem normIntegersEquivAdic_integersMap (x : RingOfIntegers K) :
    normIntegersEquivAdic K p (integersMap K p x) =
      algebraMap (RingOfIntegers K) (p.adicCompletionIntegers K) x := by
  apply Subtype.ext
  rfl

/-- The existing global-to-completed residue equivalence transported to adic integers. -/
def adicResidueEquiv : (RingOfIntegers K ⧸ p.asIdeal) ≃+*
    IsLocalRing.ResidueField (p.adicCompletionIntegers K) :=
  (residueEquiv K p).trans (IsLocalRing.ResidueField.mapEquiv (normIntegersEquivAdic K p))

@[simp] theorem adicResidueEquiv_mk (x : RingOfIntegers K) :
    adicResidueEquiv K p (Ideal.Quotient.mk p.asIdeal x) =
      IsLocalRing.residue (p.adicCompletionIntegers K)
        (algebraMap (RingOfIntegers K) (p.adicCompletionIntegers K) x) := by
  simp only [adicResidueEquiv, RingEquiv.trans_apply, residueEquiv_mk,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue _) (normIntegersEquivAdic_integersMap K p x)

instance finite_adicResidueField : Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers K)) :=
  Finite.of_equiv (RingOfIntegers K ⧸ p.asIdeal) (adicResidueEquiv K p).toEquiv

theorem card_adicResidueField :
    Nat.card (IsLocalRing.ResidueField (p.adicCompletionIntegers K)) = Ideal.absNorm p.asIdeal :=
  Nat.card_congr (adicResidueEquiv K p).symm.toEquiv

end Langlands.Global.CompletionResidue
