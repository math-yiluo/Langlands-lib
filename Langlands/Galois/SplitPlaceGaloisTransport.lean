import Langlands.Galois.ClosureRestriction
import Langlands.Galois.QuadraticPatchingStatement
import Langlands.Weil.Representation.Restriction
import Mathlib.LinearAlgebra.Trace

/-! # Reflection of Galois representation equivalence at a split place -/

noncomputable section

universe uK uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K : Type uK} {E : Type uE} {L : Type uL}
  [Field K] [Field E] [Field L]

/-- Every base automorphism lifts along the chosen closure embedding of a field isomorphism. -/
theorem absoluteGaloisMap_surjective_of_surjective (f : K →+* E) (hf : Function.Surjective f) :
    Function.Surjective (Field.absoluteGaloisGroup.map f) := by
  let : Algebra K E := f.toAlgebra
  let : Algebra.IsIntegral K E := ⟨f.isIntegral_of_surjective hf⟩
  let : Algebra.IsIntegral K (AlgebraicClosure E) := Algebra.IsIntegral.trans E
  let : IsAlgClosure K (AlgebraicClosure E) := ⟨inferInstance, inferInstance⟩
  let ι := chosenClosureEmbedding f
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := ι.toAlgebra
  let : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E) := IsScalarTower.of_algHom ι
  intro σ
  let τ : AlgebraicClosure E ≃ₐ[K] AlgebraicClosure E := σ.liftNormal (AlgebraicClosure E)
  have hfix (e : E) : τ (algebraMap E (AlgebraicClosure E) e) =
      algebraMap E (AlgebraicClosure E) e := by
    obtain ⟨k, rfl⟩ := hf e
    exact τ.commutes k
  let τE : Field.absoluteGaloisGroup E := { τ.toRingEquiv with commutes' := hfix }
  refine ⟨τE, ?_⟩
  change (AlgEquiv.restrictScalars K τE).restrictNormal (AlgebraicClosure K) = σ
  exact σ.restrict_liftNormal (AlgebraicClosure E)

variable [NumberField K] [NumberField E] [Algebra K E]

/-- Restricting along the completion map at a completely split place reaches every local
    absolute Galois element of the base. -/
theorem splitPlace_absoluteGaloisMap_surjective {v : FinitePlace K}
    (w : FinitePlace E) [hw : w.asIdeal.LiesOver v.asIdeal]
    (hsplit : SplitsCompletelyAt (N := E) v) :
    Function.Surjective (Field.absoluteGaloisGroup.map (completionMap v w)) :=
  absoluteGaloisMap_surjective_of_surjective (completionMap v w)
    (Module.Free.bijective_algebraMap_of_finrank_eq_one (hsplit w hw)).surjective

/-- Equivalence of actual local representations is unchanged by restriction to a split place. -/
def SplitPlaceGaloisTransportStatement : Prop :=
  ∀ (K : Type uK) (E : Type uE) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (v : FinitePlace K) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal],
    SplitsCompletelyAt (N := E) v →
    ∀ (L : Type uL) [Field L]
      (A : FiniteRepresentation.{uL, uK, uV} L (LocalGroup v))
      (B : FiniteRepresentation.{uL, uK, uW} L (LocalGroup v)),
      let φ := (Field.absoluteGaloisGroup.map (completionMap v w)).toMonoidHom
      Nonempty (FiniteRepresentation.Equiv (A.restrict φ) (B.restrict φ)) ↔
        Nonempty (FiniteRepresentation.Equiv A B)

theorem splitPlaceGaloisTransport : SplitPlaceGaloisTransportStatement.{uK, uE, uL, uV, uW} := by
  intro K E _ _ _ _ _ v w _ hsplit L _ A B
  constructor
  · rintro ⟨e⟩
    refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
    intro σ
    obtain ⟨τ, rfl⟩ := splitPlace_absoluteGaloisMap_surjective w hsplit σ
    exact e.toIntertwiningMap.isIntertwining' τ
  · rintro ⟨e⟩
    exact ⟨Representation.Equiv.mk e.toLinearEquiv
      (fun τ => e.toIntertwiningMap.isIntertwining'
        (Field.absoluteGaloisGroup.map (completionMap v w) τ))⟩

end Langlands.GaloisRepresentation
