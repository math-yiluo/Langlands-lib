import Langlands.Galois.FrobeniusCharacter
import Langlands.Galois.PureCyclotomicComparison
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Weil.Representation.AbsoluteIrreducibility

/-! # Absolute irreducibility from a weakly associated family -/

noncomputable section

universe uK uL uM uV uW uE

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Unramified

private theorem irreducible_after_untwisting_scalarExtension
    {F G : Type*} [Field F] [Group G] (E : Type*) [Field E] [Algebra F E]
    (A : FiniteRepresentation F G) (χ : G →* Fˣ)
    (h : Representation.IsIrreducible ((A.twist χ).extendCoefficients E).representation) :
    Representation.IsIrreducible (A.extendCoefficients E).representation := by
  let χE := (Units.map (algebraMap F E).toMonoidHom).comp χ
  have heq : ((A.twist χ).extendCoefficients E).representation =
      Langlands.twist χE (A.extendCoefficients E).representation := by
    ext g : 1
    change ((χ g : F) • A.representation g).baseChange E =
      (algebraMap F E (χ g : F)) • (A.representation g).baseChange E
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [heq] at h
  exact (Langlands.isIrreducible_twist_iff χE (A.extendCoefficients E).representation).mp h

/-- For two pure weakly associated families with the same spectrum, an irreducible
    scalar-extended restriction of the first family forces absolute irreducibility
    of the second restriction at compatible coefficient identifications. -/
def PureLocalIrreducibilityTransferStatement : Prop :=
  ∀ {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [NumberField L] {M : Type uM} [Field M] [NumberField M]
    {E : Type uE} [Field E] [TopologicalSpace E] [T2Space E] [IsAlgClosed E]
    {excludedL : Finset (FinitePlace L)} {excludedM : Finset (FinitePlace M)}
    {R : Collection.{uK, uL, uV} K L excludedL} {U : Collection.{uK, uM, uW} K M excludedM}
    {ι : L →+* ℂ} {κ : M →+* ℂ} {r : ℕ} {s : SpectralSystem (FinitePlace K) r}
    {m n : ℤ},
    IsPureCompatible excludedL R m → IsPureCompatible excludedM U n →
    IsWeaklyAssociatedToSpectrum ι excludedL R s →
    IsWeaklyAssociatedToSpectrum κ excludedM U s →
    ∀ (v : FinitePlace K) (lam : {l : FinitePlace L // l ∉ excludedL})
      (mu : {l : FinitePlace M // l ∉ excludedM}),
      0 < (U mu).val.rank → (R lam).val.rank = (U mu).val.rank →
      ∀ (e : E →+* ℂ) (jR : FiniteCompletion L lam.val →+* E)
        (jU : FiniteCompletion M mu.val →+* E),
        Continuous jR → Continuous jU →
        (∀ x : L, e (jR (NumberField.FinitePlace.embedding lam.val x)) = ι x) →
        (∀ x : M, e (jU (NumberField.FinitePlace.embedding mu.val x)) = κ x) →
        (letI : Algebra (FiniteCompletion L lam.val) E := jR.toAlgebra;
          Representation.IsIrreducible
            ((atFinitePlace v (R lam)).val.extendCoefficients E).representation) →
        (atFinitePlace v (U mu)).val.IsAbsolutelyIrreducible

theorem pureLocalIrreducibilityTransfer :
    PureLocalIrreducibilityTransferStatement.{uK, uL, uM, uV, uW, uE} := by
  classical
  intro K _ _ L _ _ M _ _ E _ _ _ _ excludedL excludedM R U ι κ r s m n
    hR hU hs ht v lam mu hpos hrank e jR jU hjR hjU hι hκ hirr
  obtain ⟨k, hk⟩ := pureWeightDifferenceEven lam mu hpos hR hU hs ht
  have heq := eventually_frobeniusEulerPolynomial_map_eq_cyclotomicTwist_of_weakAssociation
    hk hR hU hs ht lam mu e jR jU hι hκ
  have hf := Filter.eventually_cofinite.mp heq
  let : Algebra (FiniteCompletion L lam.val) E := jR.toAlgebra
  let : Algebra (FiniteCompletion M mu.val) E := jU.toAlgebra
  obtain ⟨f⟩ := localEquiv_extendCoefficients_of_frobeniusEulerPolynomial_map_eq
    (R lam) (cyclotomicTwist mu.val k (U mu)) jR jU hjR hjU hf.toFinset
    (fun w hw _ => by
      by_contra hn
      exact hw (hf.mem_toFinset.mpr hn)) v hrank hirr
  let res := Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding (K := K) v)
  let χ := geometricCyclotomicPower K _ (CompletionPadic.padicMap mu.val) k
  have htwist := (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv f).mp hirr
  have hUext := irreducible_after_untwisting_scalarExtension E
    (atFinitePlace v (U mu)).val (χ.comp res.toMonoidHom) htwist
  exact FiniteRepresentation.irreducible_extendCoefficients_of_isAlgClosed
    E (AlgebraicClosure (FiniteCompletion M mu.val)) _ hUext

end Langlands.GaloisRepresentation
