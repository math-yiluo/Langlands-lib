import Langlands.Shimura.Unitary.EvenNormCorrection
import Langlands.Shimura.Unitary.SignedDeterminantReciprocity
import Langlands.Shimura.Unitary.UnitaryProfileCarrier

/-! # The even unitary profile from its discriminant invariant formulas -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.LocalClassField Langlands.ClassFieldTheory.Local
open Langlands.GaloisCohomology Langlands.ProfiniteCohomology Langlands.Galois
open scoped FiniteExtension

universe u v

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {n : ℕ} (hn : 1 < n)
  {s : Finset (Langlands.Global.FinitePlace E)} (positive : ∀ p : s, FinitePlacesAbove K p.val)
  (a : s → ZMod n) (r : (E →+* ℝ) → ℕ)

/-- The initial algebra with all signed Brauer values and the real signature charts. -/
structure InitialUnitaryProfile where
  carrier : CSA.{v, v} K
  data : letI : Algebra E carrier := Algebra.compHom carrier (algebraMap E K)
    letI : IsScalarTower E K carrier := IsScalarTower.of_algebraMap_eq' rfl
    CentralSimpleUnitaryData E K carrier n
  signatures : letI : Algebra E carrier := Algebra.compHom carrier (algebraMap E K)
    ∀ τ, HasSignature data.toSecondKindInvolution τ n (r τ)
  signed (p : s) (q : FinitePlacesAbove K p.val) : HasCompletedBrauerInvariant K carrier q.val
    (denominatorEquiv n (lt_trans Nat.zero_lt_one hn)
      (by classical exact if q = positive p then a p else -a p))
  outside (p : Langlands.Global.FinitePlace E) (hp : p ∉ s) (q : FinitePlacesAbove K p) :
    HasCompletedBrauerInvariant K carrier q.val 0

set_option maxRecDepth 8192 in
/-- Construct the algebra, set the real signatures, and retain its finite Brauer profile. -/
def initialUnitaryProfile (hs : ∀ p : s, IsSplitPlace E K p.val) (hr : ∀ τ, r τ ≤ n) :
    InitialUnitaryProfile hn positive a r := by
  classical
  let ex := exists_csa_with_involution_for_splitProfile (lt_trans Nat.zero_lt_one hn) hs positive a
  let A := ex.choose
  have hA := ex.choose_spec
  let : Algebra E A := Algebra.compHom A (algebraMap E K)
  let : IsScalarTower E K A := IsScalarTower.of_algebraMap_eq' rfl
  let σ := SecondKindInvolution.ofUnitaryInvolution hA.2.1.choose hA.2.1.choose_spec
  let D : CentralSimpleUnitaryData E K A n :=
    { toSecondKindInvolution := σ
      rank_gt_one := hn
      central := inferInstance
      simple := inferInstance
      finite := inferInstance
      dimension := hA.1.trans (pow_two n).symm }
  let T := realSignatureTwist D r hr
  exact ⟨A, { D with toSecondKindInvolution := T.val }, T.property, hA.2.2.1, hA.2.2.2⟩

attribute [local instance] FiniteExtension.local_finite

set_option maxRecDepth 8192 in
/-- The localization data needed from the even discriminant of the initial unitary pair. -/
structure UnitaryProfileDiscriminantValues (P : InitialUnitaryProfile hn positive a r) where
  embeddings : PlaceEmbeddings E (AlgebraicClosure E)
  brauerClass : cohomology (unitsModule E (AlgebraicClosure E)) 2
  chosen (p : s) : localInvariant embeddings p.val brauerClass = (n / 2) •
    (denominatorEquiv n (lt_trans Nat.zero_lt_one hn) (a p) : RationalModIntegers)
  splitOutside (p : Langlands.Global.FinitePlace E) (hps : p ∉ s) (hp : IsSplitPlace E K p) :
    localInvariant embeddings p brauerClass = 0
  nonsplitOutside (p : Langlands.Global.FinitePlace E) (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p) :
    letI : Algebra E P.carrier := Algebra.compHom P.carrier (algebraMap E K)
    letI : IsScalarTower E K P.carrier := IsScalarTower.of_algebraMap_eq' rfl
    localInvariant embeddings p brauerClass = (by
      classical
      exact if (nonsplitSignedDeterminant p hp P.data (lt_trans Nat.zero_lt_one hn) (P.outside p hps)).val ∈
        normSubgroup (FiniteCompletion E p) (FiniteCompletion K (placeAbove K p).val)
        then 0 else rationalClass (1 / 2))
  real (w : InfinitePlace E) : realLocalInvariant embeddings w brauerClass = denominatorMap 2 (by decide)
    (((n / 2 + (n - r (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) : ℕ) : ZMod 2))

set_option maxRecDepth 8192 in
/-- The class with the discriminant localization formulas yields the fully
realized profile in even degree. -/
def realizeEvenUnitaryLocalProfileOfDiscriminant (he : Even n)
    (P : InitialUnitaryProfile hn positive a r) (hc : CompatibleUnitaryLocalProfile E a r)
    (h : UnitaryProfileDiscriminantValues hn positive a r P) :
    UnitaryLocalProfileWitness (lt_trans Nat.zero_lt_one hn) positive a r := by
  let hn₀ := lt_trans Nat.zero_lt_one hn
  let A := P.carrier
  let : Algebra E A := Algebra.compHom A (algebraMap E K)
  let : IsScalarTower E K A := IsScalarTower.of_algebraMap_eq' rfl
  let S := evenSignedDeterminantDefectSet P.data hn₀ he.two_dvd a r P.outside hc
    h.embeddings h.brauerClass h.chosen h.splitOutside h.nonsplitOutside h.real
  let t := evenNormCorrection P.data hn₀ he s S.val P.outside S.property.1 S.property.2.1
    S.property.2.2.1 S.property.2.2.2 r P.signatures
  let D : CentralSimpleUnitaryData E K A n :=
    { P.data with toSecondKindInvolution := P.data.toSecondKindInvolution.twist t.val t.property.choose }
  exact unitaryLocalProfileWitnessOfAlgebra D hn₀ positive a r t.property.choose_spec.1
    t.property.choose_spec.2 P.signed

end Langlands.Shimura.FiniteUnitary
