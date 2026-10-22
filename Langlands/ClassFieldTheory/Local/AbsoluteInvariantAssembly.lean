import Langlands.ClassFieldTheory.Local.AbsoluteInvariantStatement
import Langlands.ClassFieldTheory.Local.AbsoluteH2InflationProof
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Langlands.ClassFieldTheory.Local.UnramifiedCommonExtension
import Langlands.ClassFieldTheory.Local.UnramifiedH2Statement
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantCompatibilityStatement
import Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityStatement
import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeStatement
import Langlands.Galois.Local.UnramifiedCriterionProof

noncomputable section

namespace Langlands.ClassFieldTheory.Local.AbsoluteInvariantAssembly

universe u

open Langlands.LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- A finite stage with the actual canonical unramified and Galois certificates. -/
def Stage :=
  {L : FiniteIntermediateExtension F.Carrier //
    IsGalois F.Carrier L.field ∧
    F.canonicalTopologicalData.ramificationIndex =
      (L.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex}

namespace Stage

variable {F}

abbrev field (L : Stage F) := L.val.field
abbrev padic (L : Stage F) := L.val.asPadicField (p := p)

instance (L : Stage F) : IsGalois F.Carrier L.field := L.property.1

abbrev unramified (L : Stage F) := L.property.2

def coordinate (L : Stage F) :
    Gal(L.field/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier L.field)) :=
  by
  letI := L.padic.algebra
  letI : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Classical.choose (arithmeticUnramifiedCoordinateExistence p F L.padic L.unramified)

theorem coordinate_arithmetic (L : Stage F) :
    let : NeZero (Module.finrank F.Carrier L.field) := ⟨Module.finrank_pos.ne'⟩
    IsArithmeticUnramifiedCoordinate F L.field L.coordinate := by
  let := L.padic.algebra
  let : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Classical.choose_spec
    (arithmeticUnramifiedCoordinateExistence p F L.padic L.unramified)

def invariant (L : Stage F) : relativeCohomology F.Carrier L.field 2 →+ RationalModIntegers :=
  by
  letI := L.padic.algebra
  letI : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact unramifiedH2Invariant F L.padic L.unramified L.coordinate

def common (L M : Stage F) : Stage F :=
  let N := commonUnramifiedExtension Langlands.PadicField.canonicalUnramifiedCriterion
    F L.val M.val L.unramified M.unramified
  ⟨N.val, N.property.1, N.property.2.2.2⟩

theorem le_common_left (L M : Stage F) : L.field ≤ (common L M).field :=
  le_sup_left

theorem le_common_right (L M : Stage F) : M.field ≤ (common L M).field :=
  le_sup_right

def inflate (L M : Stage F) (h : L.field ≤ M.field) :
    relativeCohomology F.Carrier L.field 2 →+ relativeCohomology F.Carrier M.field 2 := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower F.Carrier L.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (relativeInflation F.Carrier L.field M.field 2).hom.toAddMonoidHom

theorem inflate_closure
    (hTower : ClosureInflationTowerCompatibility.{u})
    (L M : Stage F) (h : L.field ≤ M.field)
    (x : relativeCohomology F.Carrier L.field 2) :
    closureInflation F.Carrier M.field 2 (inflate L M h x) =
      closureInflation F.Carrier L.field 2 x := by
  let : Algebra L.field M.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower F.Carrier L.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L.field M.field (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact hTower F.Carrier L.field M.field 2 x

theorem inflate_invariant
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    (L M : Stage F) (h : L.field ≤ M.field)
    (x : relativeCohomology F.Carrier L.field 2) :
    M.invariant (inflate L M h x) = L.invariant x := by
  let : Algebra L.field M.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower F.Carrier L.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let := L.padic.algebra
  let : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  let := M.padic.algebra
  let : IsScalarTower (Padic p) F.Carrier M.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact hInv p F L.padic M.padic L.unramified M.unramified
    L.coordinate M.coordinate L.coordinate_arithmetic M.coordinate_arithmetic x

theorem closure_injective (L : Stage F) :
    Function.Injective (closureInflation F.Carrier L.field 2) := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact (AbsoluteH2Assembly.closureInflationExactness F.Carrier L.field).1

end Stage

/-- A finite unramified representative computes the proposed absolute value. -/
def Value (x : absoluteCohomology F.Carrier 2) (q : RationalModIntegers) : Prop :=
  ∃ L : Stage F, ∃ a : relativeCohomology F.Carrier L.field 2,
    closureInflation F.Carrier L.field 2 a = x ∧ L.invariant a = q

theorem value_exists (hEx : UnramifiedH2Exhaustion.{u})
    (x : absoluteCohomology F.Carrier 2) : ∃ q, Value F x q := by
  obtain ⟨L, hGal, hL, a, ha⟩ := hEx p F x
  let S : Stage F := ⟨L, hGal, hL⟩
  exact ⟨S.invariant a, S, a, ha, rfl⟩

theorem value_unique
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    {x : absoluteCohomology F.Carrier 2} {q r : RationalModIntegers}
    (hq : Value F x q) (hr : Value F x r) : q = r := by
  obtain ⟨L, a, ha, rfl⟩ := hq
  obtain ⟨M, b, hb, rfl⟩ := hr
  let N := L.common M
  let a' := Stage.inflate L N (L.le_common_left M) a
  let b' := Stage.inflate M N (L.le_common_right M) b
  have ha' : closureInflation F.Carrier N.field 2 a' = x :=
    (Stage.inflate_closure hTower L N (L.le_common_left M) a).trans ha
  have hb' : closureInflation F.Carrier N.field 2 b' = x :=
    (Stage.inflate_closure hTower M N (L.le_common_right M) b).trans hb
  have hab : a' = b' := N.closure_injective (ha'.trans hb'.symm)
  calc
    L.invariant a = N.invariant a' :=
      (Stage.inflate_invariant hInv L N (L.le_common_left M) a).symm
    _ = N.invariant b' := congrArg N.invariant hab
    _ = M.invariant b :=
      Stage.inflate_invariant hInv M N (L.le_common_right M) b

theorem value_add
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    {x y : absoluteCohomology F.Carrier 2} {q r : RationalModIntegers}
    (hq : Value F x q) (hr : Value F y r) : Value F (x + y) (q + r) := by
  obtain ⟨L, a, ha, rfl⟩ := hq
  obtain ⟨M, b, hb, rfl⟩ := hr
  let N := L.common M
  let a' := Stage.inflate L N (L.le_common_left M) a
  let b' := Stage.inflate M N (L.le_common_right M) b
  refine ⟨N, a' + b', ?_, ?_⟩
  · rw [map_add]
    rw [Stage.inflate_closure hTower, Stage.inflate_closure hTower, ha, hb]
  · rw [map_add]
    rw [Stage.inflate_invariant hInv, Stage.inflate_invariant hInv]

def chosenValue (hEx : UnramifiedH2Exhaustion.{u})
    (x : absoluteCohomology F.Carrier 2) : RationalModIntegers :=
  Classical.choose (value_exists F hEx x)

theorem chosenValue_spec (hEx : UnramifiedH2Exhaustion.{u})
    (x : absoluteCohomology F.Carrier 2) : Value F x (chosenValue F hEx x) :=
  Classical.choose_spec (value_exists F hEx x)

def descendedHom
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u}) :
    absoluteCohomology F.Carrier 2 →+ RationalModIntegers where
  toFun := chosenValue F hEx
  map_zero' := by
    obtain ⟨_, L, _, _, _⟩ := value_exists F hEx 0
    exact value_unique F hTower hInv (chosenValue_spec F hEx 0)
      ⟨L, 0, map_zero _, map_zero _⟩
  map_add' x y :=
    value_unique F hTower hInv (chosenValue_spec F hEx (x + y))
      (value_add F hTower hInv (chosenValue_spec F hEx x) (chosenValue_spec F hEx y))

theorem descendedHom_stage
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    (L : Stage F) (a : relativeCohomology F.Carrier L.field 2) :
    descendedHom F hEx hTower hInv (closureInflation F.Carrier L.field 2 a) =
      L.invariant a :=
  value_unique F hTower hInv (chosenValue_spec F hEx _)
    ⟨L, a, rfl, rfl⟩

theorem descendedHom_injective
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u}) :
    Function.Injective (descendedHom F hEx hTower hInv) := by
  intro x y hxy
  obtain ⟨q, L, a, ha, hq⟩ := value_exists F hEx (x - y)
  have hz : L.invariant a = 0 := by
    rw [← descendedHom_stage F hEx hTower hInv L a, ha, map_sub, hxy, sub_self]
  let := L.padic.algebra
  let : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  have ha0 : a = 0 :=
    unramifiedH2Invariant_injective F L.padic L.unramified L.coordinate
      (hz.trans (map_zero L.invariant).symm)
  apply sub_eq_zero.mp
  rw [← ha, ha0, map_zero]

theorem exists_denominator (q : RationalModIntegers) :
    ∃ n : ℕ, 0 < n ∧ q ∈ denominatorSubgroup n := by
  obtain ⟨r, hr⟩ :=
    QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) q
  change rationalClass r = q at hr
  refine ⟨r.den, r.pos, ?_⟩
  have h := (denominatorEquiv r.den r.pos (r.num : ZMod r.den)).property
  simpa only [denominatorEquiv_intCast, Rat.num_div_den, hr] using h

theorem descendedHom_surjective
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u}) :
    Function.Surjective (descendedHom F hEx hTower hInv) := by
  intro q
  obtain ⟨n, hn, hq⟩ := exists_denominator q
  obtain ⟨L, hGal, hL, hdegree⟩ := unramifiedExtensionDegreeExistence p F n hn
  let S : Stage F := ⟨L, hGal, hL⟩
  let := S.padic.algebra
  let : IsScalarTower (Padic p) F.Carrier S.padic.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hqS : q ∈ S.invariant.range := by
    change q ∈ (unramifiedH2Invariant F S.padic S.unramified S.coordinate).range
    rw [unramifiedH2Invariant_range, hdegree]
    exact hq
  obtain ⟨a, ha⟩ := hqS
  exact ⟨closureInflation F.Carrier S.field 2 a,
    (descendedHom_stage F hEx hTower hInv S a).trans ha⟩

def descendedEquiv
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u}) :
    absoluteCohomology F.Carrier 2 ≃+ RationalModIntegers :=
  AddEquiv.ofBijective (descendedHom F hEx hTower hInv)
    ⟨descendedHom_injective F hEx hTower hInv,
      descendedHom_surjective F hEx hTower hInv⟩

theorem value_restriction
    (hStage : UnramifiedBaseChangeStageExistence.{u})
    (hSquare : ClosureInflationBaseChangeCompatibility.{u})
    (hBase : UnramifiedInvariantBaseChangeCompatibility.{u})
    (E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
      (AlgebraicClosure E.Carrier)]
    {x : absoluteCohomology F.Carrier 2} {q : RationalModIntegers}
    (hx : Value F x q) :
    Value E (absoluteRestriction F.Carrier E.Carrier 2 x)
      (Module.finrank F.Carrier E.Carrier • q) := by
  obtain ⟨L, a, rfl, rfl⟩ := hx
  obtain ⟨M₀, hGal, hUnr, hImage⟩ := hStage p F E L.val L.unramified
  let M : Stage E := ⟨M₀, hGal, hUnr⟩
  let : Algebra F.Carrier M.field :=
    ((algebraMap E.Carrier M.field).comp (algebraMap F.Carrier E.Carrier)).toAlgebra
  let : IsScalarTower F.Carrier E.Carrier M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let f : L.field →+* M.field :=
    ((algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)).comp
      (algebraMap L.field (AlgebraicClosure F.Carrier))).codRestrict M.field hImage
  let : Algebra L.field M.field := f.toAlgebra
  let : IsScalarTower F.Carrier L.field M.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    apply Subtype.ext
    change algebraMap E.Carrier (AlgebraicClosure E.Carrier)
        (algebraMap F.Carrier E.Carrier b) =
      algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
        (algebraMap L.field (AlgebraicClosure F.Carrier)
          (algebraMap F.Carrier L.field b))
    rw [← IsScalarTower.algebraMap_apply F.Carrier L.field
      (AlgebraicClosure F.Carrier),
      ← IsScalarTower.algebraMap_apply F.Carrier (AlgebraicClosure F.Carrier)
        (AlgebraicClosure E.Carrier)]
    rfl
  have hComm (b : L.field) :
      algebraMap M.field (AlgebraicClosure E.Carrier)
          (algebraMap L.field M.field b) =
        algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
          (algebraMap L.field (AlgebraicClosure F.Carrier) b) := rfl
  let b := relativeRestriction F.Carrier E.Carrier M.field 2
    (relativeInflation F.Carrier L.field M.field 2 a)
  refine ⟨M, b, ?_, ?_⟩
  · exact (hSquare F.Carrier E.Carrier L.field M.field hComm 2 a).symm
  · let := L.padic.algebra
    let : IsScalarTower (Padic p) F.Carrier L.padic.Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    let := M.padic.algebra
    let : IsScalarTower (Padic p) E.Carrier M.padic.Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact hBase p F E L.padic M.padic L.unramified M.unramified
      L.coordinate M.coordinate L.coordinate_arithmetic M.coordinate_arithmetic a

theorem descendedHom_restriction
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    (hStage : UnramifiedBaseChangeStageExistence.{u})
    (hSquare : ClosureInflationBaseChangeCompatibility.{u})
    (hBase : UnramifiedInvariantBaseChangeCompatibility.{u})
    (E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier)
      (AlgebraicClosure E.Carrier)]
    (x : absoluteCohomology F.Carrier 2) :
    descendedHom E hEx hTower hInv (absoluteRestriction F.Carrier E.Carrier 2 x) =
      Module.finrank F.Carrier E.Carrier • descendedHom F hEx hTower hInv x :=
  value_unique E hTower hInv (chosenValue_spec E hEx _)
    (value_restriction F hStage hSquare hBase E (chosenValue_spec F hEx x))

theorem absoluteInvariantExistence_of_finite_stages
    (hEx : UnramifiedH2Exhaustion.{u})
    (hTower : ClosureInflationTowerCompatibility.{u})
    (hInv : UnramifiedInvariantInflationCompatibility.{u})
    (hStage : UnramifiedBaseChangeStageExistence.{u})
    (hSquare : ClosureInflationBaseChangeCompatibility.{u})
    (hBase : UnramifiedInvariantBaseChangeCompatibility.{u}) :
    AbsoluteInvariantExistence.{u} := by
  intro p hp
  refine ⟨fun F => descendedEquiv F hEx hTower hInv, ?_⟩
  intro F E _ _ _ _ _ x
  exact descendedHom_restriction F hEx hTower hInv hStage hSquare hBase E x

end Langlands.ClassFieldTheory.Local.AbsoluteInvariantAssembly
