import Langlands.BaseChange.LocalCyclicBaseChangeReductionStatement
import Langlands.BaseChange.CharZeroRankOneSigmaLift
import Langlands.BaseChange.PadicCharacterNormFactors
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof
import Langlands.BushnellKutzko.SupercuspidalConductorRankLowerBoundProof
import Langlands.BushnellKutzko.SupercuspidalSwanLevelProof
import Langlands.LocalField.CanonicalTransport
import Langlands.BaseChange.NormTrivialCharacterGroup
import Langlands.BaseChange.DifferentExponentExistence
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.SigmaOrbitStability
import Langlands.BaseChange.NormTwistFibreReduction
import Langlands.Combinatorics.FiniteOccurrenceMatching
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Correspondence.HenniartBaseChangeSlopeProof
import Langlands.JacquetLanglands.PadicSquareIntegrabilityComparison
import Langlands.LocalField.PadicTowerModuleTopology
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.BaseChange.SigmaLiftOnSupercuspidals

/-! # Reduction of weak cyclic base change to the local σ-lift statements -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped BigOperators

namespace Langlands.BaseChange

open Correspondence GeneralLinear Henniart.Numerical LocalClassField
open BushnellKutzko (SupercuspidalConductorRankLowerBoundStatement)

universe uK uV uW

variable {p : ℕ} [Fact p.Prime]

private local instance (K : PadicField.{uK} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance (K : PadicField.{uK} p) : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance (K : PadicField.{uK} p) : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

local instance (K : PadicField.{uK} p) : CharZero K.Carrier :=
  Algebra.charZero_of_charZero (Padic p) K.Carrier

private local instance (K : PadicField.{uK} p) (n : ℕ) : T2Space (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_t2Space K.Carrier n

private local instance (K : PadicField.{uK} p) (n : ℕ) : LocallyCompactSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace K.Carrier n

private local instance (K : PadicField.{uK} p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace K.Carrier n

private abbrev Cuspidal (K : PadicField.{uK} p) (k : ℕ) :=
  SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat

private abbrev CuspidalRep (K : PadicField.{uK} p) (k : ℕ) :=
  SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1)

/-! ### The cyclic step and its norm characters -/

variable (S : CyclicPrimeStep.{uK} p)

local notation "Fₛ" => S.base.Carrier
local notation "Eₛ" => S.top.Carrier

local instance : Algebra Fₛ Eₛ := S.algebra

local instance : FiniteDimensional Fₛ Eₛ := S.finiteDimensional

local instance : IsModuleTopology Fₛ Eₛ := by
  let := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  exact PadicField.padicTowerModuleTopology p S.base S.top

private theorem cyclicGenerator : ∃ σ : S.Gal, IsCyclicAlgebra σ S.degree := by
  let : IsGalois Fₛ Eₛ := S.isGalois
  let : Fact (Nat.card S.Gal).Prime := ⟨S.card_prime⟩
  have : IsCyclic S.Gal := isCyclic_of_prime_card rfl
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_monoid_generator (α := S.Gal)
  refine ⟨σ, inferInstance, rfl, inferInstance, ?_, ?_⟩
  · rw [S.degree_eq_card]
    exact orderOf_eq_card_of_forall_mem_powers hgen
  · intro x hx
    apply IntermediateField.mem_bot.mp
    apply (IsGalois.mem_bot_iff_fixed x).mpr
    intro g
    obtain ⟨i, rfl⟩ := hgen g
    change (σ ^ i) x = x
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hx]

private def powersEquiv {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) :
    Fin S.degree ≃ S.Gal := by
  let : Finite S.Gal := S.finite_gal
  let : Fintype S.Gal := Fintype.ofFinite _
  let f (i : Fin S.degree) : S.Gal := σ ^ (i : ℕ)
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨?_, ?_⟩)
  · intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ) _ _ hij
    · rw [Set.mem_Iio, hσ.2.2.2.1]
      exact i.isLt
    · rw [Set.mem_Iio, hσ.2.2.2.1]
      exact j.isLt
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, S.degree_eq_card]

private theorem normTrivial_iff (η : QuasiCharacter S.base) :
    IsNormTrivial Eₛ η.toMonoidHom ↔ η ∈ S.normCharacters := by
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact h x
  · intro h x
    exact h ⟨x, rfl⟩

private def normCharacterOfHom (κ : normTrivialCharacterGroup Fₛ Eₛ) : QuasiCharacter S.base := by
  let : NontriviallyNormedField Fₛ := S.base.canonicalNormedField
  let : CompleteSpace Fₛ := inferInstance
  have hopen : IsOpen (κ.val.ker : Set Fₛˣ) := IsNormTrivial.isOpen_ker (L := Eₛ) κ.property
  refine ⟨κ.val, continuous_of_continuousAt_one κ.val ?_⟩
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hopen.mem_nhds (one_mem κ.val.ker)] with x hx
  exact (MonoidHom.mem_ker.mp hx).symm

private def normCharactersEquiv : normTrivialCharacterGroup Fₛ Eₛ ≃ S.normCharacters where
  toFun κ := ⟨normCharacterOfHom S κ, (normTrivial_iff S _).mp κ.property⟩
  invFun η := ⟨η.val.toMonoidHom, (normTrivial_iff S _).mpr η.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (ContinuousMonoidHom.toMonoidHom_injective rfl)

private theorem normCharacters_card {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) :
    Nat.card S.normCharacters = S.degree :=
  (Nat.card_congr (normCharactersEquiv S)).symm.trans (card_normTrivialCharacterGroup hσ)

variable {S}

/-! ### Conjugation and twisting on classes -/

private def cuspidalOfRepresentation (K : PadicField.{uK} p) {k : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (k + 1) K.Carrier) V)
    (hρ : ρ.IsIrreducible) (hsc : IsSupercuspidal ρ) : CuspidalRep.{uK, uV} K k :=
  ⟨SmoothRep.of ρ hsc.1.1, hρ, hsc⟩

private theorem cuspidal_isoClass_eq {K : PadicField.{uK} p} {k : ℕ}
    (A B : CuspidalRep.{uK, uV} K k) :
    A.isoClass = B.isoClass ↔ Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  rw [SupercuspidalRep.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨SmoothRep.equivOfIso ((ObjectProperty.ι _).mapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e)⟩

private def conjugateRep (g : S.Gal) {k : ℕ} (A : CuspidalRep.{uK, uV} S.top k) :
    CuspidalRep.{uK, uV} S.top k :=
  cuspidalOfRepresentation S.top (A.obj.representation.comp (entrywiseAut g (k + 1)).toMonoidHom)
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ (entrywiseAut g (k + 1))).mpr A.property.1)
    (isSupercuspidal_comp_entrywiseAut g _ A.property.2)

private theorem conjugateRep_representation (g : S.Gal) {k : ℕ}
    (A : CuspidalRep.{uK, uV} S.top k) :
    (conjugateRep g A).obj.representation =
      A.obj.representation.comp (entrywiseAut g (k + 1)).toMonoidHom := by
  rfl

private theorem conjugateRep_isoClass (g : S.Gal) {k : ℕ}
    (A : CuspidalRep.{uK, uV} S.top k) :
    (conjugateRep g A).isoClass = S.galoisConjugate g k A.isoClass := by
  apply (cuspidal_isoClass_eq _ _).mpr
  exact ⟨Representation.Equiv.refl _⟩

private theorem galoisConjugate_eq_iff (g : S.Gal) {k : ℕ}
    (A : CuspidalRep.{uK, uV} S.top k) :
    S.galoisConjugate g k A.isoClass = A.isoClass ↔
      Nonempty (A.obj.representation.Equiv
        (A.obj.representation.comp (entrywiseAut g (k + 1)).toMonoidHom)) := by
  rw [← conjugateRep_isoClass]
  exact (cuspidal_isoClass_eq _ _).trans
    ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

private theorem galoisConjugate_one (k : ℕ) (a : Cuspidal.{uK,uV} S.top k) :
    S.galoisConjugate 1 k a = a := by
  let A : CuspidalRep.{uK,uV} S.top k := Quotient.out a
  have ha : A.isoClass = a := Quotient.out_eq a
  rw [← ha]
  apply (galoisConjugate_eq_iff (1 : S.Gal) A).mpr
  have h : A.obj.representation.comp (entrywiseAut (1 : S.Gal) (k + 1)).toMonoidHom =
      A.obj.representation := by
    apply MonoidHom.ext
    intro g
    exact congrArg A.obj.representation (entrywiseAut_one_apply (F := Fₛ) g)
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩

private theorem galoisConjugate_mul (g h : S.Gal) (k : ℕ) (a : Cuspidal.{uK,uV} S.top k) :
    S.galoisConjugate h k (S.galoisConjugate g k a) = S.galoisConjugate (g * h) k a := by
  let A : CuspidalRep.{uK,uV} S.top k := Quotient.out a
  have ha : A.isoClass = a := Quotient.out_eq a
  rw [← ha, ← conjugateRep_isoClass, ← conjugateRep_isoClass, ← conjugateRep_isoClass]
  apply (cuspidal_isoClass_eq _ _).mpr
  simp only [conjugateRep_representation, comp_entrywiseAut_mul]
  exact ⟨Representation.Equiv.refl _⟩

private def blockMultiset (σ : S.Gal) (s k : ℕ) (a : Cuspidal.{uK,uV} S.top k) :
    Multiset (Σ k' : ℕ, Cuspidal.{uK,uV} S.top k') :=
  (List.ofFn (fun i : Fin s => (⟨k, S.galoisConjugate (σ ^ (i : ℕ)) k a⟩ :
    Σ k' : ℕ, Cuspidal.{uK,uV} S.top k')) : List (Σ k' : ℕ, Cuspidal.{uK,uV} S.top k'))

private theorem blockMultiset_one (σ : S.Gal) (k : ℕ) (a : Cuspidal.{uK,uV} S.top k) :
    blockMultiset σ 1 k a = {⟨k, a⟩} := by
  simp [blockMultiset, List.ofFn_succ, galoisConjugate_one]

private theorem blockMultiset_degree {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    (k : ℕ) (a : Cuspidal.{uK,uV} S.top k) :
    blockMultiset σ S.degree k a = S.galoisOrbit a := by
  classical
  let : Fintype S.Gal := Fintype.ofFinite _
  unfold blockMultiset CyclicPrimeStep.galoisOrbit
  rw [← Fin.univ_val_map]
  let f : S.Gal → (Σ j, Cuspidal.{uK,uV} S.top j) := fun g => ⟨k, S.galoisConjugate g k a⟩
  change (Finset.univ.val.map (f ∘ powersEquiv S hσ)) = Finset.univ.val.map f
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

private theorem galoisOrbit_invariant (k : ℕ) (a : Cuspidal.{uK,uV} S.top k) (g : S.Gal) :
    (S.galoisOrbit a).map (S.galoisConjugateSigma g) = S.galoisOrbit a := by
  classical
  let : Fintype S.Gal := Fintype.ofFinite _
  simp only [CyclicPrimeStep.galoisOrbit, Multiset.map_map, Function.comp_def,
    CyclicPrimeStep.galoisConjugateSigma, galoisConjugate_mul]
  let f : S.Gal → (Σ j, Cuspidal.{uK,uV} S.top j) := fun h => ⟨k, S.galoisConjugate h k a⟩
  change (Finset.univ.val.map (f ∘ Equiv.mulRight g)) = Finset.univ.val.map f
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

private def twistRep (η : QuasiCharacter S.base) {k : ℕ} (A : CuspidalRep.{uK,uV} S.base k) :
    CuspidalRep.{uK,uV} S.base k :=
  SupercuspidalRep.twist (determinantQuasiCharacter S.base k.succPNat η)
    (isOpen_ker_determinantQuasiCharacter S.base k.succPNat η)
    (ker_determinant_le_ker_comp η.toMonoidHom) A

private theorem twistRep_isoClass (η : QuasiCharacter S.base) {k : ℕ}
    (A : CuspidalRep.{uK,uV} S.base k) :
    (twistRep η A).isoClass = supercuspidalCharacterTwist S.base k η A.isoClass := rfl

/-! ### Existence, equivalence, and twists of σ-lifts -/

private theorem essentiallySquareIntegrable {k : ℕ} (A : CuspidalRep.{uK,uV} S.base k) :
    JacquetLanglands.IsEssentiallySquareIntegrable A.obj.representation :=
  JacquetLanglands.padicSupercuspidalEssentialSquareIntegrability p S.base
    S.base.canonicalTopologicalData (k + 1) (Nat.succ_pos k) A.obj
    A.obj.representation A.property.1 A.property.2

private structure SigmaLiftData (σ : S.Gal) {n : ℕ}
    (A : SupercuspidalRep.{uK,uV} (F := Fₛ) (n := n)) where
  obj : SmoothRep.{0,uK,uW} ℂ (GeneralLinear n Eₛ)
  admissible : IsAdmissible obj.representation
  irreducible : obj.IsIrreducible
  intertwiner : SigmaIntertwiner σ n obj.representation
  constant : ℂ
  isLift : IsSigmaLift σ S.degree A.obj.representation A.property.2.1 obj.representation
    admissible intertwiner constant

private theorem exists_sigmaLiftData (hDiscrete : DiscreteSeriesSigmaLiftStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ} (A : CuspidalRep.{uK,uV} S.base k) :
    Nonempty (SigmaLiftData.{uK,uV,uV} σ A) := by
  obtain ⟨W, _, _, P, hP, I, c, hirr, h, _⟩ :=
    hDiscrete Fₛ Eₛ σ S.degree (k + 1) hσ A.obj.representation A.property.2.1
      A.property.1 (essentiallySquareIntegrable A)
  exact ⟨⟨SmoothRep.of P hP.1, hP, hirr, I, c, h⟩⟩

private theorem liftEquiv (hUnique : SigmaLiftUniquenessStatement.{uK,uK,uV,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ}
    {A B : CuspidalRep.{uK,uV} S.base k} (hAB : A.isoClass = B.isoClass)
    (L : SigmaLiftData.{uK,uV,uV} σ A) (M : SigmaLiftData.{uK,uV,uV} σ B) :
    Nonempty (L.obj.representation.Equiv M.obj.representation) := by
  obtain ⟨e⟩ := (cuspidal_isoClass_eq B A).mp hAB.symm
  let h := M.isLift.transport A.property.2.1 e M.admissible (Representation.Equiv.refl _)
  exact hUnique Fₛ Eₛ σ S.degree (k + 1) hσ A.obj.representation A.property.2.1 A.property.1
    L.obj.representation L.admissible L.irreducible M.obj.representation M.admissible M.irreducible
    L.intertwiner _ L.constant M.constant L.isLift h

private def shrinkLift {σ : S.Gal} {n : ℕ}
    {A : SupercuspidalRep.{uK,uV} (F := Fₛ) (n := n)} (L : SigmaLiftData.{uK,uV,uW} σ A) :
    Σ L' : SigmaLiftData.{uK,uV,uV} σ A, L.obj.representation.Equiv L'.obj.representation := by
  have h := padicIrreducibleSmoothSmallRealization.{uK,uW,uV} p S.top
    S.top.canonicalTopologicalData n L.obj L.irreducible
  let Q := h.choose
  let e := h.choose_spec.2.some
  let hQ := isAdmissible_of_equiv e L.admissible
  exact ⟨⟨Q, hQ, h.choose_spec.1, L.intertwiner.transport e, L.constant,
    L.isLift.transport A.property.2.1 (Representation.Equiv.refl _) hQ e⟩, e⟩

private def twistLift (hTwist : SigmaLiftTwistStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ}
    {A : CuspidalRep.{uK,uV} S.base k} (L : SigmaLiftData.{uK,uV,uV} σ A)
    (η : QuasiCharacter S.base) (hη : η ∈ S.normCharacters) :
    SigmaLiftData.{uK,uV,uV} σ (twistRep η A) := by
  let ηE : Eₛˣ →* ℂˣ := η.toMonoidHom.comp (Units.map (Algebra.norm Fₛ))
  have hηE : (ηE.comp (determinant (n := k + 1))) = 1 :=
    MonoidHom.ext fun g => (normTrivial_iff S η).mpr hη (determinant g)
  let τ := twist (ηE.comp determinant) L.obj.representation
  have eτ : τ = L.obj.representation := by dsimp only [τ]; rw [hηE, twist_one]
  let A' := twistRep η A
  have htransport (ρ : Representation ℂ (GeneralLinear (k + 1) Eₛ) L.obj)
      (e : ρ = L.obj.representation) :
      let I : SigmaIntertwiner σ (k + 1) ρ := e.symm ▸ L.intertwiner
      let hρ : IsAdmissible ρ := e.symm ▸ L.admissible
      (I : L.obj → L.obj) = L.intertwiner ∧
        (IsSigmaLift σ S.degree A'.obj.representation A'.property.2.1 ρ hρ I L.constant ↔
          IsSigmaLift σ S.degree A'.obj.representation A'.property.2.1
            L.obj.representation L.admissible L.intertwiner L.constant) := by
    subst ρ
    exact ⟨rfl, Iff.rfl⟩
  have h := htransport τ eτ
  let hτ : IsAdmissible τ := eτ.symm ▸ L.admissible
  let I : SigmaIntertwiner σ (k + 1) τ := eτ.symm ▸ L.intertwiner
  have hl := hTwist Fₛ Eₛ σ S.degree (k + 1) hσ A.obj L.obj A.obj.representation
    A.property.2.1 L.obj.representation L.admissible L.intertwiner L.constant η.toMonoidHom
    (Units.continuous_val.comp η.continuous) A'.property.2.1 hτ I h.1 L.isLift
  exact ⟨L.obj, L.admissible, L.irreducible, L.intertwiner, L.constant, h.2.mp hl⟩

private theorem normTwist_fibre (hFibre : SigmaLiftFibreStatement.{uK,uK,uV,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ}
    {A B : CuspidalRep.{uK,uV} S.base k}
    (L : SigmaLiftData.{uK,uV,uV} σ A) (M : SigmaLiftData.{uK,uV,uV} σ B)
    (e : M.obj.representation.Equiv L.obj.representation) :
    ∃ η ∈ S.normCharacters, B.isoClass = supercuspidalCharacterTwist S.base k η A.isoClass := by
  obtain ⟨κ, hκ, he⟩ := hFibre Fₛ Eₛ σ S.degree (k + 1) hσ A.obj B.obj L.obj
    A.obj.representation A.property.2.1 B.obj.representation B.property.2.1 L.obj.representation
    L.admissible A.property.1 B.property.1 L.irreducible (essentiallySquareIntegrable A)
    (essentiallySquareIntegrable B) L.intertwiner (M.intertwiner.transport e) L.constant M.constant
    L.isLift (M.isLift.transport B.property.2.1 (Representation.Equiv.refl _) L.admissible e)
  let η := normCharacterOfHom S ⟨κ, hκ⟩
  exact ⟨η, (normTrivial_iff S η).mp hκ,
    (cuspidal_isoClass_eq B (twistRep η A)).mpr he⟩

private def reindexRepresentation {K : Type uK} [Field K] {m n : ℕ}
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear m K) V) (h : m = n) :
    Representation ℂ (GeneralLinear n K) V :=
  ρ.comp (GeneralLinear.reindex (R := K) (finCongr h)).symm.toMonoidHom

/-! ### Orbit products and their supports -/

private def orbitProductAtRank (σ : S.Gal) {s j n : ℕ}
    (B : CuspidalRep.{uK,uV} S.top j) (hrank : s * (j + 1) = n) :=
  reindexRepresentation (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation) hrank

private structure OrbitPresentation (σ : S.Gal) {k : ℕ} (A : CuspidalRep.{uK,uV} S.base k) where
  lift : SigmaLiftData.{uK,uV,uV} σ A
  s : ℕ
  j : ℕ
  block : CuspidalRep.{uK,uV} S.top j
  rank_eq : s * (j + 1) = k + 1
  stabilizer_card : s = Nat.card (normTwistStabilizer Eₛ A.obj.representation)
  dvd_degree : s ∣ S.degree
  period : ∀ i : ℕ, S.galoisConjugate (σ ^ i) j block.isoClass = block.isoClass ↔ s ∣ i
  equivalent : Nonempty (lift.obj.representation.Equiv (orbitProductAtRank σ block rank_eq))

private theorem exists_orbitPresentation
    (hStructure : CuspidalSigmaLiftStructureStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k}
    (L : SigmaLiftData.{uK,uV,uV} σ A) : Nonempty (OrbitPresentation.{uK,uV} σ A) := by
  obtain ⟨hdvd, n₁, hn₁, hrank, W₁, _, _, P₁, hsc, hirr, hperiod, he⟩ :=
    hStructure Fₛ Eₛ σ S.degree (k + 1) hσ (Nat.succ_pos k) A.obj A.obj.representation
      A.property.2.1 A.property.2 A.property.1 L.obj L.obj.representation L.admissible
      L.irreducible L.intertwiner L.constant L.isLift
  cases n₁ with
  | zero => exact (Nat.lt_irrefl 0 hn₁).elim
  | succ j =>
    let B := cuspidalOfRepresentation S.top P₁ hirr hsc
    exact ⟨⟨L, _, j, B, hrank, rfl, hdvd,
      fun i => (galoisConjugate_eq_iff (σ ^ i) B).trans (hperiod i), he⟩⟩

private def OrbitPresentation.support {σ : S.Gal} {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k}
    (P : OrbitPresentation.{uK,uV} σ A) := blockMultiset σ P.s P.j P.block.isoClass

private theorem orbitProductAtRank_rfl (σ : S.Gal) (s j : ℕ)
    (B : CuspidalRep.{uK,uV} S.top j) :
    orbitProductAtRank σ B (rfl : s * (j + 1) = s * (j + 1)) =
      sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation := by
  simp only [orbitProductAtRank, reindexRepresentation, reindex_finCongr_rfl, MulEquiv.refl_symm]
  rfl

private abbrev topFieldPackage (step : CyclicPrimeStep.{uK} p) :=
  AllFieldBZ.LocalFieldPackage.ofField step.top.Carrier

private abbrev topFieldData (step : CyclicPrimeStep.{uK} p) : (topFieldPackage step).TopologicalData :=
  LocalFieldData.ofInstances step.top.Carrier

private def supportDatum (S : CyclicPrimeStep.{uK} p) (a : Σ j, Cuspidal.{uK,uV} S.top j) :
    AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV,uK} (topFieldData S) :=
  ⟨a.1 + 1, Nat.succ_pos _, a.2⟩

private theorem subquotient_of_product_equiv {K : Type uK} [Field K] (T : LocalFieldData K)
    {n : ℕ} (shape : BlockShape n) :
    letI := T.topology
    ∀ (C : ∀ i, SmoothRep.{0,uK,uV} ℂ (GeneralLinear (shape.size i) K))
      (A : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear n K)),
      A.representation.Equiv (T.normalizedProductInduced shape (fun i => (C i).representation)) →
      SmoothRep.IsSubquotient A ((T.normalizedProductInductionFunctor shape).obj C) := by
  let := T.topology
  intro C A e
  exact SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom e.toIntertwiningMap, e.injective⟩

set_option maxHeartbeats 1200000 in
private theorem support_of_orbitProduct (σ : S.Gal) {s j n : ℕ}
    (B : CuspidalRep.{uK,uV} S.top j) (hrank : s * (j + 1) = n)
    {P : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear n Eₛ)}
    (e : P.representation.Equiv (orbitProductAtRank σ B hrank)) (hirr : P.IsIrreducible) :
    AllFieldBZ.LocalFieldPackage.TopologicalData.IsSupercuspidalSupport (T := topFieldData S) P
      ((blockMultiset σ s j B.isoClass).map (supportDatum S)) := by
  subst n
  let T : LocalFieldData Eₛ := topFieldData S
  let : TopologicalSpace (topFieldPackage S).Carrier := T.topology
  have : IsTopologicalRing (topFieldPackage S).Carrier := (inferInstance : IsTopologicalRing Eₛ)
  let C (i : Fin s) := conjugateRep (σ ^ (i : ℕ)) B
  let ρ (i : Fin s) := supportDatum S (⟨j, (C i).isoClass⟩ : Σ l, Cuspidal.{uK,uV} S.top l)
  have hsum : ∑ i, (ρ i).rank = s * (j + 1) := by simp [ρ, supportDatum]
  refine ⟨s, ρ, ?_, hsum, C, fun _ => rfl, hirr, ?_⟩
  · simp only [blockMultiset, Multiset.map_coe, List.map_ofFn, ρ, C, conjugateRep_isoClass,
      Function.comp_def]
  · have e' : P.representation.Equiv (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation) :=
      orbitProductAtRank_rfl σ s j B ▸ e
    let shape := BlockShape.uniform s (j + 1) (Nat.succ_pos j)
    let factors (i : Fin shape.length) := (C i).obj
    let twisted (i : Fin shape.length) : Representation ℂ (GeneralLinear (j + 1) Eₛ) B.obj :=
      B.obj.representation.comp (entrywiseAut (σ ^ (i : ℕ)) (j + 1)).toMonoidHom
    let ef (i : Fin shape.length) : (twisted i).Equiv (factors i).representation :=
      Representation.Equiv.refl _
    let E := LocalFieldData.normalizedProductInducedEquiv T shape ef
    change SmoothRep.IsSubquotient P ((T.normalizedProductInductionFunctor shape).obj factors)
    exact subquotient_of_product_equiv T shape factors P (e'.trans E)

private theorem supportDatum_injective : Function.Injective (supportDatum.{uK,uV} S) := by
  rintro ⟨j, a⟩ ⟨l, b⟩ hab
  have hjl : j = l := Nat.add_right_cancel (congrArg
    AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.rank hab)
  subst l
  injection hab with _ hcls
  exact congrArg (Sigma.mk j) hcls

private theorem orbitSupport_eq_of_equiv {σ : S.Gal} {s j n s' j' : ℕ}
    {B : CuspidalRep.{uK,uV} S.top j} {B' : CuspidalRep.{uK,uV} S.top j'}
    {h : s * (j + 1) = n} {h' : s' * (j' + 1) = n}
    (e : (orbitProductAtRank σ B h).Equiv (orbitProductAtRank σ B' h'))
    (hn : 0 < n) (hs : IsSmooth (orbitProductAtRank σ B h))
    (hi : (orbitProductAtRank σ B h).IsIrreducible) :
    blockMultiset σ s j B.isoClass = blockMultiset σ s' j' B'.isoClass := by
  let P := SmoothRep.of (orbitProductAtRank σ B h) hs
  have hB := support_of_orbitProduct (P := P) σ B h (Representation.Equiv.refl _) hi
  have hB' := support_of_orbitProduct (P := P) σ B' h' e hi
  apply Multiset.map_injective (supportDatum_injective (S := S))
  exact AllFieldBZ.glSupercuspidalSupportUniqueness.{uV,uK} (topFieldPackage S)
    (topFieldData S) n hn P hi _ _ hB hB'

private theorem OrbitPresentation.support_eq_of_liftEquiv {σ : S.Gal} {k : ℕ}
    {A B : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A)
    (Q : OrbitPresentation.{uK,uV} σ B)
    (e : P.lift.obj.representation.Equiv Q.lift.obj.representation) : P.support = Q.support := by
  let eP := P.equivalent.some
  let eQ := Q.equivalent.some
  exact orbitSupport_eq_of_equiv (eP.symm.trans (e.trans eQ)) (Nat.succ_pos k)
    (isSmooth_of_surjective eP.toIntertwiningMap eP.surjective P.lift.obj.isSmooth)
    ((isIrreducible_iff_of_equiv eP).mp P.lift.irreducible)

set_option maxHeartbeats 1300000 in
private theorem orbitProductEquiv_of_block_matching (σ : S.Gal) (s j : ℕ)
    (B B' : CuspidalRep.{uK,uV} S.top j) (hn : 0 < s * (j + 1))
    (hi : (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation).IsIrreducible)
    (w : Equiv.Perm (Fin s))
    (hw : ∀ i : Fin s,
      S.galoisConjugate (σ ^ ((w i : Fin s) : ℕ)) j B.isoClass =
        S.galoisConjugate (σ ^ (i : ℕ)) j B'.isoClass) :
    Nonempty ((sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation).Equiv
      (sigmaOrbitProduct σ s (Nat.succ_pos j) B'.obj.representation)) := by
  let T := LocalFieldData.ofInstances Eₛ
  let shape := BlockShape.uniform s (j + 1) (Nat.succ_pos j)
  let ρ (i : Fin shape.length) : Representation ℂ (GeneralLinear (j + 1) Eₛ) B.obj :=
    B.obj.representation.comp (entrywiseAut (σ ^ (i : ℕ)) (j + 1)).toMonoidHom
  let ρ' (i : Fin shape.length) : Representation ℂ (GeneralLinear (j + 1) Eₛ) B'.obj :=
    B'.obj.representation.comp (entrywiseAut (σ ^ (i : ℕ)) (j + 1)).toMonoidHom
  have hρi (i : Fin shape.length) : (ρ i).IsIrreducible :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ (entrywiseAut _ _)).mpr B.property.1
  have hρsc (i : Fin shape.length) : IsSupercuspidal (ρ i) :=
    isSupercuspidal_comp_entrywiseAut (σ ^ (i : ℕ)) _ B.property.2
  obtain ⟨e⟩ := T.normalizedProductInduced_equiv_permute_of_irreducible hn shape
    (V := fun _ => B.obj) ρ hρi hρsc hi w
  have hclass (i : Fin shape.length) : Nonempty ((ρ (w i)).Equiv (ρ' i)) := by
    let C := conjugateRep (σ ^ ((w i : Fin s) : ℕ)) B
    let D := conjugateRep (σ ^ (i : ℕ)) B'
    have hCD : C.isoClass = D.isoClass := by
      simpa only [C, D, conjugateRep_isoClass] using hw i
    exact (cuspidal_isoClass_eq C D).mp hCD
  let e' := T.normalizedProductInducedEquiv shape (V := fun _ => B.obj) (W := fun _ => B'.obj)
    (fun i => (hclass i).some)
  exact ⟨e.trans e'⟩

private theorem orbitProductEquiv_of_support_eq (σ : S.Gal) {s j n s' j' : ℕ}
    {B : CuspidalRep.{uK,uV} S.top j} {B' : CuspidalRep.{uK,uV} S.top j'}
    (h : s * (j + 1) = n) (h' : s' * (j' + 1) = n) (hn : 0 < n)
    (hi : (orbitProductAtRank σ B h).IsIrreducible)
    (he : blockMultiset σ s j B.isoClass = blockMultiset σ s' j' B'.isoClass) :
    Nonempty ((orbitProductAtRank σ B h).Equiv (orbitProductAtRank σ B' h')) := by
  have hss : s = s' := by simpa [blockMultiset] using congrArg Multiset.card he
  subst s'
  have hs : 0 < s := Nat.pos_of_ne_zero (fun hz => hn.ne' (by simpa [hz] using h.symm))
  have hjj : j = j' := Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hs (h.trans h'.symm))
  subst j'
  subst n
  have hirr : (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation).IsIrreducible :=
    orbitProductAtRank_rfl σ s j B ▸ hi
  let f (i : Fin s) : Cuspidal.{uK,uV} S.top j := S.galoisConjugate (σ ^ (i : ℕ)) j B.isoClass
  let g (i : Fin s) : Cuspidal.{uK,uV} S.top j := S.galoisConjugate (σ ^ (i : ℕ)) j B'.isoClass
  obtain ⟨w, hw⟩ := Combinatorics.exists_equiv_of_ofFn_multiset_eq
    (fun i => (⟨j, f i⟩ : Σ l, Cuspidal.{uK,uV} S.top l)) (fun i => ⟨j, g i⟩) he
  have hmatch (i : Fin s) : f (w.symm i) = g i := by
    have hc := eq_of_heq (Sigma.mk.inj (hw (w.symm i))).2
    simpa only [Equiv.apply_symm_apply] using hc
  rw [orbitProductAtRank_rfl, orbitProductAtRank_rfl]
  exact orbitProductEquiv_of_block_matching σ s j B B' hn hirr w.symm hmatch

/-! ### The rank, orbit, fibre, and image clauses -/

private theorem normTwistStabilizer_mem_iff {k : ℕ} (A : CuspidalRep.{uK,uV} S.base k)
    (κ : normTrivialCharacterGroup Fₛ Eₛ) :
    κ.val ∈ normTwistStabilizer Eₛ A.obj.representation ↔
      supercuspidalCharacterTwist S.base k (normCharacterOfHom S κ) A.isoClass = A.isoClass := by
  rw [← twistRep_isoClass, cuspidal_isoClass_eq]
  exact ⟨fun h => ⟨h.2.some.symm⟩, fun ⟨e⟩ => ⟨κ.property, ⟨e.symm⟩⟩⟩

private theorem OrbitPresentation.length_one {σ : S.Gal} {k : ℕ}
    {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A)
    (h : ∀ η ∈ S.normCharacters, η ≠ 1 → supercuspidalCharacterTwist S.base k η A.isoClass ≠
      A.isoClass) : P.s = 1 := by
  have eq_bot : normTwistStabilizer Eₛ A.obj.representation = ⊥ := by
    apply le_antisymm _ bot_le
    intro κ hκ
    have hκfix := (normTwistStabilizer_mem_iff A ⟨κ, hκ.1⟩).mp hκ
    have he := not_imp_not.mp (h (normCharacterOfHom S ⟨κ, hκ.1⟩)
      ((normTrivial_iff S _).mp hκ.1)) hκfix
    exact (Subgroup.mem_bot).mpr (congrArg ContinuousMonoidHom.toMonoidHom he)
  rw [P.stabilizer_card, eq_bot, Subgroup.card_bot]

private theorem OrbitPresentation.length_degree {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A)
    (h : ∀ η ∈ S.normCharacters, supercuspidalCharacterTwist S.base k η A.isoClass = A.isoClass) :
    P.s = S.degree := by
  have heq : normTwistStabilizer Eₛ A.obj.representation = normTrivialCharacterGroup Fₛ Eₛ := by
    ext κ
    refine ⟨fun hκ => hκ.1, fun hκ => ?_⟩
    exact (normTwistStabilizer_mem_iff A ⟨κ, hκ⟩).mpr
      (h (normCharacterOfHom S ⟨κ, hκ⟩) ((normTrivial_iff S _).mp hκ))
  rw [P.stabilizer_card, heq, card_normTrivialCharacterGroup hσ]

private theorem OrbitPresentation.sum_rank {σ : S.Gal} {k : ℕ}
    {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A) :
    (P.support.map fun ρ => ρ.1 + 1).sum = k + 1 := by
  simpa [OrbitPresentation.support, blockMultiset, List.sum_ofFn] using P.rank_eq

private theorem OrbitPresentation.degree_free {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A)
    (hs : P.s = S.degree) {g : S.Gal} (hg : g ≠ 1) :
    S.galoisConjugate g P.j P.block.isoClass ≠ P.block.isoClass := by
  obtain ⟨i, rfl⟩ := (powersEquiv S hσ).surjective g
  intro h
  apply hg
  have hdiv := (P.period (i : ℕ)).mp h
  change σ ^ (i : ℕ) = 1
  exact orderOf_dvd_iff_pow_eq_one.mp
    (Eq.mp (congrArg (fun n => n ∣ (i : ℕ)) (hs.trans hσ.2.2.2.1.symm)) hdiv)

private theorem OrbitPresentation.galois_invariant {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A) (g : S.Gal) :
    P.support.map (S.galoisConjugateSigma g) = P.support := by
  rcases (Nat.dvd_prime S.degree_prime).mp P.dvd_degree with h | h
  · obtain ⟨i, rfl⟩ := (powersEquiv S hσ).surjective g
    have hfix : S.galoisConjugate ((powersEquiv S hσ) i) P.j P.block.isoClass =
        P.block.isoClass := (P.period (i : ℕ)).mpr (h ▸ one_dvd (i : ℕ))
    simp only [OrbitPresentation.support, h, blockMultiset_one, Multiset.map_singleton,
      CyclicPrimeStep.galoisConjugateSigma, hfix]
  · rw [OrbitPresentation.support, h, blockMultiset_degree hσ]
    exact galoisOrbit_invariant _ _ g

private theorem OrbitPresentation.support_singleton {σ : S.Gal} {k : ℕ}
    {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A) (h : P.s = 1) :
    ∃ b : Cuspidal.{uK,uV} S.top k, P.support = {⟨k, b⟩} := by
  have hj : P.j = k := by simpa [h] using P.rank_eq
  have hreindex {j l : ℕ} (hjl : j = l) (b : Cuspidal.{uK,uV} S.top j) :
      ∃ b' : Cuspidal.{uK,uV} S.top l, (⟨j, b⟩ : Σ i, Cuspidal.{uK,uV} S.top i) = ⟨l, b'⟩ := by
    subst l
    exact ⟨b, rfl⟩
  obtain ⟨b, hb⟩ := hreindex hj P.block.isoClass
  exact ⟨b, by rw [OrbitPresentation.support, h, blockMultiset_one, hb]⟩

private theorem exists_from_orbit (hConverse : CuspidalSigmaLiftExistenceStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {s j n : ℕ} (hrank : s * (j + 1) = n)
    (B : CuspidalRep.{uK,uV} S.top j)
    (hperiod : ∀ i : ℕ, S.galoisConjugate (σ ^ i) j B.isoClass = B.isoClass ↔ s ∣ i) :
    ∃ (A : SupercuspidalRep.{uK,uV} (F := Fₛ) (n := n))
      (L : SigmaLiftData.{uK,uV,uV} σ A),
      Nonempty (L.obj.representation.Equiv (orbitProductAtRank σ B hrank)) := by
  subst n
  obtain ⟨hPi, hP, V, _, _, π, hπ, I, c, hsc, hi, _, h⟩ :=
    hConverse Fₛ Eₛ σ S.degree hσ s (j + 1) (Nat.succ_pos j) B.obj B.obj.representation
      B.property.2 B.property.1 (fun i => (galoisConjugate_eq_iff (σ ^ i) B).symm.trans (hperiod i))
  let A : SupercuspidalRep.{uK,uV} (F := Fₛ) (n := s * (j + 1)) :=
    ⟨SmoothRep.of π hπ.1, hi, hsc⟩
  let L : SigmaLiftData.{uK,uV,max uK uV} σ A :=
    ⟨SmoothRep.of _ hP.1, hP, hPi, I, c, h⟩
  let small := shrinkLift L
  refine ⟨A, small.1, ?_⟩
  rw [orbitProductAtRank_rfl]
  exact ⟨small.2.symm⟩

private theorem OrbitPresentation.support_eq_of_other_orbit
    (hUnique : SigmaLiftUniquenessStatement.{uK,uK,uV,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k s j : ℕ}
    {A B : CuspidalRep.{uK,uV} S.base k} (hAB : A.isoClass = B.isoClass)
    (P : OrbitPresentation.{uK,uV} σ A) (L : SigmaLiftData.{uK,uV,uV} σ B)
    (C : CuspidalRep.{uK,uV} S.top j) (hrank : s * (j + 1) = k + 1)
    (e : L.obj.representation.Equiv (orbitProductAtRank σ C hrank)) :
    P.support = blockMultiset σ s j C.isoClass := by
  let eP := P.equivalent.some
  let u := (liftEquiv hUnique hσ hAB P.lift L).some
  exact orbitSupport_eq_of_equiv (eP.symm.trans (u.trans e)) (Nat.succ_pos k)
    (isSmooth_of_surjective eP.toIntertwiningMap eP.surjective P.lift.obj.isSmooth)
    ((isIrreducible_iff_of_equiv eP).mp P.lift.irreducible)

private def ConductorClause {σ : S.Gal} {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k}
    (P : OrbitPresentation.{uK,uV} σ A) : Prop :=
  (S.residueDegree : ℤ) *
      (P.support.map fun ρ => (supercuspidalSwanExponent S.top ρ.2 : ℤ)).sum =
    (∑ᶠ η ∈ S.normCharacters,
      (supercuspidalSwanExponent S.base
        (supercuspidalCharacterTwist S.base k η A.isoClass) : ℤ)) -
      (S.residueDegree : ℤ) * S.wildDifferentExponent * ((k : ℤ) + 1)

set_option maxHeartbeats 1000000 in
private theorem assemble_of_conductor
    (hUnique : SigmaLiftUniquenessStatement.{uK,uK,uV,uV,uV})
    (hTwist : SigmaLiftTwistStatement.{uK,uK,uV,uV})
    (hDiscrete : DiscreteSeriesSigmaLiftStatement.{uK,uK,uV,uV})
    (hFibre : SigmaLiftFibreStatement.{uK,uK,uV,uV,uV})
    (hStructure : CuspidalSigmaLiftStructureStatement.{uK,uK,uV,uV})
    (hConverse : CuspidalSigmaLiftExistenceStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    (hW4 : ∀ (k : ℕ) (A : CuspidalRep.{uK,uV} S.base k) (P : OrbitPresentation.{uK,uV} σ A),
      ConductorClause P) :
    ∃ Ch : CyclicBaseChangeMap.{uK,uV} S, IsWeakCyclicBaseChange S Ch ∧
      ∀ (k : ℕ) (a : Cuspidal.{uK,uV} S.base k), ∃ (A₀ : CuspidalRep.{uK,uV} S.base k)
        (_ : A₀.isoClass = a) (P : OrbitPresentation.{uK,uV} σ A₀), Ch k a = P.support := by
  let A (k : ℕ) (a : Cuspidal.{uK,uV} S.base k) : CuspidalRep.{uK,uV} S.base k := Quotient.out a
  have hA (k : ℕ) (a : Cuspidal.{uK,uV} S.base k) : (A k a).isoClass = a := Quotient.out_eq a
  let P (k : ℕ) (a : Cuspidal.{uK,uV} S.base k) : OrbitPresentation.{uK,uV} σ (A k a) :=
    (exists_orbitPresentation hStructure hσ (exists_sigmaLiftData hDiscrete hσ (A k a)).some).some
  let Ch : CyclicBaseChangeMap.{uK,uV} S := fun k a => (P k a).support
  have hCh_twist (k : ℕ) (a : Cuspidal.{uK,uV} S.base k) (η : QuasiCharacter S.base)
      (hη : η ∈ S.normCharacters) : Ch k (supercuspidalCharacterTwist S.base k η a) = Ch k a := by
    let b := supercuspidalCharacterTwist S.base k η a
    let L := (P k a).lift
    let M := twistLift hTwist hσ L η hη
    have hclass : (A k b).isoClass = (twistRep η (A k a)).isoClass := by
      rw [hA, twistRep_isoClass, hA]
    obtain ⟨e⟩ := liftEquiv hUnique hσ hclass (P k b).lift M
    exact (P k b).support_eq_of_liftEquiv (P k a) e
  have hCh_fibre (k : ℕ) (a b : Cuspidal.{uK,uV} S.base k) (he : Ch k b = Ch k a) :
      ∃ η ∈ S.normCharacters, b = supercuspidalCharacterTwist S.base k η a := by
    let e₁ := (P k b).equivalent.some
    let e₂ := (P k a).equivalent.some
    obtain ⟨e⟩ := orbitProductEquiv_of_support_eq σ (P k b).rank_eq (P k a).rank_eq (Nat.succ_pos k)
      ((isIrreducible_iff_of_equiv e₁).mp (P k b).lift.irreducible) he
    obtain ⟨η, hη, h⟩ := normTwist_fibre hFibre hσ (P k a).lift (P k b).lift (e₁.trans (e.trans e₂.symm))
    exact ⟨η, hη, by simpa only [hA] using h⟩
  have hCh_image {k s j : ℕ} (B : CuspidalRep.{uK,uV} S.top j) (hrank : s * (j + 1) = k + 1)
      (hperiod : ∀ i : ℕ, S.galoisConjugate (σ ^ i) j B.isoClass = B.isoClass ↔ s ∣ i) :
      ∃ a : Cuspidal.{uK,uV} S.base k, Ch k a = blockMultiset σ s j B.isoClass := by
    obtain ⟨C, L, ⟨e⟩⟩ := exists_from_orbit hConverse hσ hrank B hperiod
    let a : Cuspidal.{uK,uV} S.base k := C.isoClass
    exact ⟨a, OrbitPresentation.support_eq_of_other_orbit hUnique hσ (hA k a) (P k a) L B hrank e⟩
  refine ⟨Ch, ?_, fun k a => ⟨A k a, hA k a, P k a, rfl⟩⟩
  refine fun k => ⟨?_, ?_, ?_⟩
  · intro a
    let R := P k a
    refine ⟨R.sum_rank, R.galois_invariant hσ, hCh_twist k a, ?_, ?_, ?_⟩
    · intro htrivial
      have hlen := R.length_one (by simpa only [hA] using htrivial)
      refine ⟨R.support_singleton hlen, fun b => ⟨hCh_fibre k a b, ?_⟩⟩
      rintro ⟨η, hη, rfl⟩
      exact hCh_twist k a η hη
    · intro hfull
      have hlen := R.length_degree hσ (by simpa only [hA] using hfull)
      have hRank : S.degree * (R.j + 1) = k + 1 := hlen ▸ R.rank_eq
      refine ⟨⟨R.j + 1, hRank.symm⟩, ⟨R.j, R.block.isoClass, ?_, ?_, ?_⟩, ?_⟩
      · rw [← hRank, Nat.mul_div_cancel_left _ S.degree_prime.pos]
      · exact fun g hg => R.degree_free hσ hlen hg
      · change R.support = S.galoisOrbit R.block.isoClass
        rw [OrbitPresentation.support, hlen, blockMultiset_degree hσ]
      · intro b hb
        obtain ⟨η, hη, he⟩ := hCh_fibre k a b hb
        exact he.trans (hfull η hη)
    · have hw := hW4 k (A k a) R
      simpa only [ConductorClause, hA] using hw
  · intro b hb
    let B : CuspidalRep.{uK,uV} S.top k := Quotient.out b
    have hB : B.isoClass = b := Quotient.out_eq b
    obtain ⟨a, ha⟩ := hCh_image B (Nat.one_mul (k + 1))
      (fun i => iff_of_true (by rw [hB]; exact hb (σ ^ i)) (one_dvd i))
    exact ⟨a, by simpa only [blockMultiset_one, hB] using ha⟩
  · intro j b hdvd hrank hb
    let B : CuspidalRep.{uK,uV} S.top j := Quotient.out b
    have hB : B.isoClass = b := Quotient.out_eq b
    have hRank : S.degree * (j + 1) = k + 1 := by
      rw [hrank, Nat.mul_div_cancel' hdvd]
    have hperiod (i : ℕ) : S.galoisConjugate (σ ^ i) j B.isoClass = B.isoClass ↔ S.degree ∣ i := by
      rw [hB, ← hσ.2.2.2.1, orderOf_dvd_iff_pow_eq_one]
      exact ⟨fun h => not_not.mp (fun hn => hb _ hn h), fun h => h ▸ galoisConjugate_one j b⟩
    obtain ⟨a, ha⟩ := hCh_image B hRank hperiod
    exact ⟨a, by simpa only [blockMultiset_degree hσ, hB] using ha⟩

/-! ### The conductor identity and its finite sum -/

variable (S) in
private theorem residueDegree_spec :
    IsResidueDegree Fₛ Eₛ S.residueDegree :=
  Weil.Local.extensionResidueCardinality S.base S.top S.embedding

set_option maxHeartbeats 900000 in
variable (S) in
private theorem differentExponent_spec :
    IsDifferentExponent Fₛ Eₛ S.differentExponent := by
  let := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  have : ValuativeExtension Fₛ Eₛ := ⟨fun x y => by
    change ValuativeRel.vle (S.embedding x) (S.embedding y) ↔ ValuativeRel.vle x y
    rw [S.top.canonicalTopologicalData_vle, S.base.canonicalTopologicalData_vle,
      Weil.Local.canonicalNorm_map, Weil.Local.canonicalNorm_map]⟩
  have hc := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap Fₛ Eₛ)
  obtain ⟨d, hd⟩ := differentExponentExistence Fₛ Eₛ hc
  have hideal := hd.differentIdeal_eq_maximalIdeal_pow hc
  have he : S.differentExponent = d := by
    unfold CyclicPrimeStep.differentExponent
    dsimp only
    have hinj : Function.Injective (fun n : ℕ =>
        IsLocalRing.maximalIdeal S.top.canonicalTopologicalData.Integers ^ n) :=
      (Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field _)
        (Ideal.IsMaximal.ne_top inferInstance)).injective
    apply le_antisymm (Nat.sInf_le hideal)
    refine le_csInf ⟨d, hideal⟩ ?_
    intro b hb
    exact (hinj (hb.symm.trans hideal)).ge
  exact he.symm ▸ hd

private def normCharacterFinset (S : CyclicPrimeStep.{uK} p) : Finset (QuasiCharacter S.base) :=
  S.normCharacters_finite_ncard.1.toFinset

private theorem mem_normCharacterFinset (S : CyclicPrimeStep.{uK} p) (η : QuasiCharacter S.base) :
    η ∈ normCharacterFinset S ↔ η ∈ S.normCharacters := Set.Finite.mem_toFinset _

private theorem normCharacterFinset_card {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) :
    (normCharacterFinset S).card = S.degree := by
  rw [normCharacterFinset, ← Set.ncard_eq_toFinset_card _ S.normCharacters_finite_ncard.1,
    ← Nat.card_coe_set_eq]
  exact normCharacters_card S hσ

variable (S) in
private def normHomEmbedding : QuasiCharacter S.base ↪ (Fₛˣ →* ℂˣ) :=
  ⟨fun η => η.toMonoidHom, fun _ _ h => ContinuousMonoidHom.toMonoidHom_injective h⟩

variable (S) in
private def normHomFinset : Finset (Fₛˣ →* ℂˣ) :=
  (normCharacterFinset S).map (normHomEmbedding S)

variable (S) in
private theorem mem_normHomFinset (κ : Fₛˣ →* ℂˣ) :
    κ ∈ normHomFinset S ↔ IsNormTrivial Eₛ κ := by
  rw [normHomFinset, Finset.mem_map]
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact (normTrivial_iff S η).mpr ((mem_normCharacterFinset S η).mp hη)
  · intro hκ
    let η := normCharacterOfHom S ⟨κ, hκ⟩
    exact ⟨η, (mem_normCharacterFinset S η).mpr ((normTrivial_iff S η).mp hκ), rfl⟩

private def conductorNat (K : PadicField.{uK} p) {k : ℕ} (a : Cuspidal.{uK,uV} K k) : ℕ :=
  (conductor K a).untopD 0

private theorem conductorNat_cast (K : PadicField.{uK} p) {k : ℕ} (a : Cuspidal.{uK,uV} K k) :
    (conductorNat K a : WithTop ℕ) = conductor K a := by
  obtain ⟨x, hx⟩ := BushnellKutzko.normalizedLevelExistence p K (k + 1) (Nat.succ_pos k)
    (SupercuspidalClass.toSmoothDualClass a)
  obtain ⟨c, hc, _⟩ := BushnellKutzko.supercuspidalSwanLevel p K k a x hx
  simp [conductorNat, hc]

private theorem conductor_identity_finset
    (hConductor : CuspidalSigmaLiftConductorStatement.{uK,uK,uV,uV}) {σ : S.Gal}
    (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k}
    (P : OrbitPresentation.{uK,uV} σ A) :
    ∑ η ∈ normCharacterFinset S, conductorNat S.base
        (supercuspidalCharacterTwist S.base k η A.isoClass) =
      S.residueDegree * (P.s * conductorNat S.top P.block.isoClass + (k + 1) * S.differentExponent) := by
  have h := hConductor Fₛ Eₛ σ S.degree hσ k A.obj A.obj.representation A.property.2.1
    A.property.2 A.property.1 P.s P.j P.rank_eq P.block.obj P.block.obj.representation
    P.block.property.2 P.block.property.1 P.lift.obj P.lift.obj.representation P.lift.admissible
    P.equivalent P.lift.intertwiner P.lift.constant P.lift.isLift S.residueDegree S.differentExponent
    (residueDegree_spec S) (differentExponent_spec S) (normHomFinset S) (mem_normHomFinset S)
  rw [normHomFinset, Finset.sum_map] at h
  have h' : ∑ η ∈ normCharacterFinset S, conductor S.base
      (supercuspidalCharacterTwist S.base k η A.isoClass) =
      (S.residueDegree : WithTop ℕ) * ((P.s : WithTop ℕ) * conductor S.top P.block.isoClass +
        ((k + 1 : ℕ) : WithTop ℕ) * (S.differentExponent : WithTop ℕ)) := by
    simp only [← twistRep_isoClass, Henniart.Numerical.conductor, SupercuspidalClass.firstFixedLevel_isoClass]
    exact h
  simp_rw [← conductorNat_cast] at h'
  exact_mod_cast h'

/-! ### The rank-one correction -/

private theorem conductorNat_rankOne (K : PadicField.{uK} p) (A : CuspidalRep.{uK,uV} K 0)
    (χ : QuasiCharacter K) (e : A.obj.representation.Equiv (RankinSelberg.rankOneCharacter χ.toMonoidHom)) :
    conductorNat K A.isoClass = K.canonicalTopologicalData.multiplicativeConductor χ := by
  have h : Henniart.Numerical.conductor K A.isoClass =
      (K.canonicalTopologicalData.toLocalFieldData.multiplicativeConductor χ : WithTop ℕ) :=
    Conductor.firstFixedLevel_eq_multiplicativeConductor χ e
  rw [K.canonicalTopologicalData.toLocalFieldData_multiplicativeConductor] at h
  simp [conductorNat, h]

private theorem conductorZero_iff_unramified (K : PadicField.{uK} p) (χ : QuasiCharacter K) :
    K.canonicalTopologicalData.multiplicativeConductor χ = 0 ↔
      K.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom := by
  let T := K.canonicalTopologicalData
  rw [T.multiplicativeConductor_eq_zero_iff, PadicField.TopologicalData.IsUnramifiedCharacter,
    ← T.ker_ordUnits]
  have h (a : K.Carrierˣ) : T.discreteValuation a = 1 ↔ T.ord a = 0 :=
    ((T.normalizedAbs_eq_one_iff_discreteValuation _).symm.trans
      (T.ord_eq_zero_iff_normalizedAbs a).symm)
  exact ⟨fun H a ha => H a ((h a).mpr ha), fun H a ha => H ((h a).mp ha)⟩

private theorem rankOne_zero_galois_fixed (g : S.Gal) (B : CuspidalRep.{uK,uV} S.top 0)
    (hb : conductorNat S.top B.isoClass = 0) : S.galoisConjugate g 0 B.isoClass = B.isoClass := by
  obtain ⟨χ, ⟨e⟩⟩ := GodementJacquet.exists_tateCharacterModel B.obj.representation B.property.2.1 B.property.1
  let T := S.top.canonicalTopologicalData
  have hχ : T.multiplicativeConductor χ = 0 := (conductorNat_rankOne S.top B χ e).symm.trans hb
  have hu := T.eq_unramifiedCharacter χ.toMonoidHom ((conductorZero_iff_unramified S.top χ).mp hχ)
  have heq : (RankinSelberg.rankOneCharacter χ.toMonoidHom).comp (entrywiseAut g 1).toMonoidHom =
      RankinSelberg.rankOneCharacter χ.toMonoidHom := by
    rw [hu]
    apply MonoidHom.ext
    intro x
    have hval : ((determinant (entrywiseAut g 1 x) : Eₛˣ) : Eₛ) = g (determinant x : Eₛ) := by
      change (determinant (Matrix.GeneralLinearGroup.map g.toRingHom x) : Eₛ) = _
      rw [Matrix.GeneralLinearGroup.map_det]
      rfl
    have ho := PadicField.CanonicalTransport.ord_map S.top S.top (S.galoisAutomorphism g)
      (determinant x : Eₛ)
    have hchar : T.unramifiedCharacter (χ T.uniformizerUnit) (determinant (entrywiseAut g 1 x)) =
        T.unramifiedCharacter (χ T.uniformizerUnit) (determinant x) := by
      rw [T.unramifiedCharacter_apply, T.unramifiedCharacter_apply, hval]
      exact congrArg (fun n : ℤ => (χ T.uniformizerUnit) ^ n) ho
    exact congrArg (fun a : ℂˣ => (a : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) hchar
  let e' : Representation.Equiv (B.obj.representation.comp (entrywiseAut g 1).toMonoidHom)
      (RankinSelberg.rankOneCharacter χ.toMonoidHom) :=
    heq ▸ CuspidalSupport.equivComp e (entrywiseAut g 1).toMonoidHom
  exact (galoisConjugate_eq_iff g B).mpr ⟨e.trans e'.symm⟩

private theorem conductorNat_twist_rankOne {A : CuspidalRep.{uK,uV} S.base 0}
    {χ : QuasiCharacter S.base} (e : A.obj.representation.Equiv
      (RankinSelberg.rankOneCharacter χ.toMonoidHom)) (η : QuasiCharacter S.base) :
    conductorNat S.base (supercuspidalCharacterTwist S.base 0 η A.isoClass) =
      S.base.canonicalTopologicalData.multiplicativeConductor (η * χ) := by
  rw [← twistRep_isoClass]
  apply conductorNat_rankOne S.base (twistRep η A) (η * χ)
  have hcanonical : twist (η.toMonoidHom.comp determinant)
      (RankinSelberg.rankOneCharacter χ.toMonoidHom) =
      RankinSelberg.rankOneCharacter (η * χ).toMonoidHom := by
    ext g
    simp [RankinSelberg.rankOneCharacter, characterRepresentation, twist]
  exact hcanonical ▸ twistEquiv (η.toMonoidHom.comp determinant) e

private theorem natDegree_lPolynomial (K : PadicField.{uK} p) (χ : QuasiCharacter K) :
    (LocalFactor.PadicAbelian.lPolynomial K.canonicalTopologicalData χ).natDegree =
      1 - K.canonicalTopologicalData.multiplicativeConductor χ := by
  let T := K.canonicalTopologicalData
  by_cases h : T.multiplicativeConductor χ = 0
  · have hlin : (Polynomial.C (χ T.uniformizerUnit : ℂ) * Polynomial.X).natDegree = 1 := by
      simp [(χ T.uniformizerUnit).ne_zero]
    have hlt : (1 : Polynomial ℂ).natDegree <
        (Polynomial.C (χ T.uniformizerUnit : ℂ) * Polynomial.X).natDegree := by
      rw [Polynomial.natDegree_one, hlin]
      exact Nat.zero_lt_one
    rw [LocalFactor.PadicAbelian.lPolynomial, ite_eq_left h,
      Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt, hlin, h, Nat.sub_zero]
  · have hge : 1 ≤ T.multiplicativeConductor χ := Nat.pos_of_ne_zero h
    rw [LocalFactor.PadicAbelian.lPolynomial, ite_eq_right h, Polynomial.natDegree_one,
      Nat.sub_eq_zero_of_le hge]

set_option maxHeartbeats 900000 in
private theorem rankOne_defect_sum {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree)
    {A : CuspidalRep.{uK,uV} S.base 0} (P : OrbitPresentation.{uK,uV} σ A) :
    ∑ η ∈ normCharacterFinset S, (1 - conductorNat S.base
      (supercuspidalCharacterTwist S.base 0 η A.isoClass)) =
    S.residueDegree * P.s * (P.j + 1 - conductorNat S.top P.block.isoClass) := by
  classical
  obtain ⟨L, s, j, B, hrank, hstab, hdvd, hperiod, hproduct⟩ := P
  dsimp only
  clear hstab hdvd hperiod
  have hₛ : s ≠ 0 := fun hz => by simp [hz] at hrank
  have hs : s = 1 := le_antisymm
    ((Nat.le_mul_of_pos_right s (Nat.succ_pos j)).trans_eq hrank) (Nat.pos_of_ne_zero hₛ)
  have hj : j = 0 := by
    simpa [hs] using hrank
  subst s j
  obtain ⟨χ, ⟨eχ⟩⟩ := GodementJacquet.exists_tateCharacterModel A.obj.representation A.property.2.1 A.property.1
  obtain ⟨ψ, ⟨eψ⟩⟩ := GodementJacquet.exists_tateCharacterModel B.obj.representation B.property.2.1 B.property.1
  obtain ⟨eBlock⟩ := sigmaOrbitProduct_one_equiv σ (Nat.succ_pos 0)
    B.obj.representation B.property.2.1.1
  let eLift : L.obj.representation.Equiv B.obj.representation := hproduct.some.trans eBlock
  have hNorm := charZeroRankOneSigmaLiftNormPullback Fₛ Eₛ σ S.degree hσ A.obj L.obj
    A.obj.representation A.property.2.1 L.obj.representation L.admissible L.intertwiner L.constant
    L.isLift χ ψ eχ (eLift.trans eψ)
  let := Weil.Local.extensionAlgebra_isScalarTower S.base S.top S.embedding
  let Q := normCharacterFinset S
  let X := normHomFinset S
  let ξ (κ : X) : QuasiCharacter S.base :=
    normCharacterOfHom S ⟨κ.val, (mem_normHomFinset S _).mp κ.property⟩ * χ
  have hpol := prod_lPolynomial_normTwists S.base.canonicalTopologicalData S.top.canonicalTopologicalData
    (residueDegree_spec S) χ X (mem_normHomFinset S) ξ (fun _ => rfl)
  have hu : χ.comp (localNorm S.base.canonicalTopologicalData S.top.canonicalTopologicalData) = ψ :=
    ContinuousMonoidHom.toMonoidHom_injective hNorm.symm
  rw [hu] at hpol
  have hdeg := congrArg Polynomial.natDegree hpol
  rw [Polynomial.natDegree_prod _ _ (fun κ _ => LocalFactor.PadicAbelian.lPolynomial_ne_zero _ _),
    Polynomial.natDegree_expand] at hdeg
  simp_rw [natDegree_lPolynomial] at hdeg
  have htwists : ∑ η ∈ Q, (1 - conductorNat S.base
      (supercuspidalCharacterTwist S.base 0 η A.isoClass)) =
      ∑ κ : X, (1 - S.base.canonicalTopologicalData.multiplicativeConductor (ξ κ)) := by
    rw [← Finset.sum_coe_sort]
    apply Fintype.sum_equiv (Finset.equivMap (normHomEmbedding S) Q)
    intro η
    rw [conductorNat_twist_rankOne eχ]
    rfl
  rw [htwists, hdeg, conductorNat_rankOne S.top B ψ eψ]
  simp only [mul_one, zero_add]
  exact Nat.mul_comm _ _

/-! ### The truncated conductor identity -/

private theorem rank_le_conductorNat
    (hLower : SupercuspidalConductorRankLowerBoundStatement.{uK,uV})
    (K : PadicField.{uK} p) {k : ℕ} (hk : 0 < k) (a : Cuspidal.{uK,uV} K k) :
    k + 1 ≤ conductorNat K a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have h := hLower p K m a
  rw [← conductorNat_cast] at h
  exact_mod_cast h

private theorem rank_le_block_conductorNat
    (hLower : SupercuspidalConductorRankLowerBoundStatement.{uK,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ} (hk : 0 < k)
    {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A) :
    P.j + 1 ≤ conductorNat S.top P.block.isoClass := by
  by_cases hj : 0 < P.j
  · exact rank_le_conductorNat hLower S.top hj _
  · have hj₀ : P.j = 0 := by omega
    have hlen : P.s = S.degree := by
      rcases (Nat.dvd_prime S.degree_prime).mp P.dvd_degree with h | h
      · have hr := P.rank_eq
        simp [h, hj₀] at hr
        omega
      · exact h
    have hσ₁ : σ ≠ 1 := by
      intro heq
      have h := hσ.2.2.2.1
      rw [heq, orderOf_one] at h
      exact S.degree_prime.ne_one h.symm
    by_contra! hz
    have hzero : conductorNat S.top P.block.isoClass = 0 := by omega
    have hfixed {j : ℕ} (B : CuspidalRep.{uK,uV} S.top j) (h : j = 0)
        (hc : conductorNat S.top B.isoClass = 0) :
        S.galoisConjugate σ j B.isoClass = B.isoClass := by
      subst j
      exact rankOne_zero_galois_fixed σ B hc
    exact (P.degree_free hσ hlen hσ₁) (hfixed P.block hj₀ hzero)

private theorem conductor_defect_sum
    (hLower : SupercuspidalConductorRankLowerBoundStatement.{uK,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ}
    {A : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A) :
    ∑ η ∈ normCharacterFinset S, (k + 1 - conductorNat S.base
      (supercuspidalCharacterTwist S.base k η A.isoClass)) =
    S.residueDegree * P.s * (P.j + 1 - conductorNat S.top P.block.isoClass) := by
  rcases k with _ | k
  · exact rankOne_defect_sum hσ P
  · have ht := rank_le_block_conductorNat hLower hσ (Nat.succ_pos k) P
    have hb (η : QuasiCharacter S.base) := rank_le_conductorNat hLower S.base (Nat.succ_pos k)
      (supercuspidalCharacterTwist S.base k.succ η A.isoClass)
    simp only [Nat.sub_eq_zero_of_le ht, Nat.sub_eq_zero_of_le (hb _), Finset.sum_const_zero, mul_zero]

private theorem cast_nat_sub_with_defect (a n : ℕ) :
    ((a - n : ℕ) : ℤ) = (a : ℤ) - n + ((n - a : ℕ) : ℤ) := by omega

private theorem conductorClause_of_identity
    (hLower : SupercuspidalConductorRankLowerBoundStatement.{uK,uV})
    (hConductor : CuspidalSigmaLiftConductorStatement.{uK,uK,uV,uV}) {σ : S.Gal}
    (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ} {A : CuspidalRep.{uK,uV} S.base k}
    (P : OrbitPresentation.{uK,uV} σ A) : ConductorClause P := by
  let f := S.residueDegree
  let Q := normCharacterFinset S
  let n := k + 1
  let m := P.j + 1
  let a (η : QuasiCharacter S.base) := conductorNat S.base
    (supercuspidalCharacterTwist S.base k η A.isoClass)
  let b := conductorNat S.top P.block.isoClass
  have hsum : ∑ η ∈ Q, (a η : ℤ) = (f : ℤ) * (P.s * b + n * S.differentExponent) := by
    exact_mod_cast conductor_identity_finset hConductor hσ P
  have hdefect : ∑ η ∈ Q, ((n - a η : ℕ) : ℤ) = (f : ℤ) * P.s * (m - b : ℕ) := by
    exact_mod_cast conductor_defect_sum hLower hσ P
  have hdeg : (S.ramificationIndex : ℤ) * f = S.degree := by
    exact_mod_cast S.ramificationIndex_mul_residueDegree
  have hrank : (P.s : ℤ) * m = n := by exact_mod_cast P.rank_eq
  have hcard : (Q.card : ℤ) = S.degree := by exact_mod_cast normCharacterFinset_card hσ
  have htop : (P.support.map (fun ρ => (supercuspidalSwanExponent S.top ρ.2 : ℤ))).sum =
      (P.s : ℤ) * ((b - m : ℕ) : ℤ) := by
    simp [OrbitPresentation.support, blockMultiset, S.conductor_galoisConjugate,
      Function.comp_def, supercuspidalSwanExponent, b, m, conductorNat]
  have hbase : ∑ η ∈ Q, ((a η - n : ℕ) : ℤ) =
      (f : ℤ) * (P.s * b + n * S.differentExponent) - S.degree * (n : ℤ) +
        (f : ℤ) * P.s * (m - b : ℕ) := by
    have hsub (η : QuasiCharacter S.base) := cast_nat_sub_with_defect (a η) n
    simp_rw [hsub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hdefect, Finset.sum_const,
      nsmul_eq_mul, hcard]
  unfold ConductorClause
  rw [htop, finsum_mem_eq_finite_toFinset_sum _ S.normCharacters_finite_ncard.1]
  change (f : ℤ) * ((P.s : ℤ) * ((b - m : ℕ) : ℤ)) =
    (∑ η ∈ Q, ((a η - n : ℕ) : ℤ)) - (f : ℤ) * S.wildDifferentExponent * (n : ℤ)
  rw [hbase, cast_nat_sub_with_defect b m, ← hdeg, CyclicPrimeStep.wildDifferentExponent]
  linear_combination -(f : ℤ) * hrank

/-! ### Certification by σ-lifts for the chosen generator -/

/-- The orbit product, defined through the general local-field data of the instances, is
equivalent to the normalized product induction of the canonical p-adic data with the same
blocks: both are normalized inductions for definitionally equal half-modulus characters. -/
private theorem sigmaOrbitProduct_equiv_canonical (σ : S.Gal) (s : ℕ) {n : ℕ} (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n Eₛ) W) :
    Nonempty ((sigmaOrbitProduct σ s hn τ).Equiv
      (S.top.canonicalTopologicalData.normalizedProductInduced (BlockShape.uniform s n hn)
        (fun i => τ.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom))) := by
  let T := S.top.canonicalTopologicalData
  have hRing : @IsTopologicalRing Eₛ T.topology _ := inferInstance
  let B := BlockShape.uniform s n hn
  let ρ := B.blockTensor (fun i => τ.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
  have key : ∀ χ χ' : Induction.SmoothCharacter ℂ (B.Levi Eₛ), χ = χ' →
      Nonempty ((@BlockShape.normalizedInducedOf Eₛ _ T.topology hRing _ B _ _ _ χ ρ).Equiv
        (@BlockShape.normalizedInducedOf Eₛ _ T.topology hRing _ B _ _ _ χ' ρ)) := by
    rintro χ _ rfl
    exact ⟨Representation.Equiv.refl _⟩
  unfold PadicField.TopologicalData.normalizedProductInduced
    PadicField.TopologicalData.normalizedParabolicInduced
  unfold sigmaOrbitProduct LocalFieldData.normalizedProductInduced
    LocalFieldData.normalizedParabolicInduced
  exact key (T.toLocalFieldData.leviHalfCharacter B) (T.leviHalfCharacter B) rfl

private theorem padicSubquotient_of_product_equiv {K : PadicField.{uK} p} (T : K.TopologicalData)
    {n : ℕ} (shape : BlockShape n) :
    letI := T.topology
    ∀ (C : ∀ i, SmoothRep.{0,uK,uV} ℂ (GeneralLinear (shape.size i) K.Carrier))
      (A : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear n K.Carrier)),
      A.representation.Equiv (T.normalizedProductInduced shape (fun i => (C i).representation)) →
      SmoothRep.IsSubquotient A ((T.normalizedProductInductionFunctor shape).obj C) := by
  let := T.topology
  intro C A e
  exact SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom e.toIntertwiningMap, e.injective⟩

/-- An irreducible representation equivalent to the orbit product of a block has the multiset
of the classes of the conjugate blocks, read as p-adic cuspidal data, as a supercuspidal
support. -/
private theorem padicSupport_of_orbitProduct (σ : S.Gal) {s j n : ℕ}
    (B : CuspidalRep.{uK,uV} S.top j) (hrank : s * (j + 1) = n)
    {P : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear n Eₛ)}
    (e : P.representation.Equiv (orbitProductAtRank σ B hrank)) (hirr : P.IsIrreducible) :
    S.top.canonicalTopologicalData.IsSupercuspidalSupport P
      ((blockMultiset σ s j B.isoClass).map (supercuspidalSupportDatum S.top)) := by
  subst n
  let C (i : Fin s) := conjugateRep (σ ^ (i : ℕ)) B
  let ρ (i : Fin s) := supercuspidalSupportDatum S.top
    (⟨j, (C i).isoClass⟩ : Σ l, Cuspidal.{uK,uV} S.top l)
  have hsum : ∑ i, (ρ i).rank = s * (j + 1) := by simp [ρ]
  refine ⟨s, ρ, ?_, hsum, C, fun _ => rfl, hirr, ?_⟩
  · simp only [blockMultiset, Multiset.map_coe, List.map_ofFn, ρ, C, conjugateRep_isoClass,
      Function.comp_def]
  · have e' : P.representation.Equiv
        (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation) :=
      orbitProductAtRank_rfl σ s j B ▸ e
    let T := S.top.canonicalTopologicalData
    let shape := BlockShape.uniform s (j + 1) (Nat.succ_pos j)
    have b : (sigmaOrbitProduct σ s (Nat.succ_pos j) B.obj.representation).Equiv
        (T.normalizedProductInduced shape (fun i =>
          B.obj.representation.comp (entrywiseAut (σ ^ (i : ℕ)) (j + 1)).toMonoidHom)) :=
      (sigmaOrbitProduct_equiv_canonical σ s (Nat.succ_pos j) B.obj.representation).some
    let ef (i : Fin shape.length) :
        Representation.Equiv
          (B.obj.representation.comp (entrywiseAut (σ ^ (i : ℕ)) (j + 1)).toMonoidHom)
          (C i).obj.representation :=
      Representation.Equiv.refl _
    let E := T.normalizedProductInducedEquiv shape ef
    change SmoothRep.IsSubquotient P ((T.normalizedProductInductionFunctor shape).obj
      fun i => (C i).obj)
    exact padicSubquotient_of_product_equiv T shape (fun i => (C i).obj) P ((e'.trans b).trans E)

/-- The σ-lift of an orbit presentation, carried to the orbit product, is a σ-lift of every
representative of the same class and has the support of the presentation. -/
private theorem OrbitPresentation.certify {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) {k : ℕ}
    {A₀ : CuspidalRep.{uK,uV} S.base k} (P : OrbitPresentation.{uK,uV} σ A₀)
    (A : CuspidalRep.{uK,uV} S.base k) (hA : A₀.isoClass = A.isoClass) :
    ∃ (τ : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear (k + 1) Eₛ))
      (hτ : IsAdmissible τ.representation)
      (I : SigmaIntertwiner σ (k + 1) τ.representation) (c : ℂ),
      IsSigmaLift σ (orderOf σ) A.obj.representation A.property.2.1 τ.representation hτ I c ∧
        S.top.canonicalTopologicalData.IsSupercuspidalSupport τ
          (P.support.map (supercuspidalSupportDatum S.top)) := by
  let eP := P.equivalent.some
  let τ : SmoothRep.{0,uK,max uK uV} ℂ (GeneralLinear (k + 1) Eₛ) :=
    SmoothRep.of (orbitProductAtRank σ P.block P.rank_eq)
      (isSmooth_of_surjective eP.toIntertwiningMap eP.surjective P.lift.obj.isSmooth)
  have hτ : IsAdmissible τ.representation := isAdmissible_of_equiv eP P.lift.admissible
  obtain ⟨eA⟩ := (cuspidal_isoClass_eq A₀ A).mp hA
  refine ⟨τ, hτ, P.lift.intertwiner.transport eP, P.lift.constant, ?_, ?_⟩
  · rw [hσ.2.2.2.1]
    exact P.lift.isLift.transport A.property.2.1 eA hτ eP
  · exact padicSupport_of_orbitProduct σ P.block P.rank_eq (Representation.Equiv.refl _)
      ((isIrreducible_iff_of_equiv eP).mp P.lift.irreducible)

variable (S) in
/-- For every generator `σ` of `S.Gal`, the map built from the σ-lifts of supercuspidal
representations and their orbit decompositions is a weak cyclic base change and is certified by
σ-lifts on supercuspidal classes. -/
theorem exists_weakCyclicBaseChange_sigmaLiftOnSupercuspidals
    (hUnique : SigmaLiftUniquenessStatement.{uK,uK,uV,uV,uV})
    (hTwist : SigmaLiftTwistStatement.{uK,uK,uV,uV})
    (hDiscrete : DiscreteSeriesSigmaLiftStatement.{uK,uK,uV,uV})
    (hFibre : SigmaLiftFibreStatement.{uK,uK,uV,uV,uV})
    (hStructure : CuspidalSigmaLiftStructureStatement.{uK,uK,uV,uV})
    (hConverse : CuspidalSigmaLiftExistenceStatement.{uK,uK,uV,uV})
    (hConductor : CuspidalSigmaLiftConductorStatement.{uK,uK,uV,uV})
    {σ : S.Gal} (hσ : IsCyclicAlgebra σ S.degree) :
    ∃ Ch : CyclicBaseChangeMap.{uK,uV} S, IsWeakCyclicBaseChange S Ch ∧
      IsSigmaLiftOnSupercuspidals.{uK,uV} S.embedding Ch σ := by
  obtain ⟨Ch, hW, hP⟩ := assemble_of_conductor hUnique hTwist hDiscrete hFibre hStructure
    hConverse hσ (fun _ _ P => conductorClause_of_identity
      BushnellKutzko.supercuspidalConductorRankLowerBound.{uK,uV} hConductor hσ P)
  refine ⟨Ch, hW, fun k π A hA => ?_⟩
  obtain ⟨A₀, hA₀, P, hCh⟩ := hP k π
  rw [hCh]
  exact P.certify hσ A (hA₀.trans hA.symm)

/-- The seven local σ-lift statements imply weak cyclic base change of prime degree. -/
theorem localCyclicBaseChangeReduction : LocalCyclicBaseChangeReductionStatement.{uK,uV} := by
  intro hUnique hTwist hDiscrete hFibre hStructure hConverse hConductor p _ S
  obtain ⟨σ, hσ⟩ := cyclicGenerator S
  exact (exists_weakCyclicBaseChange_sigmaLiftOnSupercuspidals S hUnique hTwist hDiscrete
    hFibre hStructure hConverse hConductor hσ).imp fun _ h => h.1

end Langlands.BaseChange
