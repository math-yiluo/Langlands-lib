import Langlands.Geometry.FormalGroup.DrinfeldLineCentralizerDivision
import Langlands.Geometry.FormalGroup.DivisibleHomFaithfulness
import Mathlib.NumberTheory.LocalField.Basic

/-! # The integral commutant of the reduced Lubin–Tate line -/

noncomputable section

namespace Langlands.FormalGroup

universe u v

namespace ModuleLaw

open CategoryTheory
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {σ : Type} [Finite σ]

/-- A Cauchy sequence specified by the successive uniformizer divisibilities has
an integral limit with the corresponding congruences. -/
theorem exists_scalar_limit [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) (a : ℕ → O)
    (ha : ∀ n, π ^ n ∣ a (n + 1) - a n) : ∃ L : O, ∀ n, π ^ n ∣ L - a n := by
  have hdvd {n m : ℕ} (hnm : n ≤ m) : π ^ n ∣ a m - a n := by
    induction m, hnm using Nat.le_induction with
    | base => rw [sub_self]; exact dvd_zero _
    | succ m hm ih =>
      rw [← sub_add_sub_cancel (a (m + 1)) (a m) (a n)]
      exact dvd_add ((pow_dvd_pow π hm).trans (ha m)) ih
  have hc : IsPrecomplete (IsLocalRing.maximalIdeal O) O := inferInstance
  obtain ⟨L, hL⟩ := hc.prec (f := a) (by
    intro m n hmn
    apply SModEq.symm
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hπ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hdvd hmn)
  refine ⟨L, fun n => ?_⟩
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] using (hL n).symm

/-- Successive integral scalar digits determine a formal endomorphism on a
uniformizer-power torsion module. -/
theorem exists_scalarHom_of_digits [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (M : ModuleLaw O R σ) {π : O} (hπ : Irreducible π) (ht : M.IsPiPowerTorsion π)
    (P : Hom M M → Prop)
    (hd : ∀ f, P f → ∃ b : O, ∃ g : { g : Hom M M // P g }, f = M.scalarHom b + π • g.val)
    (z : Hom M M) (hz : P z) : ∃ a : O, M.scalarHom a = z := by
  let digit (f : { g : Hom M M // P g }) : O := (hd f.val f.property).choose
  let rest (f : { g : Hom M M // P g }) : { g : Hom M M // P g } :=
    (hd f.val f.property).choose_spec.choose
  have hdigit (f : { g : Hom M M // P g }) : f.val = M.scalarHom (digit f) + π • (rest f).val :=
    (hd f.val f.property).choose_spec.choose_spec
  let t : ℕ → O × { g : Hom M M // P g } :=
    Nat.rec (0, ⟨z, hz⟩) (fun n s => (s.1 + π ^ n * digit s.2, rest s.2))
  have hstep (n : ℕ) : π ^ n ∣ (t (n + 1)).1 - (t n).1 := by
    change π ^ n ∣ (t n).1 + π ^ n * digit (t n).2 - (t n).1
    rw [add_sub_cancel_left]
    exact dvd_mul_right _ _
  have happ (n : ℕ) : z = M.scalarHom (t n).1 + π ^ n • (t n).2.val := by
    induction n with
    | zero => simp [t, scalarHom]
    | succ n ih =>
      change z = M.scalarHom ((t n).1 + π ^ n * digit (t n).2) + π ^ (n + 1) • (rest (t n).2).val
      calc
        _ = _ := ih
        _ = _ := by
          rw [hdigit (t n).2, smul_add, ← mul_smul, ← pow_succ]
          simp only [scalarHom, add_smul, mul_smul, add_assoc]
  obtain ⟨a, ha⟩ := exists_scalar_limit hπ (fun n => (t n).1) hstep
  refine ⟨a, ?_⟩
  apply Hom.ext_onAlgebraPoints
  intro A x
  obtain ⟨n, hn⟩ := ht A x
  obtain ⟨b, hb⟩ := ha n
  have ha' : a = (t n).1 + π ^ n * b := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hb
  have hs : M.scalarHom a = M.scalarHom (t n).1 + π ^ n • (b • Hom.id M) := by
    rw [ha']
    simp only [scalarHom, add_smul, mul_smul]
  have hdiff : M.scalarHom a - z = π ^ n • (b • Hom.id M - (t n).2.val) := by
    conv_lhs => rw [hs, happ n]
    rw [add_sub_add_left_eq_sub, smul_sub]
  let ev := (Hom.onPointsLinear (κ := Empty)).comp
    (Hom.mapLinear (M := M) (N := M) (IsScalarTower.toAlgHom O R A))
  let x' : (M.map (IsScalarTower.toAlgHom O R A)).Point Empty := x
  change ev (M.scalarHom a) x' = ev z x'
  apply sub_eq_zero.mp
  calc
    _ = ev (M.scalarHom a - z) x' := by rw [map_sub, LinearMap.sub_apply]
    _ = _ := by
      rw [hdiff]
      change (π ^ n • (b • Hom.id M - (t n).2.val)).onAlgebraPoints x = 0
      rw [Hom.onAlgebraPoints_smul, ← map_smul, hn, map_zero]

end ModuleLaw

namespace LocalDivision

open ValuativeRel CentralDivision CentralSimple IsLocalRing ModuleLaw
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
local instance lineIntegralCentralizerLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable [Finite (ResidueField (SubfieldIntegerRing K D ι))]
variable (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) {π : 𝒪[K]} (hπ : Irreducible π)

local notation "C" => SubfieldIntegerRing K D ι
local notation "H" => drinfeldLubinTateLine ι χ hL hπ
local notation "EndH" => ModuleLaw.Hom H H
local notation "fc" => drinfeldLineCoefficientEnd ι χ hL hπ

variable (p : ℕ) [ExpChar κ p] {e : ℕ} (hcard : Nat.card 𝓀[K] = p ^ e)
variable (σ : L ≃ₐ[K] L)
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "tc" => drinfeldLineFrobeniusEnd ι χ hL hπ p hcard σ hσ

/-- The subring of integral scalar-linear endomorphisms commuting with the
embedded integers and arithmetic Frobenius. -/
def drinfeldLineCentralizer : Subring EndH :=
  Subring.centralizer (Set.range fc ∪ {tc})

theorem mem_drinfeldLineCentralizer (f : EndH) :
    f ∈ drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ ↔
      (∀ a : C, Commute f (fc a)) ∧ Commute f tc := by
  change f ∈ Subring.centralizer (Set.range fc ∪ {tc}) ↔ _
  rw [Subring.mem_centralizer_iff]
  constructor
  · intro hf
    exact ⟨fun a => (hf _ (Or.inl ⟨a, rfl⟩)).symm, (hf _ (Or.inr rfl)).symm⟩
  · rintro ⟨hf, ht⟩ _ (⟨a, rfl⟩ | rfl)
    exacts [(hf a).symm.eq, ht.symm.eq]

variable [Algebra.IsAlgebraic 𝓀[K] κ]

include hcard in
/-- The reduced Lubin–Tate line is divisible by the original scalar uniformizer. -/
theorem drinfeldLine_isPiDivisible : (H).IsPiDivisible π := by
  let θ := subfieldReductionCharacter ι χ
  have hz : θ (algebraMap 𝒪[K] C π) = 0 := by
    change χ (residue C (algebraMap 𝒪[K] C π)) = 0
    rw [LubinTateStandard.residue_uniformizer _ (subfieldMaximalIdeal_eq_uniformizer ι hL hπ), map_zero]
  exact (hasPiHeight_of_scalarFrobenius H hcard ((θ.commutes π).symm.trans hz)
    (drinfeldLubinTateLine_uniformizer_frobenius ι χ hL hπ p hcard) (reducedDegree_pos K D)).1

/-- The integral commutant of the reduced line consists exactly of the original scalar order. -/
def drinfeldLineScalarEndEquiv : 𝒪[K] ≃+* drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  let S := drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ
  let f : 𝒪[K] →+* S :=
    { toFun := fun a => ⟨(H).scalarHom a, (mem_drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ _).mpr
        ⟨fun b => (Hom.comp_scalarHom (fc b) a).symm, (Hom.comp_scalarHom tc a).symm⟩⟩
      map_zero' := Subtype.ext (zero_smul _ _)
      map_one' := Subtype.ext ((H).scalarHom_one)
      map_add' := fun a b => Subtype.ext (add_smul a b _)
      map_mul' := fun a b => Subtype.ext ((H).scalarHom_mul a b) }
  have hH := drinfeldLine_isPiDivisible ι χ hL hπ p hcard
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply sub_eq_zero.mp
    by_contra hn
    obtain ⟨n, c, hc⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hπ
    have hf : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hf' : (H).scalarHom (a - b) = 0 := congrArg Subtype.val hf
    have hzero : π ^ n • ((c : 𝒪[K]) • Hom.id H) = π ^ n • (0 : EndH) := by
      simpa only [hc, scalarHom, mul_smul, smul_comm (c : 𝒪[K]), smul_zero] using hf'
    have hc0 := hH.smul_pow_injective n hzero
    have hid := congrArg (fun y : EndH => (↑c⁻¹ : 𝒪[K]) • y) hc0
    have hid0 : (Hom.id H : EndH) = 0 := by
      simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using hid
    have hz := congrArg (fun g : EndH => CommLaw.Hom.lineDerivative (H).groupLaw g.toHom) hid0
    change CommLaw.Hom.lineDerivative (H).groupLaw 1 = CommLaw.Hom.lineDerivative (H).groupLaw 0 at hz
    exact one_ne_zero (by simpa only [map_one, map_zero] using hz)
  · intro z
    have hp (g : EndH) : g ∈ S ↔ (∀ b : C, Commute g (fc b)) ∧ Commute g tc :=
      mem_drinfeldLineCentralizer ι χ hL hπ p hcard σ hσ g
    obtain ⟨a, ha⟩ := exists_scalarHom_of_digits H hπ hH.torsion (fun g => g ∈ S) (by
      intro g hg
      obtain ⟨b, g', hcoeff, hfrob, hd⟩ :=
        drinfeldLine_scalar_digit ι χ hL hπ p hcard σ hσ g ((hp g).mp hg).1 ((hp g).mp hg).2
      exact ⟨b, ⟨g', (hp g').mpr ⟨hcoeff, hfrob⟩⟩, hd⟩) z.val z.property
    exact ⟨a, Subtype.ext ha⟩

@[simp]
theorem drinfeldLineScalarEndEquiv_apply (a : 𝒪[K]) :
    (drinfeldLineScalarEndEquiv ι χ hL hπ p hcard σ hσ a).val = (H).scalarHom a := rfl

end LocalDivision
end Langlands.FormalGroup
