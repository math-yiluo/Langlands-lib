import Langlands.Representation.Character.WeightedTest
import Langlands.BaseChange.EllipticDiscreteTraceSeparationStatement
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.RankOneNormNeighborhood
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Localization
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.Representation.Finite.AbelianNormalBrauer
import Langlands.Representation.Twist.UnitaryModCenterProof
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.Representation.Category.UniverseLift

/-! # Twist rigidity of essentially square-integrable traces on elliptic determinant regions -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory
open Langlands.FiniteRep.AbelianNormalBrauer
open scoped BigOperators IsMulCommutative

universe u v uV uV'

section NormTests

open Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- A function whose nonzero values all lie at norms has vanishing orbital integrals at every
regular semisimple non-norm. -/
theorem vanishesOffNorms_of_isNorm_support
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    {σ : E ≃ₐ[F] E} {l n : ℕ} (hE : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μ : Measure (GeneralLinear n F)) {f : GeneralLinear n F → ℂ}
    (hf : ∀ g, f g ≠ 0 → IsNorm σ l g) :
    VanishesOffNorms σ l μ f := by
  intro γ _ hγ μγ _ _ νγ _
  have hzero : twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ f = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [twistedOrbitFunction_mk, MonoidHom.id_apply, Pi.zero_apply]
      by_contra hx
      obtain ⟨δ, hδ⟩ := hf _ hx
      exact hγ ⟨δ, by simpa [mul_assoc] using hδ.twistedConj hE.pow_eq_one 1 x⁻¹⟩
  simp only [orbitalIntegral, twistedOrbitalIntegral, hzero, Pi.zero_apply, integral_zero]

end NormTests

section NormSubgroup

open CharZeroLocalField LocalField LocalClassField

/-- For a cyclic field extension `E/F` of nonarchimedean local fields of characteristic zero, the
norm subgroup `N_{E/F}(Eˣ)` of `Fˣ` is open and of finite index (local class field theory). -/
theorem IsCyclicAlgebra.normRange_isOpen_finiteIndex
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type v} [Field E] [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ}
    (hE : IsCyclicAlgebra σ l) :
    IsOpen ((Units.map (Algebra.norm F : E →* F)).range : Set Fˣ) ∧
      (Units.map (Algebra.norm F : E →* F)).range.FiniteIndex := by
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : FiniteDimensional F E := hE.1
  let : IsGalois F E := hE.isGalois
  let : IsAbelianGalois F E := hE.isAbelianGalois
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier L.Carrier := hE.1
  let : IsAbelianGalois K.Carrier L.Carrier := (inferInstance : IsAbelianGalois F E)
  change IsOpen (normSubgroup K.Carrier L.Carrier : Set K.Carrierˣ) ∧
    (normSubgroup K.Carrier L.Carrier).FiniteIndex
  exact ⟨isOpen_normSubgroup_of_isAbelianGalois T L.canonicalTopologicalData,
    Subgroup.finiteIndex_iff.mpr
    (by rw [NormUnitImage.normSubgroup_index_eq_finrank K L]; exact Module.finrank_pos.ne')⟩

end NormSubgroup

section Averaging

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem unitary_of_finite_character {Q : Type*} [Group Q] [Finite Q]
    (χ : Q →* ℂˣ) (x : Q) : ‖(χ x : ℂ)‖ = 1 := by
  have hpow : ‖(χ x : ℂ)‖ ^ orderOf x = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one,
      Units.val_one, norm_one]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (orderOf_pos x).ne').mp
    (hpow.trans (one_pow _).symm)

private theorem isEssentiallySquareIntegrable_twist_unitary
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F) V}
    (hρ : IsEssentiallySquareIntegrable ρ)
    (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hunit : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    IsEssentiallySquareIntegrable (twist χ ρ) := by
  obtain ⟨s, hs⟩ := hρ
  refine ⟨s, ?_⟩
  have he : realPowerTwist (determinantNorm F n) (-s) (twist χ ρ) =
      twist χ (realPowerTwist (determinantNorm F n) (-s) ρ) := by
    ext g x
    change (realPowerCharacter (determinantNorm F n) (-s) g : ℂ) • ((χ g : ℂ) • ρ g x) =
      (χ g : ℂ) • ((realPowerCharacter (determinantNorm F n) (-s) g : ℂ) • ρ g x)
    rw [smul_comm]
  rw [he]
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  intro μ _
  exact isSquareIntegrableModCenter_unitaryTwist χ hχ hunit μ (hs μ)

private theorem sum_distribution_twists
    {Q : Type*} [CommGroup Q] [Fintype Q]
    (d : G →* Q) (hc : IsClopen {g | d g = 1})
    (hloc : ∀ χ : Q →* ℂˣ, IsLocallyConstant fun g => (χ (d g) : ℂ))
    (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (htwist : ∀ χ : Q →* ℂˣ, IsAdmissible (twist (χ.comp d) ρ))
    (f : SchwartzBruhat G) :
    letI := charFintype (A := Q)
    (∑ χ : Q →* ℂˣ, Character.distribution μ (twist (χ.comp d) ρ) (htwist χ) f) =
      (Nat.card Q : ℂ) *
        Character.distribution μ ρ hρ (ConcordanceLocalization.cutoff hc f) := by
  classical
  let := charFintype (A := Q)
  have hterm (χ : Q →* ℂˣ) :
      Character.distribution μ (twist (χ.comp d) ρ) (htwist χ) f =
        Character.distribution μ ρ hρ (Character.weightedTest (χ.comp d) (hloc χ) f) :=
    Character.distribution_twist_weightedTest μ ρ hρ (χ.comp d) (hloc χ) (htwist χ) f
  simp_rw [hterm]
  rw [← map_sum]
  have hsum : (∑ χ : Q →* ℂˣ, Character.weightedTest (χ.comp d) (hloc χ) f) =
      (Nat.card Q : ℂ) • ConcordanceLocalization.cutoff hc f := by
    apply Subtype.ext
    funext g
    let ev : SchwartzBruhat G →ₗ[ℂ] ℂ :=
      (LinearMap.proj g).comp (schwartzBruhatSubmodule G).subtype
    change ev (∑ χ : Q →* ℂˣ, Character.weightedTest (χ.comp d) (hloc χ) f) =
      (Nat.card Q : ℂ) * ConcordanceLocalization.cutoff hc f g
    rw [map_sum, ConcordanceLocalization.cutoff_apply]
    change (∑ χ : Q →* ℂˣ, (χ (d g) : ℂ) * f g) =
      (Nat.card Q : ℂ) * (if d g = 1 then f g else 0)
    rw [← Finset.sum_mul, sum_char_apply]
    split <;> simp [*]
  rw [hsum, map_smul, smul_eq_mul]

end Averaging

section Rigidity

open ConcordanceLocalization

/-- Twist rigidity on an elliptic determinant region, from finite elliptic trace separation: if
the trace of `π'` is `t` times the trace of `π` on the tests supported in the regular elliptic
elements with determinant in an open subgroup `H` of finite index of `Fˣ`, then `t ≠ 0` and
`π' ≅ (κ ∘ det) ⊗ π` for a character `κ` of `Fˣ` trivial on `H`. -/
theorem ellipticTwistRigidity_of_separation
    (hSep : EllipticDiscreteTraceSeparationStatement.{u, u, max uV uV', uV'})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (n : ℕ) (hn : 0 < n) (H : Subgroup Fˣ) (hH : IsOpen (H : Set Fˣ))
    [H.FiniteIndex] :
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
      (π' : Representation ℂ (GeneralLinear n F) V') (hπ' : IsAdmissible π'),
      π.IsIrreducible → π'.IsIrreducible →
      IsEssentiallySquareIntegrable π → IsEssentiallySquareIntegrable π' →
      ∀ t : ℂ,
        (∀ f : SchwartzBruhat (GeneralLinear n F), IsEllipticSupported f →
          (∀ g, f g ≠ 0 → GeneralLinear.determinant g ∈ H) →
          Character.distribution μ π' hπ' f = t * Character.distribution μ π hπ f) →
        t ≠ 0 ∧ ∃ κ : Fˣ →* ℂˣ, (∀ x ∈ H, κ x = 1) ∧
          Nonempty (π'.Equiv (twist (κ.comp GeneralLinear.determinant) π)) := by
  classical
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  intro μ _ V _ _ V' _ _ π hπ π' hπ' hi hi' hsq hsq' t htrace
  let Q := Fˣ ⧸ H
  let : Fintype Q := Fintype.ofFinite Q
  let : IsMulCommutative Q := IsMulCommutative.of_comm (mul_comm (G := Q))
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hH
  let q := QuotientGroup.mk' H
  let d : GeneralLinear n F →* Q := q.comp GeneralLinear.determinant
  have hd : Continuous d :=
    QuotientGroup.continuous_mk.comp Matrix.GeneralLinearGroup.continuous_det
  have hdet (g : GeneralLinear n F) : d g = 1 ↔ GeneralLinear.determinant g ∈ H :=
    QuotientGroup.eq_one_iff _
  have hc : IsClopen {g | d g = 1} := (isClopen_discrete ({1} : Set Q)).preimage hd
  let D := Q →* ℂˣ
  let : Fintype D := charFintype (A := Q)
  have hloc (χ : D) : IsLocallyConstant (fun g => (χ (d g) : ℂ)) :=
    (IsLocallyConstant.of_discrete (fun x : Q => (χ x : ℂ))).comp_continuous hd
  have hopen (χ : D) : IsOpen ((χ.comp d).ker : Set (GeneralLinear n F)) :=
    ((IsLocallyConstant.of_discrete (χ : Q → ℂˣ)).comp_continuous hd).isOpen_fiber 1
  let T₁ (χ : D) := twist (χ.comp d) π
  let T₂ (χ : D) := twist (χ.comp d) π'
  have h₁ (χ : D) : IsAdmissible (T₁ χ) := (isAdmissible_twist_iff _ π (hopen χ)).mpr hπ
  have h₂ (χ : D) : IsAdmissible (T₂ χ) := (isAdmissible_twist_iff _ π' (hopen χ)).mpr hπ'
  have hi₁ (χ : D) : (T₁ χ).IsIrreducible := (isIrreducible_twist_iff _ π).mpr hi
  have hi₂ (χ : D) : (T₂ χ).IsIrreducible := (isIrreducible_twist_iff _ π').mpr hi'
  have hsq₁ (χ : D) : IsEssentiallySquareIntegrable (T₁ χ) :=
    isEssentiallySquareIntegrable_twist_unitary hsq _ (hopen χ)
      (fun g => unitary_of_finite_character χ (d g))
  have hsq₂ (χ : D) : IsEssentiallySquareIntegrable (T₂ χ) :=
    isEssentiallySquareIntegrable_twist_unitary hsq' _ (hopen χ)
      (fun g => unitary_of_finite_character χ (d g))
  let tr₁ (χ : D) := Character.distribution μ (T₁ χ) (h₁ χ)
  let tr₂ (χ : D) := Character.distribution μ (T₂ χ) (h₂ χ)
  -- Averaging over the characters of `Fˣ/H`.
  have havg (f : SchwartzBruhat (GeneralLinear n F)) (hf : IsEllipticSupported f) :
      (∑ χ : D, tr₂ χ f) = t * ∑ χ : D, tr₁ χ f := by
    have hcut (g : GeneralLinear n F) (hg : cutoff hc f g ≠ 0) :
        f g ≠ 0 ∧ d g = 1 := by
      have hm : g ∈ Function.support (cutoff hc f) := hg
      rw [support_cutoff] at hm
      exact hm
    have e := htrace (cutoff hc f) (fun g hg => hf g (hcut g hg).1)
      (fun g hg => (hdet g).mp (hcut g hg).2)
    change (∑ χ : D, Character.distribution μ (twist (χ.comp d) π') (h₂ χ) f) =
      t * ∑ χ : D, Character.distribution μ (twist (χ.comp d) π) (h₁ χ) f
    rw [sum_distribution_twists (Q := Q) d hc hloc μ π' hπ' h₂ f,
      sum_distribution_twists (Q := Q) d hc hloc μ π hπ h₁ f, e]
    ring
  -- The self-twists of `π'` and the others.
  let p (χ : D) : Prop := Nonempty (π'.Equiv (T₂ χ))
  let S := Finset.univ.filter p
  have hone : (1 : D) ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have e : T₂ 1 = π' := by
      ext g x
      change ((1 : ℂˣ) : ℂ) • π' g x = π' g x
      simp
    exact ⟨e.symm ▸ Representation.Equiv.refl π'⟩
  have hm : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨1, hone⟩).ne'
  let D₂ := {χ : D // ¬ p χ}
  have hsplit (f : SchwartzBruhat (GeneralLinear n F)) (hf : IsEllipticSupported f) :
      (S.card : ℂ) * Character.distribution μ π' hπ' f + ∑ χ : D₂, tr₂ χ.val f =
        t * ∑ χ : D, tr₁ χ f := by
    have hstab : (∑ χ ∈ S, tr₂ χ f) = (S.card : ℂ) * Character.distribution μ π' hπ' f := by
      calc
        (∑ χ ∈ S, tr₂ χ f) = ∑ _χ ∈ S, Character.distribution μ π' hπ' f := by
          apply Finset.sum_congr rfl
          intro χ hχ
          let e := (Finset.mem_filter.mp hχ).2.some
          exact DFunLike.congr_fun (Character.distribution_eq_of_equiv μ hπ' (h₂ χ) e).symm f
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ p (fun χ => tr₂ χ f)
    change (∑ χ ∈ S, tr₂ χ f) + (∑ χ ∈ Finset.univ.filter (fun χ => ¬ p χ), tr₂ χ f) =
      ∑ χ : D, tr₂ χ f at h
    rw [hstab, ← Finset.sum_subtype_eq_sum_filter, havg f hf] at h
    simpa only [Finset.subtype_univ] using h
  -- The non-self-twists of `π'`, on a common carrier universe.
  let carriers₂ : D₂ → Type (max uV uV') := fun _ => ULift.{uV} V'
  let _ : ∀ j : D₂, AddCommGroup (carriers₂ j) :=
    fun _ => (ULift.addCommGroup : AddCommGroup (ULift.{uV} V'))
  let _ : ∀ j : D₂, Module ℂ (carriers₂ j) :=
    fun _ => (ULift.module' : Module ℂ (ULift.{uV} V'))
  let reps₂ : (j : D₂) → Representation ℂ (GeneralLinear n F) (carriers₂ j) :=
    fun χ => universeLiftRepresentation.{uV} (T₂ χ.val)
  have hr₂ (j : D₂) : IsAdmissible (reps₂ j) :=
    (isAdmissible_iff_of_equiv (universeLiftEquiv (T₂ j.val))).mp (h₂ j.val)
  have hright₂ (f : SchwartzBruhat (GeneralLinear n F)) (j : D₂) :
      Character.distribution μ (reps₂ j) (hr₂ j) f = tr₂ j.val f :=
    DFunLike.congr_fun (Character.distribution_eq_of_equiv μ (h₂ j.val) (hr₂ j)
      (universeLiftEquiv (T₂ j.val))).symm f
  have hir₂ (j : D₂) : (reps₂ j).IsIrreducible :=
    (isIrreducible_iff_of_equiv (universeLiftEquiv (T₂ j.val))).mp (hi₂ j.val)
  have hsr₂ (j : D₂) : IsEssentiallySquareIntegrable (reps₂ j) :=
    (isEssentiallySquareIntegrable_iff_of_equiv (universeLiftEquiv (T₂ j.val))).mp (hsq₂ j.val)
  -- The factor is nonzero.
  have ht : t ≠ 0 := by
    rintro rfl
    have hlin (f : SchwartzBruhat (GeneralLinear n F)) (hf : IsEllipticSupported f) :
        Character.distribution μ π' hπ' f =
          ∑ j : D₂, (-(S.card : ℂ)⁻¹) * Character.distribution μ (reps₂ j) (hr₂ j) f := by
      have h := hsplit f hf
      rw [zero_mul] at h
      simp only [hright₂, ← Finset.mul_sum]
      field_simp
      linear_combination h
    obtain ⟨j, ⟨e⟩⟩ := hSep F n hn μ D₂ carriers₂ V' reps₂ π' hr₂ hπ' hir₂ hi' hsr₂ hsq'
      (fun _ => -(S.card : ℂ)⁻¹) hlin
    exact j.property ⟨e.trans (universeLiftEquiv (T₂ j.val)).symm⟩
  refine ⟨ht, ?_⟩
  -- All twists of `π` together with the non-self-twists of `π'`.
  let J := D ⊕ D₂
  let carriers : J → Type (max uV uV') :=
    Sum.elim (fun _ => ULift.{uV'} V) (fun _ => ULift.{uV} V')
  let _ : ∀ j : J, AddCommGroup (carriers j) :=
    Sum.rec (motive := fun j : J => AddCommGroup (carriers j))
      (fun _ => (ULift.addCommGroup : AddCommGroup (ULift.{uV'} V)))
      (fun _ => (ULift.addCommGroup : AddCommGroup (ULift.{uV} V')))
  let _ : ∀ j : J, Module ℂ (carriers j) :=
    Sum.rec (motive := fun j : J => Module ℂ (carriers j))
      (fun _ => (ULift.module' : Module ℂ (ULift.{uV'} V)))
      (fun _ => (ULift.module' : Module ℂ (ULift.{uV} V')))
  let reps : (j : J) → Representation ℂ (GeneralLinear n F) (carriers j) :=
    Sum.rec (motive := fun j : J => Representation ℂ (GeneralLinear n F) (carriers j))
      (fun χ => universeLiftRepresentation.{uV'} (T₁ χ))
      (fun χ => universeLiftRepresentation.{uV} (T₂ χ.val))
  have hr (j : J) : IsAdmissible (reps j) := by
    cases j with
    | inl χ => exact (isAdmissible_iff_of_equiv
        (universeLiftEquiv (T₁ χ))).mp (h₁ χ)
    | inr χ => exact (isAdmissible_iff_of_equiv
        (universeLiftEquiv (T₂ χ.val))).mp (h₂ χ.val)
  have hir (j : J) : (reps j).IsIrreducible := by
    cases j with
    | inl χ => exact (isIrreducible_iff_of_equiv
        (universeLiftEquiv (T₁ χ))).mp (hi₁ χ)
    | inr χ => exact (isIrreducible_iff_of_equiv
        (universeLiftEquiv (T₂ χ.val))).mp (hi₂ χ.val)
  have hsr (j : J) : IsEssentiallySquareIntegrable (reps j) := by
    cases j with
    | inl χ => exact (isEssentiallySquareIntegrable_iff_of_equiv
        (universeLiftEquiv (T₁ χ))).mp (hsq₁ χ)
    | inr χ => exact (isEssentiallySquareIntegrable_iff_of_equiv
        (universeLiftEquiv (T₂ χ.val))).mp (hsq₂ χ.val)
  let coef : J → ℂ := Sum.elim (fun _ => t / (S.card : ℂ)) (fun _ => -(S.card : ℂ)⁻¹)
  have hlinear (f : SchwartzBruhat (GeneralLinear n F)) (hf : IsEllipticSupported f) :
      Character.distribution μ π' hπ' f =
        ∑ j : J, coef j * Character.distribution μ (reps j) (hr j) f := by
    have h := hsplit f hf
    have hleft (χ : D) :
        Character.distribution μ (reps (.inl χ)) (hr (.inl χ)) f = tr₁ χ f :=
      DFunLike.congr_fun (Character.distribution_eq_of_equiv μ (h₁ χ) (hr (.inl χ))
        (universeLiftEquiv (T₁ χ))).symm f
    have hright (χ : D₂) :
        Character.distribution μ (reps (.inr χ)) (hr (.inr χ)) f = tr₂ χ.val f :=
      DFunLike.congr_fun (Character.distribution_eq_of_equiv μ (h₂ χ.val) (hr (.inr χ))
        (universeLiftEquiv (T₂ χ.val))).symm f
    rw [Fintype.sum_sum_type]
    simp only [coef, Sum.elim_inl, Sum.elim_inr, hleft, hright, ← Finset.mul_sum]
    apply (mul_right_inj' hm).mp
    calc
      (S.card : ℂ) * Character.distribution μ π' hπ' f =
          t * (∑ χ : D, tr₁ χ f) - ∑ χ : D₂, tr₂ χ.val f := eq_sub_of_add_eq h
      _ = _ := by
        field_simp
        ring
  obtain ⟨j, ⟨e⟩⟩ := hSep F n hn μ J carriers V' reps π' hr hπ' hir hi' hsr hsq' coef hlinear
  cases j with
  | inl χ =>
      refine ⟨χ.comp q, fun x hx => ?_, ⟨e.trans (universeLiftEquiv (T₁ χ)).symm⟩⟩
      change χ (q x) = 1
      rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  | inr χ => exact (χ.property ⟨e.trans (universeLiftEquiv (T₂ χ.val)).symm⟩).elim

end Rigidity

end Langlands.BaseChange
