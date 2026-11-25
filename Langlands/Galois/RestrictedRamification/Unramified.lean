import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Langlands.Global.AdelicFunctoriality.Finite

/-!
# Extensions unramified outside a set of finite places

For a number field `K`, a field `Ω` over `K` and a set `S` of finite places of `K`, an intermediate
field `E` of `Ω / K` is *unramified outside `S`* if every finite place of `K` outside `S` is
unramified in the ring of integers of `E`. The notion is meant for finite `E`, where `𝓞 E` is the
ring of integers of a number field.

This file proves the basic properties: the tower formula for ramification, the criterion by inertia
groups in a finite Galois extension, stability under compositum, under the Galois action and under
passage to a subfield, and the comparison along a finite extension `L / K` with the places of `L`
above `S`. It also transports valuations along the Galois action on places.
-/

namespace Langlands.Galois

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

section Places

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

/-- The finite places of `L` lying above a place of `S`. -/
def finitePlacesAbove (S : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

variable {L}

theorem mem_finitePlacesAbove {S : Set (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ finitePlacesAbove L S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal :=
  Iff.rfl

theorem liesOver_iff_eq_under [NumberField L] {w : HeightOneSpectrum (𝓞 L)}
    {v : HeightOneSpectrum (𝓞 K)} : w.asIdeal.LiesOver v.asIdeal ↔ v = w.under (𝓞 K) :=
  ⟨fun h => HeightOneSpectrum.ext h.over, fun h => h ▸ ⟨rfl⟩⟩

theorem mem_finitePlacesAbove_iff_under [NumberField L] {S : Set (HeightOneSpectrum (𝓞 K))}
    {w : HeightOneSpectrum (𝓞 L)} : w ∈ finitePlacesAbove L S ↔ w.under (𝓞 K) ∈ S := by
  constructor
  · rintro ⟨v, hv, hwv⟩
    rwa [← liesOver_iff_eq_under.1 hwv]
  · intro h
    exact ⟨_, h, ⟨rfl⟩⟩

theorem finitePlacesAbove_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    finitePlacesAbove L S ⊆ finitePlacesAbove L T :=
  fun _ ⟨v, hv, hwv⟩ => ⟨v, h hv, hwv⟩

theorem finite_finitePlacesAbove [NumberField K] [NumberField L] {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) : (finitePlacesAbove L S).Finite := by
  have hfin : ∀ v ∈ S, {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite := by
    intro v _
    have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
    refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
      fun a _ b _ hab => HeightOneSpectrum.ext hab).subset ?_
    intro w hw
    exact ⟨w.isPrime, hw⟩
  refine (hS.biUnion hfin).subset ?_
  rintro w ⟨v, hv, hwv⟩
  exact Set.mem_biUnion hv hwv

theorem mem_finitePlacesAbove_of_natCast_mem {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {w : HeightOneSpectrum (𝓞 L)} [NumberField L] (hw : ((n : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    w ∈ finitePlacesAbove L S := by
  refine mem_finitePlacesAbove_iff_under.2 (hn _ ?_)
  change ((n : ℕ) : 𝓞 K) ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
  rw [Ideal.mem_comap, map_natCast (algebraMap (𝓞 K) (𝓞 L))]
  exact hw

end Places

section Tower

variable {F L M : Type*} [Field F] [Field L] [Field M] [NumberField F] [NumberField L]
  [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]

/-- In a tower `F ⊆ L ⊆ M` of number fields, a prime of `M` is unramified over `F` if and only if
its contraction to `L` is unramified over `F` and it is unramified over `L`. -/
theorem isUnramifiedAt_tower_iff (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) Q ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 L)) ∧ Algebra.IsUnramifiedAt (𝓞 L) Q := by
  rw [← Ideal.ramificationIdx_eq_one_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_tower (q := Q.under (𝓞 L))]
  exact mul_eq_one

end Tower

section Inertia

variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]

theorem restrictScalars_mem_inertia_iff (Q : Ideal (𝓞 M)) (σ : Gal(M/E)) :
    AlgEquiv.restrictScalarsHom F σ ∈ Q.inertia Gal(M/F) ↔ σ ∈ Q.inertia Gal(M/E) :=
  Iff.rfl

theorem mem_range_restrictScalarsHom_iff (σ : Gal(M/F)) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : Gal(M/E) →* Gal(M/F)).range ↔
      ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]

/-- The criterion by inertia: for a finite Galois extension `M / F` of number fields, an
intermediate field `E` and a prime `Q` of `M`, the contraction of `Q` to `E` is unramified over
`F` if and only if the inertia group of `Q` in `Gal(M/F)` fixes `E`. -/
theorem isUnramifiedAt_under_iff_inertia (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have cF : Nat.card (Q.inertia Gal(M/F)) = Q.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 F)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q Gal(M/F)]
  have cE : Nat.card (Q.inertia Gal(M/E)) = Q.ramificationIdx (𝓞 E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 E)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 E)) Q Gal(M/E)]
  have htow : Q.ramificationIdx (𝓞 F) =
      (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (q := Q.under (𝓞 E)) (r := Q)
  set φ : Gal(M/E) →* Gal(M/F) := AlgEquiv.restrictScalarsHom F with hφ
  have hinj : Function.Injective φ := AlgEquiv.restrictScalarsHom_injective F
  have hmap : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) ⊓ φ.range := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(restrictScalars_mem_inertia_iff Q τ).2 hτ, τ, rfl⟩
    · rintro ⟨hσ, τ, rfl⟩
      exact ⟨τ, (restrictScalars_mem_inertia_iff Q τ).1 hσ, rfl⟩
  have hcardmap : Nat.card ((Q.inertia Gal(M/E)).map φ) = Nat.card (Q.inertia Gal(M/E)) :=
    Subgroup.card_map_of_injective hinj
  have hpos : 0 < Nat.card (Q.inertia Gal(M/E)) := Nat.card_pos
  rw [← Ideal.ramificationIdx_eq_one_iff]
  constructor
  · intro h1 σ hσ
    have hc : Nat.card (Q.inertia Gal(M/F) ⊓ φ.range : Subgroup Gal(M/F)) ≥
        Nat.card (Q.inertia Gal(M/F)) := by
      rw [← hmap, hcardmap, cF, cE, htow, h1, one_mul]
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q.inertia Gal(M/F) ⊓ φ.range ≤ _) hc
    have hσ' : σ ∈ Q.inertia Gal(M/F) ⊓ φ.range := by rw [heq]; exact hσ
    exact (mem_range_restrictScalarsHom_iff σ).1 hσ'.2
  · intro h
    have hle : Q.inertia Gal(M/F) ≤ φ.range := fun σ hσ =>
      (mem_range_restrictScalarsHom_iff σ).2 (h σ hσ)
    have hmap' : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) := by
      rw [hmap, inf_eq_left.2 hle]
    have hc : (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) =
        1 * Q.ramificationIdx (𝓞 E) := by
      rw [← htow, ← cF, ← cE, ← hmap', hcardmap, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (cE ▸ hpos) hc

end Inertia

section Ramified

/-! ### Finitely many places ramify -/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A ramified prime of `L` divides the different ideal of `L / K`. -/
theorem dvd_differentIdeal_of_ramificationIdx_ne_one {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have h2 : 2 ≤ w.asIdeal.ramificationIdx (𝓞 K) := by
    have := Ideal.ramificationIdx_pos (q := w.asIdeal) (R := 𝓞 K)
    omega
  set v := w.asIdeal.under (𝓞 K)
  have hv0 : v ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot w.ne_bot
  have : v.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hv0
  have hmap : v.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hv0
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v w.asIdeal hmap
  have hdvd : w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣
      v.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [he]
    exact pow_multiplicity_dvd _ _
  have := pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal (by omega) hv0 hdvd
  exact (dvd_pow_self _ (by omega)).trans this

variable (K L) in
/-- Only finitely many primes of `L` are ramified over `K`. -/
theorem finite_setOf_ramificationIdx_ne_one :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
  (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))).subset
    fun _ hw => dvd_differentIdeal_of_ramificationIdx_ne_one hw

/-- Only finitely many finite places of `K` divide a nonzero natural number. -/
theorem finite_setOf_natCast_mem {N : ℕ} (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((N : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  change v.asIdeal ∣ Ideal.span {((N : ℕ) : 𝓞 K)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end Ramified

section IntermediateFields

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- An intermediate field `E` of `Ω / F` is unramified outside `S` if every finite place of `F`
outside `S` is unramified in `𝓞 E`. The notion is meant for `E` finite over `F`. -/
def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal

theorem IsUnramifiedOutside.ramificationIdx_eq_one {S : Set (HeightOneSpectrum (𝓞 F))}
    {E : IntermediateField F Ω} [FiniteDimensional F E] (hE : IsUnramifiedOutside S E)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have := NumberField.of_module_finite F E
  exact Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hE v hv) inferInstance

theorem isUnramifiedOutside_of_ramificationIdx_eq_one {S : Set (HeightOneSpectrum (𝓞 F))}
    {E : IntermediateField F Ω} [FiniteDimensional F E]
    (h : ∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    IsUnramifiedOutside S E := by
  have := NumberField.of_module_finite F E
  intro v hv
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hP
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  exact h v hv ⟨P, inferInstance, hP0⟩ hP

omit [NumberField F] in
theorem finiteDimensional_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M] :
    FiniteDimensional F E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

theorem isUnramifiedIn_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F)) (hM : Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  intro P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := E) Q).1 (hM Q hQ this)).1
  have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
  subst e
  exact hu

theorem IsUnramifiedOutside.of_le {S : Set (HeightOneSpectrum (𝓞 F))}
    {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M]
    (hM : IsUnramifiedOutside S M) : IsUnramifiedOutside S E :=
  fun v hv => isUnramifiedIn_of_le h v (hM v hv)

omit [NumberField F] in
theorem IsUnramifiedOutside.mono {S T : Set (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T)
    {E : IntermediateField F Ω} (hE : IsUnramifiedOutside S E) : IsUnramifiedOutside T E :=
  fun v hv => hE v fun hs => hv (h hs)

theorem isUnramifiedIn_iff_inertia {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        ∀ σ ∈ Q.inertia Gal(M/F), ∀ x (hx : x ∈ E), σ ⟨x, h hx⟩ = ⟨x, h hx⟩ := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  constructor
  · intro hE Q hQ hQv σ hσ x hx
    have : (Q.under (𝓞 E)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact hQv.over⟩
    have hu := hE (Q.under (𝓞 E)) inferInstance this
    exact (isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩
  · intro hI P hP hPv
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hu := (isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2
      (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)
    have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
    subst e
    exact hu

omit [NumberField F] in
theorem mem_map_fixedField_iff {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩

theorem isUnramifiedIn_iff_le_fixedField {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by
  rw [isUnramifiedIn_iff_inertia h]
  refine forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro hI x hx
    exact (mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩
  · intro hle σ hσ x hx
    obtain ⟨_, hfix⟩ := (mem_map_fixedField_iff _ x).1 (hle hx)
    exact hfix σ hσ

variable [IsGalois F Ω]

omit [NumberField F] in
/-- A finite subextension of a Galois extension lies in a finite Galois subextension. -/
theorem exists_finiteGaloisIntermediateField_le (E : IntermediateField F Ω)
    [FiniteDimensional F E] :
    ∃ M : FiniteGaloisIntermediateField F Ω, E ≤ M.toIntermediateField :=
  ⟨{ toIntermediateField := IntermediateField.normalClosure F E Ω
     finiteDimensional := normalClosure.is_finiteDimensional F E Ω
     isGalois := IsGalois.normalClosure F E Ω }, IntermediateField.le_normalClosure E⟩

theorem isUnramifiedIn_sup {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGaloisIntermediateField_le (E₁ ⊔ E₂)
  rw [isUnramifiedIn_iff_le_fixedField hM]
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)] at h₁
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)] at h₂
  exact fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)

theorem IsUnramifiedOutside.sup {S : Set (HeightOneSpectrum (𝓞 F))} {E₁ E₂ : IntermediateField F Ω}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂] (h₁ : IsUnramifiedOutside S E₁)
    (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂) :=
  fun v hv => isUnramifiedIn_sup v (h₁ v hv) (h₂ v hv)

theorem isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⊥ : IntermediateField F Ω)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGaloisIntermediateField_le (⊥ : IntermediateField F Ω)
  rw [isUnramifiedIn_iff_inertia hM]
  intro Q _ _ σ _ x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes a

theorem isUnramifiedOutside_bot (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) :=
  fun v _ => isUnramifiedIn_bot v

theorem isUnramifiedIn_map {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGaloisIntermediateField_le E
  set M' : IntermediateField F Ω := M.toIntermediateField with hM'
  set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ
  have hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y := fun y hy =>
    AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩
  have hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have := (ρ ⟨y, hM hy⟩).2
    rwa [hρapp] at this
  rw [isUnramifiedIn_iff_inertia hM] at hE
  rw [isUnramifiedIn_iff_inertia hτM]
  intro Q hQ hQv σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  have hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro z
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact (AddSubgroup.mem_inertia.1 hσ) (ρ • z)
  have := NumberField.of_module_finite F M'
  have hfix := hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy
  have hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩ := Subtype.ext (hρapp y (hM hy))
  rw [← hρy]
  calc σ (ρ ⟨y, hM hy⟩) = ρ ((ρ⁻¹ * σ * ρ) ⟨y, hM hy⟩) := by
        simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ρ ⟨y, hM hy⟩ := by rw [hfix]

theorem IsUnramifiedOutside.map {S : Set (HeightOneSpectrum (𝓞 F))} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : IsUnramifiedOutside S E) (τ : Gal(Ω/F)) :
    IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω)) :=
  fun v hv => isUnramifiedIn_map v (hE v hv) τ

end IntermediateFields

section RestrictScalars

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]

/-- For a finite extension `L / F` in which the places outside `S` are unramified, a finite
extension `M` of `L` inside `Ω` is unramified outside `S` over `F` if and only if it is unramified
over `L` outside the places of `L` above `S`. -/
theorem isUnramifiedOutside_restrictScalars_iff (S : Set (HeightOneSpectrum (𝓞 F)))
    (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) (M : IntermediateField L Ω)
    [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔
      IsUnramifiedOutside (finitePlacesAbove L S) M := by
  have : FiniteDimensional F M := FiniteDimensional.trans F L M
  have := NumberField.of_module_finite L M
  change (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) ↔ _
  constructor
  · intro hM w hw Q hQ hQw
    have hv0 : w.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) w.ne_bot
    let v : HeightOneSpectrum (𝓞 F) := ⟨w.asIdeal.under (𝓞 F), inferInstance, hv0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hv : v ∉ S := fun hvS => hw ⟨v, hvS, hwv⟩
    have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal
    exact ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hM v hv Q hQ this)).2
  · intro hM v hv Q hQ hQv
    have hP0 : Q.under (𝓞 L) ≠ ⊥ := by
      have : (Q.under (𝓞 L)).LiesOver v.asIdeal :=
        ⟨by rw [Ideal.under_under]; exact hQv.over⟩
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (Q.under (𝓞 L))
    let w : HeightOneSpectrum (𝓞 L) := ⟨Q.under (𝓞 L), inferInstance, hP0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by
      change v.asIdeal = (Q.under (𝓞 L)).under (𝓞 F)
      rw [Ideal.under_under]; exact hQv.over⟩
    have hw : w ∉ finitePlacesAbove L S := by
      rintro ⟨u, huS, hwu⟩
      have huv : u = v := HeightOneSpectrum.ext (hwu.over.trans hwv.over.symm)
      exact hv (huv ▸ huS)
    have h1 := hM w hw Q hQ ⟨rfl⟩
    have h2 := hL v hv (Q.under (𝓞 L)) inferInstance hwv
    exact (isUnramifiedAt_tower_iff (F := F) (L := L) Q).2 ⟨h2, h1⟩

end RestrictScalars

section Valuation

/-! ### Valuations along the Galois action on places -/

theorem eq_of_forall_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
      (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) → b ≤ WithZero.exp (-(n : ℤ))) → b ≤ a := by
    intro a b ha0 ha1 h
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log ha0, WithZero.exp_zero]
      exact ha1
    have hn : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
    have := h (-WithZero.log a).toNat (by rw [hn, neg_neg, WithZero.exp_log ha0])
    rwa [hn, neg_neg, WithZero.exp_log ha0] at this
  exact le_antisymm (key hb0 hb1 fun n => (h n).2) (key ha0 ha1 fun n => (h n).1)

section Conjugate

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

/-- The image of a height one prime under a ring automorphism given by a group action. -/
def smulPlace (σ : G) (w : HeightOneSpectrum B) : HeightOneSpectrum B where
  asIdeal := σ • w.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  ne_bot := by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact Ideal.map_bot

omit [IsDedekindDomain B] in
theorem smulPlace_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl

theorem intValuation_smulPlace (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, map_zero, map_zero]
  have hσr : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  refine eq_of_forall_le_exp_iff (intValuation_ne_zero _ _ hσr) (intValuation_ne_zero _ _ hr)
    (intValuation_le_one _ _) (intValuation_le_one _ _) fun n => ?_
  rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smulPlace_asIdeal, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul_iff

end Conjugate

section NumberField

variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]

theorem valuation_smulPlace (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have ha : σ (algebraMap (𝓞 M) M a) = algebraMap (𝓞 M) M (σ • a) := rfl
  have hb' : σ (algebraMap (𝓞 M) M b) = algebraMap (𝓞 M) M (σ • b) := rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smulPlace,
    intValuation_smulPlace]

theorem valuation_smulPlace_apply (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M x = w.valuation M (σ⁻¹ x) := by
  rw [← valuation_smulPlace σ w (σ⁻¹ x)]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ x).symm

end NumberField

section Unramified

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem valuation_algebraMap_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by
  rw [← valuation_liesOver L w W x, Ideal.ramificationIdx_eq_one, pow_one]

end Unramified

end Valuation

end Langlands.Galois

namespace Langlands.Galois

open NumberField IsDedekindDomain Langlands.Global.AdelicFunctoriality

universe u

section Places

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `Gal(L/K)` permutes the finite places of `L`: `σ • w` is the place with valuation
`x ↦ w(σ⁻¹ x)`. -/
instance finitePlaceAction : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := finitePlaceEquiv (σ⁻¹ : L ≃ₐ[K] L).toRingEquiv w
  one_smul _ := HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)
  mul_smul _ _ _ := HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

omit [NumberField K] [NumberField L] in
theorem smul_finitePlace_def (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ • w = finitePlaceEquiv (σ⁻¹ : L ≃ₐ[K] L).toRingEquiv w :=
  rfl

omit [NumberField K] in
/-- The valuation of `σ • w` at `σ x` is the valuation of `w` at `x`. -/
theorem valuation_smul_finitePlace (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (σ • w).valuation L (σ x) = w.valuation L x := by
  rw [smul_finitePlace_def, finitePlaceEquiv_valuation]
  congr 1
  exact σ.symm_apply_apply x

omit [NumberField K] [NumberField L] in
theorem under_smul_finitePlace (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  ext a
  change RingOfIntegers.mapRingEquiv (σ⁻¹ : L ≃ₐ[K] L).toRingEquiv (algebraMap (𝓞 K) (𝓞 L) a) ∈
    w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal
  have : RingOfIntegers.mapRingEquiv (σ⁻¹ : L ≃ₐ[K] L).toRingEquiv (algebraMap (𝓞 K) (𝓞 L) a) =
      algebraMap (𝓞 K) (𝓞 L) a := by
    apply RingOfIntegers.ext
    change (σ⁻¹ : L ≃ₐ[K] L) (algebraMap K L a) = algebraMap K L a
    exact AlgEquiv.commutes _ _
  rw [this]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `Gal(L/K)` permutes the places of `L` above `S`. -/
instance finitePlacesAboveAction : MulAction (L ≃ₐ[K] L) (finitePlacesAbove L S) where
  smul σ w := ⟨σ • w.1, by
    rw [mem_finitePlacesAbove_iff_under, under_smul_finitePlace]
    exact mem_finitePlacesAbove_iff_under.1 w.2⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ w.1)

omit [NumberField K] in
theorem coe_smul_finitePlacesAbove (σ : L ≃ₐ[K] L) (w : finitePlacesAbove L S) :
    ((σ • w : finitePlacesAbove L S) : HeightOneSpectrum (𝓞 L)) = σ • (w : HeightOneSpectrum (𝓞 L)) :=
  rfl

end Places

end Langlands.Galois
