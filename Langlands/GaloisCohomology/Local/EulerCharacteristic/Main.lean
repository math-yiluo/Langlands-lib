import Langlands.GaloisCohomology.Local.EulerCharacteristic.GroupStructure
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Vanishing
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Coprime
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Coinduced
import Langlands.GaloisCohomology.Local.Dimension

/-!
# The local Euler characteristic formula

For a nonarchimedean local field `K` with separable closure `Ksep` (`K Ksep : Type u`) and a finite
smooth `Gal(Ksep/K)`-module `M` of order invertible in `K`,
`χ(M) = |H⁰(M)| · |H²(M)| / |H¹(M)| = |𝒪[K] / |M|·𝒪[K]|⁻¹`
(`eulerCharacteristic_eq_of_card`, here `eulerChar_galois`).

By dévissage it suffices to treat simple modules; such a module is `l`-torsion for a prime `l`.
For `l` equal to the residue characteristic `p`, the wild inertia group `G₁` of a finite Galois
extension `L/K` trivializing `M` and `μ_p` acts trivially on `M` (a `p`-group acting on a simple
`𝔽_p`-module), and the formula follows from the coprime case (`Coprime.lean`) for the subgroup of
`Gal(L/K)` above the prime-to-`p` part of `G/G₁`, and from the behaviour of `χ` under restriction to
a subgroup of `p`-power index with cyclic quotient. For `l ≠ p`, the formula reads `χ(M) = 1`;
either the tame inertia acts nontrivially and all cohomology vanishes (`Vanishing.lean`), or the
coprime case applies to the subgroup above the `l`-primary part of `G/G₀`.

The fixed fields are local fields for the valuative relation of the spectral norm on `Ksep`
(`Arithmetic/SeparableClosure.lean`).
-/

noncomputable section

open Langlands.GaloisCohomology.Local.IntermediateFieldStructure

namespace Langlands.GaloisCohomology.Local

universe u

-- from MainGalois.lean
section MainGalois
open IntermediateField ValuativeRel Langlands.ProfiniteCohomology

section Preimage

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsGalois K Ksep]
  (V : OpenNormalSubgroup Gal(Ksep/K))

noncomputable abbrev restrictFixed : Gal(Ksep/K) →* Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) :=
  AlgEquiv.restrictNormalHom (fixedField (V : Subgroup Gal(Ksep/K)))

theorem restrictFixed_surjective : Function.Surjective (restrictFixed V) :=
  AlgEquiv.restrictNormalHom_surjective Ksep

theorem restrictFixed_apply (σ : Gal(Ksep/K)) (x : fixedField (V : Subgroup Gal(Ksep/K))) :
    ((restrictFixed V σ x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x

theorem ker_restrictFixed : (restrictFixed V).ker = (V : Subgroup Gal(Ksep/K)) := by
  rw [restrictFixed, IntermediateField.restrictNormalHom_ker,
    fixingSubgroup_fixedField_openNormalSubgroup]

theorem mem_V_iff_restrictFixed_eq_one (σ : Gal(Ksep/K)) :
    σ ∈ (V : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ = 1 := by
  rw [← MonoidHom.mem_ker]
  exact (SetLike.ext_iff.1 (ker_restrictFixed V) σ).symm

noncomputable def preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    OpenSubgroup Gal(Ksep/K) where
  toSubgroup := S.comap (restrictFixed V)
  isOpen' := Subgroup.isOpen_mono (H₁ := (V : Subgroup Gal(Ksep/K))) (fun σ hσ => by
      change restrictFixed V σ ∈ S
      rw [(mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
      exact S.one_mem) V.isOpen'

variable {V}

@[simp]
theorem mem_preimageOpen {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)} {σ : Gal(Ksep/K)} :
    σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ ∈ S :=
  Iff.rfl

theorem coe_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (preimageOpen V S : Subgroup Gal(Ksep/K)) = S.comap (restrictFixed V) :=
  rfl

theorem le_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)) ≤ preimageOpen V S := fun σ hσ => by
  rw [mem_preimageOpen, (mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
  exact S.one_mem

theorem preimageOpen_le_preimageOpen {S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (h : S ≤ S') : preimageOpen V S ≤ preimageOpen V S' := fun _ hσ => h hσ

instance preimageOpen_normal (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) [S.Normal] :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem preimageOpen_bot :
    ((preimageOpen V ⊥ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = V := by
  ext σ
  rw [coe_preimageOpen, Subgroup.mem_comap, Subgroup.mem_bot, mem_V_iff_restrictFixed_eq_one]

theorem relIndex_preimageOpen (S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).relIndex
      (preimageOpen V S') = S.relIndex S' := by
  rw [coe_preimageOpen, coe_preimageOpen, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (restrictFixed_surjective V)]

theorem relIndex_V_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)).relIndex (preimageOpen V S) = Nat.card S := by
  have h := relIndex_preimageOpen (V := V) ⊥ S
  rw [preimageOpen_bot, Subgroup.relIndex_bot_left] at h
  exact h

theorem index_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).index = S.index := by
  rw [coe_preimageOpen]
  exact Subgroup.index_comap_of_surjective S (restrictFixed_surjective V)

noncomputable def quotientPreimageOpenEquiv (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) ≃*
      Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S :=
  (QuotientGroup.quotientMulEquivOfEq (by
      ext σ
      rw [coe_preimageOpen, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' S).comp (restrictFixed V))
      ((QuotientGroup.mk'_surjective S).comp (restrictFixed_surjective V)))

theorem isCyclic_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] [IsCyclic (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S)] :
    IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
  isCyclic_of_surjective (quotientPreimageOpenEquiv S).symm.toMonoidHom
    (quotientPreimageOpenEquiv S).symm.surjective

theorem card_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) =
      Nat.card (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S) :=
  Nat.card_congr (quotientPreimageOpenEquiv S).toEquiv

theorem pow_eq_one_mem_fixedField_preimageOpen {n : ℕ}
    (hV : ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ n = 1 → σ ζ = ζ)
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : ∀ ζ : fixedField (V : Subgroup Gal(Ksep/K)), ζ ^ n = 1 → ζ ∈ IntermediateField.fixedField S)
    {ζ : Ksep} (hζ : ζ ^ n = 1) :
    ζ ∈ fixedField ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) := by
  have hζV : ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) :=
    (mem_fixedField_iff _ _).2 fun σ hσ => hV σ hσ ζ hζ
  set ζ' : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hζV⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext (by simp [ζ', hζ])
  have h := (mem_fixedField_iff _ _).1 (hS ζ' hζ')
  refine (mem_fixedField_iff _ _).2 fun σ hσ => ?_
  have := congrArg (fun y : fixedField (V : Subgroup Gal(Ksep/K)) => (y : Ksep)) (h _ hσ)
  simpa [ζ', restrictFixed_apply] using this

end Preimage

section Inertia

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [TopologicalSpace Ksep]
  [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]
  {V : OpenNormalSubgroup Gal(Ksep/K)}

theorem valuation_sub_lt_one_of_mem_preimageOpen
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : S ≤ lowerRamificationGroup K (fixedField (V : Subgroup Gal(Ksep/K))) 0)
    {σ : Gal(Ksep/K)} (hσ : σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)))
    {x : Ksep} (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K))) (hx1 : valuation Ksep x ≤ 1) :
    valuation Ksep (σ x - x) < 1 := by
  have hx'1 : valuation (fixedField (V : Subgroup Gal(Ksep/K))) ⟨x, hx⟩ ≤ 1 :=
    (valuation_le_one_iff_coe _ ⟨x, hx⟩).2 hx1
  have h := mem_lowerRamificationGroup_iff.mp (hS hσ) ⟨⟨x, hx⟩, hx'1⟩
  simp only [zero_add, pow_one] at h
  have h2 := mem_maximalIdeal_integer_iff.1 h
  have h3 := (valuation_lt_one_iff_coe _ _).1 h2
  simpa [restrictFixed_apply, coe_integerAlgEquiv_apply] using h3

end Inertia

end MainGalois

-- from MainCount.lean
section MainCount
open ValuativeRel Langlands.ProfiniteCohomology

section Integers

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem card_quotient_span_eq_one_of_isUnit {a : 𝒪[K]} (ha : IsUnit a) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a}) = 1 := by
  rw [Ideal.span_singleton_eq_top.2 ha]
  have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_unique

theorem card_quotient_span_mul {a b : 𝒪[K]} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a * b}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {a}) * Nat.card (𝒪[K] ⧸ Ideal.span {b}) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hπ
  have key : ∀ (v : 𝒪[K]ˣ) (n : ℕ), Ideal.span {(v : 𝒪[K]) * π ^ n} = Ideal.span {π ^ n} :=
    fun v n => Ideal.span_singleton_mul_left_unit v.isUnit _
  have hab : (u : 𝒪[K]) * π ^ i * ((w : 𝒪[K]) * π ^ j) =
      ((u * w : 𝒪[K]ˣ) : 𝒪[K]) * π ^ (i + j) := by
    push_cast
    ring
  rw [hab, key, key, key, card_quotient_span_pow hπ, card_quotient_span_pow hπ,
    card_quotient_span_pow hπ, pow_add]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem natCast_integer_ne_zero {m : ℕ} (hm : (m : K) ≠ 0) : (m : 𝒪[K]) ≠ 0 := by
  intro h
  apply hm
  have := congrArg (fun x : 𝒪[K] => (x : K)) h
  simpa using this

theorem card_quotient_span_natCast_mul {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m * n : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) * Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) := by
  rw [Nat.cast_mul]
  exact card_quotient_span_mul (natCast_integer_ne_zero hm) (natCast_integer_ne_zero hn)

theorem card_quotient_span_natCast_pow {m : ℕ} (hm : (m : K) ≠ 0) (d : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m ^ d : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ d := by
  induction d with
  | zero =>
    rw [pow_zero, pow_zero, Nat.cast_one]
    exact card_quotient_span_eq_one_of_isUnit isUnit_one
  | succ d ih =>
    have hmd : ((m ^ d : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ hm
    rw [pow_succ, card_quotient_span_natCast_mul hmd hm, ih, pow_succ]

theorem card_quotient_span_natCast_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) = 1 := by
  apply card_quotient_span_eq_one_of_isUnit
  by_contra h
  apply hm
  rw [← map_natCast (IsLocalRing.residue 𝒪[K]), IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 h

end Integers

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_quotient_span_natCast_finiteExtension (m : ℕ) :
    Nat.card (𝒪[L] ⧸ Ideal.span {(m : 𝒪[L])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ Module.finrank K L := by
  classical
  let ι := Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]
  let b : Module.Basis ι 𝒪[K] 𝒪[L] := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  let I : Ideal 𝒪[K] := Ideal.span {(m : 𝒪[K])}
  let ψ : 𝒪[L] →ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap)
  have hψ : ∀ x i, ψ x i = Submodule.Quotient.mk (b.equivFun x i) := fun _ _ => rfl
  have hsmul : ∀ y : 𝒪[L], (m : 𝒪[K]) • y = (m : 𝒪[L]) * y := fun y => by
    rw [Algebra.smul_def, map_natCast]
  have hsurj : Function.Surjective ψ := by
    intro v
    refine ⟨b.equivFun.symm fun i => Quotient.out (v i), ?_⟩
    funext i
    rw [hψ, LinearEquiv.apply_symm_apply]
    exact Quotient.out_eq (v i)
  have hker : LinearMap.ker ψ = (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K] := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have hc : ∀ i, ∃ c : 𝒪[K], c * (m : 𝒪[K]) = b.equivFun x i := fun i => by
        have := congrFun hx i
        rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose c hc using hc
      refine ⟨b.equivFun.symm c, ?_⟩
      rw [mul_comm, ← hsmul]
      apply b.equivFun.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hc i, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, mul_comm, ← hsmul, map_smul,
        Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e1 : (𝒪[L] ⧸ (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K]) ≃ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  have e2 := Submodule.Quotient.restrictScalarsEquiv 𝒪[K] (Ideal.span {(m : 𝒪[L])})
  rw [← Nat.card_congr e2.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_fun,
    ← Module.finrank_eq_nat_card_basis b, finrank_integer]

end Extension

section Groups

theorem exists_card_eq_prime_pow_of_nsmul {A : Type*} [AddCommGroup A] [Finite A] {l : ℕ}
    [Fact l.Prime] (h : ∀ a : A, l • a = 0) : ∃ d, Nat.card A = l ^ d := by
  have hP : IsPGroup l (Multiplicative A) := fun x => ⟨1, by
    rw [pow_one]
    exact congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd x))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  exact ⟨n, hn⟩

theorem exists_ne_zero_forall_mem_eq {k G : Type*} [CommRing k] [Group G] {l : ℕ} [Fact l.Prime]
    (M : Rep k G) [Finite M] [Nontrivial M] (hl : ∀ m : M, l • m = 0) (W T : Subgroup G)
    (hT : ∀ g ∈ T, ∀ m : M, M.ρ g m = m) (hW : ∀ g ∈ W, ∃ n : ℕ, g ^ l ^ n ∈ T) :
    ∃ m : M, m ≠ 0 ∧ ∀ g ∈ W, M.ρ g m = m := by
  let H := W.map (Representation.asGroupHom M.ρ)
  have hH : IsPGroup l H := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨n, hn⟩ := hW g hg
    refine ⟨n, Subtype.ext (Units.ext (LinearMap.ext fun a => ?_))⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    rw [← map_pow, Representation.asGroupHom_apply, hT _ hn]
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := (Finite.one_lt_card_iff_nontrivial (α := M)).2 inferInstance
    rw [hd, pow_zero] at h1
    exact lt_irrefl _ h1
  have hcard : l ∣ Nat.card M := hd ▸ dvd_pow_self l hd0
  have h0 : (0 : M) ∈ MulAction.fixedPoints H M := fun h => by
    show (h : (M →ₗ[k] M)ˣ) • (0 : M) = 0
    exact smul_zero _
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hcard h0
  exact ⟨b, hb0.symm, fun g hg => hb ⟨_, g, hg, rfl⟩⟩

end Groups

end MainCount

-- from MainSimple.lean
section MainSimple
open CategoryTheory IntermediateField ValuativeRel Langlands.ProfiniteCohomology

section Fixed

variable {k G : Type*} [CommRing k] [Group G]

def fixedSubmodule (M : Rep k G) (W : Subgroup G) : Submodule k M where
  carrier := {m | ∀ g ∈ W, M.ρ g m = m}
  add_mem' {a b} ha hb g hg := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c m hm g hg := by
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [map_smul, hm g hg]

theorem fixedSubmodule_le_comap (M : Rep k G) (W : Subgroup G) [hW : W.Normal] (g : G) :
    fixedSubmodule M W ≤ (fixedSubmodule M W).comap (M.ρ g) := by
  intro m hm w hw
  have h := hm (g⁻¹ * w * g) (by simpa using hW.conj_mem w hw g⁻¹)
  have e : w * g = g * (g⁻¹ * w * g) := by group
  change M.ρ w (M.ρ g m) = M.ρ g m
  calc M.ρ w (M.ρ g m) = M.ρ (w * g) m := by rw [map_mul]; rfl
    _ = M.ρ (g * (g⁻¹ * w * g)) m := by rw [e]
    _ = M.ρ g (M.ρ (g⁻¹ * w * g) m) := by rw [map_mul]; rfl
    _ = M.ρ g m := by rw [h]

end Fixed

section Simple

attribute [-instance] ULift.module

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerCharacteristic_of_forall_eq_bot_or_eq_top (M : Rep (ULift.{u} ℤ) Gal(Ksep/K)) [IsSmoothRep M]
    [Finite M] [Nontrivial M] (hM : (Nat.card M : K) ≠ 0)
    (hsimple : ∀ N : Submodule (ULift.{u} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤) :
    eulerCharacteristic M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by

  obtain ⟨l, hlp, hldvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
  have := Fact.mk hlp
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hlK : (l : K) ≠ 0 := by
    obtain ⟨c, hc⟩ := hldvd
    intro h
    apply hM
    rw [hc, Nat.cast_mul, h, zero_mul]
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  have hPmul : ∀ m n : ℕ, (m : K) ≠ 0 → (n : K) ≠ 0 → ((m * n : ℕ) : K) ≠ 0 := by
    intro m n hm hn
    rw [Nat.cast_mul]
    exact mul_ne_zero hm hn

  have hMl : ∀ m : M, l • m = 0 := by
    let N : Submodule (ULift.{u} ℤ) M := LinearMap.ker (l • LinearMap.id)
    have hN : ∀ g, N ≤ N.comap (M.ρ g) := fun g m hm => by
      simp only [N, LinearMap.mem_ker, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply] at hm ⊢
      rw [← map_nsmul, hm, map_zero]
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hldvd
    have hxN : x ∈ N := by
      simp only [N, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hx
      exact hlp.one_lt.ne hx
    rcases hsimple N hN with h | h
    · rw [h] at hxN
      exact absurd ((Submodule.mem_bot _).1 hxN) hx0
    · intro m
      have : m ∈ N := h ▸ Submodule.mem_top
      simpa [N] using this
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hMl
  have hG := hasFiniteCohomology K Ksep

  let := algebraicValuativeRel K Ksep
  let := algebraicTopology K Ksep
  have := algebraicTopology_isValuativeTopology K Ksep
  have := algebraicValuativeRel_valuativeExtension K Ksep

  obtain ⟨V, hVM, hVμ⟩ : ∃ V : OpenNormalSubgroup Gal(Ksep/K),
      (∀ g ∈ (V : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m) ∧
        ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ l = 1 → σ ζ = ζ := by
    have hdisc := (isSmoothRep_iff_forall_exists_openNormalSubgroup M).1 inferInstance
    choose U hU using hdisc
    obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite
      (fun o : Option M => o.elim (rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) l) U)
    refine ⟨V, fun g hg m => ?_, fun σ hσ ζ hζ => ?_⟩
    · exact (Representation.mem_invariants _ _).1 (hU m) ⟨g, hV (some m) hg⟩
    · exact apply_eq_of_mem_rootsOfUnityFixing (hV none hσ) hζ
  have hμV : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) := fun ζ hζ =>
    (mem_fixedField_iff _ _).2 fun σ hσ => hVμ σ hσ ζ hζ
  set L : IntermediateField K Ksep := fixedField (V : Subgroup Gal(Ksep/K)) with hL
  by_cases hlq : l = ringChar 𝓀[K]
  ·
    have hlE : ∀ E : IntermediateField K Ksep, (l : E) ≠ 0 := fun E h =>
      hlK ((algebraMap K E).injective (by rw [map_natCast, map_zero]; exact h))

    obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
      (preimageOpen V (lowerRamificationGroup K L 1)) (V : Subgroup Gal(Ksep/K)) hVM (fun g hg => by
        obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨restrictFixed V g, hg⟩
        refine ⟨n, ?_⟩
        rw [mem_V_iff_restrictFixed_eq_one, map_pow, hlq]
        exact congrArg Subtype.val hn)
    have h1fix : ∀ g ∈ (preimageOpen V (lowerRamificationGroup K L 1) : Subgroup Gal(Ksep/K)),
        ∀ m : M, M.ρ g m = m := by
      have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
        have : m0 ∈ fixedSubmodule M (preimageOpen V (lowerRamificationGroup K L 1)) := hm0fix
        rw [h] at this
        exact (Submodule.mem_bot _).1 this))
      intro g hg m
      have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
      exact this g hg

    obtain ⟨nE, hnE⟩ := exists_card_quotient_eq_pow (E := fixedField (preimageOpen V
      (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : Subgroup Gal(Ksep/K)))
      (p := l) (hlE _)
    have hX := eulerCharacteristic_coprime
      (U := preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))
      (V := preimageOpen V (lowerRamificationGroup K L 1)) hlK
      (preimageOpen_le_preimageOpen (lowerRamificationGroup_one_le_coprimeQuotientPreimage (K := K) (L := L)))
      (by
        rw [relIndex_preimageOpen, hlq]
        exact coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one (K := K) (L := L))
      (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
        (fun ζ' hζ' => pow_eq_one_mem_fixedField_lowerRamificationGroup_one (K := K) (L := L)
          (by rw [← hlq]; exact hζ')) hζ)
      (Rep.res ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0)
        (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
      (fun g hg m => h1fix g hg m) hnE

    have : IsCyclic (Gal(L/K) ⧸ coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
      isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup (K := K) (L := L)
    have : IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
      isCyclic_quotient_preimageOpen _
    obtain ⟨a, ha⟩ := exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow
      (K := K) (L := L)
    have hcard : Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [card_quotient_preimageOpen, ha, hlq]
    have hC := eulerCharacteristic_res_eq_pow (P := fun m => (m : K) ≠ 0) hPdvd hPmul hG _ hcard M hM hMl

    have hfin : Module.finrank K (fixedField ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [← index_openSubgroup, Subgroup.index, hcard]
    obtain ⟨nK, hnK⟩ := exists_card_quotient_eq_pow (E := K) (p := l) hlK
    have hext := card_quotient_span_natCast_finiteExtension (K := K) (L := fixedField
      ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :
        OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) l
    rw [hnE, hnK, hfin, ← pow_mul] at hext
    have hnE' : nE = nK * l ^ a := Nat.pow_right_injective hlp.two_le hext

    have hpos := eulerCharacteristic_pos hG M hM
    have key : eulerCharacteristic M ^ (l ^ a) = (((Nat.card M : ℚ) ^ nK)⁻¹) ^ (l ^ a) := by
      rw [← hC, hX, hnE', pow_mul, inv_pow]
    have hχ := (pow_left_inj₀ hpos.le (by positivity) (pow_ne_zero a hlp.ne_zero)).1 key
    rw [hχ, hd, card_quotient_span_natCast_pow hlK, hnK]
    push_cast
    ring
  ·
    have hl𝓀 : (l : 𝓀[K]) ≠ 0 := by
      rw [Ne, ringChar.spec]
      intro h
      exact hlq ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hlp).1 h).symm
    have hRHS : Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) = 1 :=
      card_quotient_span_natCast_eq_one (by rw [hd, Nat.cast_pow]; exact pow_ne_zero _ hl𝓀)
    rw [hRHS, Nat.cast_one, inv_one]
    have hBle : coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l ≤
        lowerRamificationGroup K L 0 :=
      coprimeRelPreimage_le _ _ l
    by_cases hB : fixedSubmodule M (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
        (lowerRamificationGroup K L 1) l)) = ⊥
    ·
      have hsub : ∀ i ≤ 2, Subsingleton (cohomology M i) := fun i hi =>
        subsingleton_cohomology_of_inertia hlp hl𝓀 (V := V.toOpenSubgroup) (le_preimageOpen _) hμV
          (fun g hg x hx hx1 => valuation_sub_lt_one_of_mem_preimageOpen hBle hg hx hx1)
          (by
            rw [relIndex_V_preimageOpen]
            exact coprime_card_coprimeRelPreimage_lowerRamificationGroup (K := K) (L := L) hlp hlq)
          M hMl hVM (fun m hm => by
            have : m ∈ fixedSubmodule M (preimageOpen V (coprimeRelPreimage
                (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l)) := hm
            rw [hB] at this
            exact (Submodule.mem_bot _).1 this) hi
      have h0 := hsub 0 (by norm_num)
      have h1 := hsub 1 (by norm_num)
      have h2 := hsub 2 le_rfl
      rw [eulerCharacteristic_eq, Nat.card_of_subsingleton (0 : cohomology M 0),
        Nat.card_of_subsingleton (0 : cohomology M 1), Nat.card_of_subsingleton (0 : cohomology M 2)]
      norm_num
    ·
      have hBfix : ∀ g ∈ (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l) : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left hB
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
        (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l))
        (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l)) hBfix (fun g hg => by
          obtain ⟨n, hn⟩ := isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
            (K := K) (L := L) hlp (QuotientGroup.mk ⟨restrictFixed V g, hg⟩)
          refine ⟨n, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hn
          rw [mem_preimageOpen, map_pow]
          simpa using hn)
      have hAfix : ∀ g ∈ (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) :
          Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
          have : m0 ∈ fixedSubmodule M (preimageOpen V
            (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) := hm0fix
          rw [h] at this
          exact (Submodule.mem_bot _).1 this))
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      have hX := eulerCharacteristic_coprime (U := ⊤)
        (V := preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) hlK le_top
        (by
          rw [show ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = ⊤ from rfl,
            Subgroup.relIndex_top_right, index_preimageOpen]
          exact coprime_card_quotient_primaryQuotientPreimage_lowerRamificationGroup (K := K) (L := L) hlp)
        (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
          (fun ζ' hζ' => pow_eq_one_mem_fixedField_primaryQuotientPreimage (K := K) (L := L) hlp hlq hζ') hζ)
        (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
        (fun g hg m => hAfix g hg m) (n := 0)
        (by
          rw [pow_zero]
          exact card_quotient_span_natCast_eq_one (natCast_residueField_fixedField_ne_zero hl𝓀 ⊤))
      have hres : eulerCharacteristic (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) =
          eulerCharacteristic M := by
        simp only [eulerCharacteristic]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [← Nat.card_eq_of_bijective _ (bijective_res_top M q)]
      rw [← hres, hX, pow_zero, inv_one]

end Simple

end MainSimple

-- from EulerCharGaloisOfCardEq.lean
section EulerCharGaloisOfCardEq
open CategoryTheory IntermediateField ValuativeRel Langlands.ProfiniteCohomology

section Main

attribute [-instance] ULift.module

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerCharacteristic_galois_of_card_eq (n : ℕ) : ∀ (M : Rep (ULift.{u} ℤ) Gal(Ksep/K)) [IsSmoothRep M]
    [Finite M], Nat.card M = n → (Nat.card M : K) ≠ 0 →
      eulerCharacteristic M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn hM
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  rcases subsingleton_or_nontrivial M with hsub | hnt
  ·
    have h1 : Nat.card M = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨0⟩⟩
    rw [eulerCharacteristic_eq_one_of_subsingleton, h1, Nat.cast_one,
      card_quotient_span_eq_one_of_isUnit isUnit_one, Nat.cast_one, inv_one]
  by_cases hs : ∀ N : Submodule (ULift.{u} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤
  · exact eulerCharacteristic_of_forall_eq_bot_or_eq_top M hM hs

  push Not at hs
  obtain ⟨N, hN, hbot, htop⟩ := hs
  let i := Rep.subtype M N hN
  have hi : Function.Injective i.hom := Submodule.injective_subtype N
  have hS := cokerShortComplex_shortExact i hi
  have : IsSmoothRep (cokerShortComplex i).X₁ := isSmoothRep_subrepresentation M N hN
  have : IsSmoothRep (cokerShortComplex i).X₂ := inferInstanceAs (IsSmoothRep M)
  have : Finite (cokerShortComplex i).X₂ := inferInstanceAs (Finite M)
  have : IsSmoothRep (cokerShortComplex i).X₃ :=
    isSmoothRep_quotient M (LinearMap.range i.hom.toLinearMap) (range_hom_le_comap i)
  have hG := hasFiniteCohomology K Ksep
  have hχ := eulerCharacteristic_shortExact hPdvd hG hS hM

  have hrange : LinearMap.range i.hom.toLinearMap = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hX₁ : Nat.card (cokerShortComplex i).X₁ = Nat.card N := rfl
  have hX₃ : Nat.card (cokerShortComplex i).X₃ = Nat.card (M ⧸ LinearMap.range i.hom.toLinearMap) := rfl
  have hcardM : Nat.card M = Nat.card (cokerShortComplex i).X₁ * Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₁, hX₃, Submodule.card_eq_card_quotient_mul_card (LinearMap.range i.hom.toLinearMap),
      Nat.card_congr (LinearEquiv.ofInjective i.hom.toLinearMap hi).toEquiv.symm]
  have : Finite (cokerShortComplex i).X₁ := Finite.of_injective _ hi
  have : Finite (cokerShortComplex i).X₃ :=
    Finite.of_surjective _ (Submodule.mkQ_surjective (LinearMap.range i.hom.toLinearMap))
  have h1 : 1 < Nat.card (cokerShortComplex i).X₁ := by
    rw [hX₁]
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have : Nontrivial N := ⟨⟨⟨x, hxN⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have h3 : 1 < Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₃, hrange]
    have : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 htop
    have : Finite (M ⧸ N) := Finite.of_surjective _ (Submodule.mkQ_surjective N)
    exact Finite.one_lt_card
  have hpos1 : 0 < Nat.card (cokerShortComplex i).X₁ := by omega
  have hpos3 : 0 < Nat.card (cokerShortComplex i).X₃ := by omega
  have hlt1 : Nat.card (cokerShortComplex i).X₁ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_right hpos1 h3
  have hlt3 : Nat.card (cokerShortComplex i).X₃ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_left hpos3 h1
  have hP1 : (Nat.card (cokerShortComplex i).X₁ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM⟩ hM
  have hP3 : (Nat.card (cokerShortComplex i).X₃ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM.trans (mul_comm _ _)⟩ hM
  change eulerCharacteristic (cokerShortComplex i).X₂ = _
  rw [hχ, ih _ hlt1 _ rfl hP1, ih _ hlt3 _ rfl hP3]
  rw [hcardM, card_quotient_span_natCast_mul hP1 hP3]
  push_cast
  rw [mul_inv]

theorem eulerCharacteristic_galois (M : Rep (ULift.{u} ℤ) Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    eulerCharacteristic M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ :=
  eulerCharacteristic_galois_of_card_eq _ M rfl hM

theorem card_cohomology_mul_div_eq (M : Rep (ULift.{u} ℤ) Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    (Nat.card (cohomology M 0) : ℚ) * Nat.card (cohomology M 2) / Nat.card (cohomology M 1) =
      (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  rw [← eulerCharacteristic_eq, eulerCharacteristic_galois M hM]

end Main

end EulerCharGaloisOfCardEq

section Public

open Langlands.ProfiniteCohomology ValuativeRel

variable (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- **The local Euler characteristic formula** (Tate). For a finite smooth `Gal(Ksep/K)`-module
`M` of order invertible in `K`, `|H⁰(M)| · |H²(M)| / |H¹(M)| = |𝒪[K] / |M|·𝒪[K]|⁻¹`. -/
theorem eulerCharacteristic_eq (M : Rep ClassFieldTheory.Local.IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    ProfiniteCohomology.eulerCharacteristic M =
      (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ :=
  eulerCharacteristic_galois M hM

/-- The order of `H¹`: `|H¹(M)| = |H⁰(M)| · |H²(M)| · |𝒪[K] / |M|·𝒪[K]|`. -/
theorem card_cohomology_one (M : Rep ClassFieldTheory.Local.IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    Nat.card (cohomology M 1) = Nat.card (cohomology M 0) * Nat.card (cohomology M 2) *
      Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) := by
  have h := card_cohomology_mul_div_eq M hM
  have hpos : ∀ r, 0 < Nat.card (cohomology M r) := fun r => by
    have := finite_cohomology K Ksep M hM r
    exact Nat.card_pos
  have h0 : (Nat.card (cohomology M 0) : ℚ) ≠ 0 := by exact_mod_cast (hpos 0).ne'
  have h1 : (Nat.card (cohomology M 1) : ℚ) ≠ 0 := by exact_mod_cast (hpos 1).ne'
  have h2 : (Nat.card (cohomology M 2) : ℚ) ≠ 0 := by exact_mod_cast (hpos 2).ne'
  have hc : (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ) ≠ 0 := by
    intro hc
    rw [hc, inv_zero, div_eq_zero_iff, mul_eq_zero] at h
    rcases h with (h | h) | h
    · exact h0 h
    · exact h2 h
    · exact h1 h
  have key : (Nat.card (cohomology M 1) : ℚ) = Nat.card (cohomology M 0) *
      Nat.card (cohomology M 2) * Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) := by
    rw [div_eq_iff h1] at h
    rw [h, mul_right_comm, inv_mul_cancel₀ hc, one_mul]
  exact_mod_cast key

end Public

end Langlands.GaloisCohomology.Local
