import Langlands.LocalFactor.Ramification.Herbrand.RelativeIndex
import Langlands.Correspondence.HenniartTameWeilFields
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Galois.Local.TotallyRamifiedSolvabilityProof
import Langlands.LocalFactor.Ramification.FiniteTameInertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof
import Langlands.Weil.ProfiniteIntegerLiftingProof
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Frobenius parametrization of the actual tame totally ramified fields -/

noncomputable section

namespace Langlands.Henniart

open LocalClassField Weil Weil.Local Ramification.Padic Ramification.HerbrandBridge
open Polynomial

universe u

/-- Inertia with cyclic quotient by a normal p-subgroup has at most one
subgroup of any prescribed prime-to-p index. -/
private theorem subgroup_eq_of_tame_index {G : Type*} [Group G] [Finite G]
    {p m : ℕ} [Fact p.Prime] (hm : ¬ p ∣ m) (P : Subgroup G) [P.Normal]
    (hP : IsPGroup p P) [IsCyclic (G ⧸ P)] (A B : Subgroup G)
    (hA : A.index = m) (hB : B.index = m) : A = B := by
  have contains (H : Subgroup G) (hH : H.index = m) : P ≤ H := by
    obtain ⟨n, hn⟩ := hP.index (H.subgroupOf P)
    have hd : H.relIndex P ∣ m := by
      rw [← hH, ← Langlands.Ramification.HerbrandBridge.relIndex_normal_sup H P]
      exact Subgroup.relIndex_dvd_index_of_le le_sup_right
    have hidx : H.relIndex P = p ^ n := hn
    have hn0 : n = 0 := by
      by_contra h
      exact hm ((dvd_pow_self p h).trans (hidx ▸ hd))
    exact Subgroup.relIndex_eq_one.mp (by rw [hidx, hn0, pow_zero])
  let q := QuotientGroup.mk' P
  have lift_eq (H : Subgroup G) (hH : H.index = m) :
      (H.map q).comap q = H := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr (contains H hH)]
  have hmap : A.map q = B.map q := by
    apply IsCyclic.subgroup_eq_iff_index_eq.mpr
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective P), lift_eq A hA,
      ← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective P), lift_eq B hB,
      hA, hB]
  rw [← lift_eq A hA, hmap, lift_eq B hB]

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local notation "Γ" => Field.absoluteGaloisGroup K.Carrier
local notation "Iₐ" => K.absoluteInertia K.canonicalTopologicalData
local notation "W" => localWeilGroup K
local notation "I" => localInertia K
local notation "π" => localProjection K
local notation "δ" => localResidueDegree K

local instance : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier

private theorem exists_radical_tame_field {m : ℕ} (hm : ¬ p ∣ m) :
    Nonempty (TameTotallyRamifiedExtensions K m) := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  let T := K.canonicalTopologicalData
  let ϖ := T.uniformizer
  have hϖ : T.ord ϖ = 1 := T.ord_uniformizer
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K.Carrier (AlgebraicClosure K.Carrier) ϖ) hm0.pos
  let E := Ramification.Kummer.adjoinFiniteIntermediate K α
  let L := E.asPadicField (p := p)
  let S := L.canonicalTopologicalData
  let f := intermediateEmbedding K E
  let d := extensionDegree K L f
  let r := extensionResidueDegree K L f
  let := L.algebra
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := IsScalarTower.of_algebraMap_eq' rfl
  let β : L.Carrier := IntermediateField.AdjoinSimple.gen K.Carrier α
  have hβ : β ^ m = algebraMap K.Carrier L.Carrier ϖ := Subtype.ext hα
  have hdm : d ≤ m := by
    rw [show d = Module.finrank K.Carrier E.field from K.extensionDegree_intermediateEmbedding E]
    change Module.finrank K.Carrier (IntermediateField.adjoin K.Carrier {α}) ≤ m
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)]
    have hroot : aeval α (X ^ m - C ϖ) = 0 := by
      simpa only [map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr hα
    simpa only [natDegree_X_pow_sub_C] using
      natDegree_le_of_dvd (minpoly.dvd K.Carrier α hroot) (monic_X_pow_sub_C ϖ hm0).ne_zero
  have hv := ramificationIndex_mul_ord_relative_algebraMap K L T S ϖ
  have he : S.ramificationIndex * r = d * T.ramificationIndex :=
    K.ramificationIndex_mul_extensionResidueDegree L f
  have hT : (0 : ℤ) < T.ramificationIndex := by exact_mod_cast T.ramificationIndex_pos
  have hS : (0 : ℤ) < S.ramificationIndex := by exact_mod_cast S.ramificationIndex_pos
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm0.pos
  have hr : (0 : ℤ) < r := by exact_mod_cast extensionResidueDegree_pos K L f
  have ho : (T.ramificationIndex : ℤ) * ((m : ℤ) * S.ord β) = S.ramificationIndex := by
    rw [← hβ, ← zpow_natCast, S.ord_zpow, hϖ, mul_one] at hv
    exact hv
  have hb : 0 < S.ord β := by
    rw [← ho, mul_pos_iff_of_pos_left hT, mul_pos_iff_of_pos_left hmZ] at hS
    exact hS
  have hprod : (m : ℤ) * (S.ord β * (r : ℤ)) = d := by
    apply mul_left_cancel₀ hT.ne'
    calc
      (T.ramificationIndex : ℤ) * ((m : ℤ) * (S.ord β * (r : ℤ))) =
          (S.ramificationIndex : ℤ) * (r : ℤ) := by rw [← ho]; ring
      _ = (T.ramificationIndex : ℤ) * d := by exact_mod_cast (he.trans (mul_comm _ _))
  have hmul : S.ord β * (r : ℤ) = 1 := by
    have hdZ : (d : ℤ) ≤ m := by exact_mod_cast hdm
    have hb₁ : 1 ≤ S.ord β := hb
    have hr₁ : (1 : ℤ) ≤ r := hr
    have hge : 1 ≤ S.ord β * (r : ℤ) := by simpa using mul_le_mul hb₁ hr₁ (by decide : (0:ℤ) ≤ 1) hb.le
    have hle : S.ord β * (r : ℤ) ≤ 1 := by
      apply (mul_le_mul_iff_right₀ hmZ).mp
      simpa only [mul_comm (S.ord β * (r : ℤ)), hprod, mul_one] using hdZ
    omega
  have hr1 : r = 1 := by
    have : (r : ℤ) = 1 := (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul).elim And.right
      (fun h => by omega)
    exact_mod_cast this
  have hd1 : d = m := by rw [hmul, mul_one] at hprod; exact_mod_cast hprod.symm
  exact ⟨⟨E, hd1, hr1, hm⟩⟩

/-- A degree-one element extends its powers to a continuous section of the
absolute residue degree. -/
private theorem exists_residue_section (w : W) (hw : localDegreeInt K w = 1) :
    ∃ s : ProfiniteIntegers →ₜ* Γ,
      (∀ t, δ (s t) = t) ∧ (∀ n : Degree, s (frobenius n) = π w ^ n.toAdd) := by
  let : NonarchimedeanGroup Γ := absoluteGaloisNonarchimedean K.Carrier
  let : CompactSpace Γ := inferInstanceAs (CompactSpace Gal(AlgebraicClosure K.Carrier/K.Carrier))
  let : T2Space Γ := inferInstanceAs (T2Space Gal(AlgebraicClosure K.Carrier/K.Carrier))
  obtain ⟨s, hs, _⟩ := profiniteIntegerLifting.{u} Γ (zpowersHom Γ (π w))
  have hpow (n : Degree) : s (frobenius n) = π w ^ n.toAdd :=
    DFunLike.congr_fun hs n
  have hwproj : δ (π w) = frobenius (Multiplicative.ofAdd 1) := by
    exact w.property.trans (congrArg (fun n : ℤ => frobenius (Multiplicative.ofAdd n)) hw)
  refine ⟨s, ?_, hpow⟩
  have heq := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).equalizer
    ((localResidueDegree K).continuous.comp s.continuous) (continuous_id : Continuous (id : ProfiniteIntegers → _))
  intro t
  apply congrFun (heq ?_) t
  funext n
  change δ (s (frobenius n)) = frobenius n
  rw [hpow, map_zpow, hwproj, ← map_zpow]
  congr 1
  rw [← ofAdd_zsmul, zsmul_one]
  rfl


private theorem section_range_le {w : W} {s : ProfiniteIntegers →ₜ* Γ}
    (hs : ∀ n : Degree, s (frobenius n) = π w ^ n.toAdd) {H : Subgroup Γ}
    (hclosed : IsClosed (H : Set Γ)) (hw : π w ∈ H) : s.toMonoidHom.range ≤ H := by
  rintro x ⟨t, rfl⟩
  refine (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).induction_on t
    (p := fun z => s z ∈ H) (hclosed.preimage s.continuous) fun n => ?_
  change s (frobenius n) ∈ H
  rw [hs]
  exact H.zpow_mem hw _

private theorem residue_section_remainder (s : ProfiniteIntegers →ₜ* Γ)
    (hs : ∀ t, δ (s t) = t) (x : Γ) : x * (s (δ x))⁻¹ ∈ Iₐ := by
  rw [← localResidueDegree_ker K]
  change δ (x * (s (δ x))⁻¹) = 1
  rw [map_mul, map_inv, hs, mul_inv_cancel]

private theorem inertia_sup_eq_top_of_section (s : ProfiniteIntegers →ₜ* Γ)
    (hs : ∀ t, δ (s t) = t) (H : Subgroup Γ) (hH : s.toMonoidHom.range ≤ H) :
    Iₐ ⊔ H = ⊤ := by
  apply top_unique
  intro x _
  have hx := residue_section_remainder K s hs x
  have hy : s (δ x) ∈ H := hH ⟨_, rfl⟩
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using Subgroup.mul_mem_sup hx hy

set_option maxHeartbeats 600000 in
private theorem exists_degree_one_in_field {m : ℕ} (E : TameTotallyRamifiedExtensions K m) :
    ∃ w : W, localDegreeInt K w = 1 ∧ w ∈ tameFieldWeilImage K E := by
  let L := E.1.asPadicField (p := p)
  let v := localGeometricFrobenius L
  refine ⟨intermediateWeilMap K E.1 v, ?_, ⟨v, rfl⟩⟩
  change (localDegree K (intermediateWeilMap K E.1 v)).toAdd = 1
  have hres : extensionResidueDegree K L (intermediateEmbedding K E.1) = 1 := E.2.2.1
  have hv : localDegree L v = Multiplicative.ofAdd (1 : ℤ) := localGeometricFrobenius_degree L
  rw [localDegree_intermediateWeilMap, hres, pow_one, hv]
  rfl

private abbrev fieldFixing (E : FiniteIntermediateExtension K.Carrier) : Subgroup Γ :=
  E.field.fixingSubgroup

private theorem tame_weil_image_eq_comap {m : ℕ} (E : TameTotallyRamifiedExtensions K m) :
    tameFieldWeilImage K E = (fieldFixing K E.1).comap (localProjection K).toMonoidHom :=
  intermediateWeilMap_range K E.1

private theorem fixing_relIndex_inertia {m : ℕ} (E : TameTotallyRamifiedExtensions K m) :
    (fieldFixing K E.1).relIndex Iₐ = m := by
  let H := fieldFixing K E.1
  obtain ⟨w, hw, hwE⟩ := exists_degree_one_in_field K E
  rw [tame_weil_image_eq_comap] at hwE
  obtain ⟨s, hs, hpow⟩ := exists_residue_section K w hw
  have hclosed : IsClosed (H : Set Γ) := InfiniteGalois.fixingSubgroup_isClosed E.1.field
  have htop := inertia_sup_eq_top_of_section K s hs H (section_range_le K hpow hclosed hwE)
  have hdeg : Module.finrank K.Carrier E.1.field = m :=
    (K.extensionDegree_intermediateEmbedding E.1).symm.trans E.2.1
  have hidx : H.index = m :=
    (IntermediateField.finrank_eq_fixingSubgroup_index (AlgebraicClosure K.Carrier)
      E.1.field).symm.trans hdeg
  change H.relIndex Iₐ = m
  rwa [← Langlands.Ramification.HerbrandBridge.relIndex_normal_sup, htop, Subgroup.relIndex_top_right]

local notation "Closure" => AlgebraicClosure K.Carrier
local notation "FiniteGaloisField" => FiniteGaloisIntermediateField K.Carrier Closure

private abbrev finiteZerothGroup (M : FiniteGaloisField) : Subgroup Gal(M/K.Carrier) :=
  lowerRamificationGroup (absoluteFiniteExtension K M).canonicalTopologicalData K.Carrier 0

private theorem absolute_inertia_map_finite (M : FiniteGaloisField) :
    (Iₐ).map (absoluteFiniteRestriction K M).toMonoidHom = finiteZerothGroup K M := by
  unfold finiteZerothGroup
  rw [lowerRamificationGroup_zero]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact absoluteFiniteRestriction_mem_inertia K M ⟨τ, hτ⟩
  · intro hσ
    obtain ⟨τ, hτ⟩ := absoluteInertiaRestriction_surjective K M ⟨σ, hσ⟩
    exact ⟨τ, τ.property, congrArg Subtype.val hτ⟩

private theorem finite_inertia_intersections_eq {m : ℕ} (hm : ¬ p ∣ m) (M : FiniteGaloisField)
    (A B : Subgroup Gal(M/K.Carrier))
    (hA : A.relIndex (finiteZerothGroup K M) = m)
    (hB : B.relIndex (finiteZerothGroup K M) = m) :
    A ⊓ finiteZerothGroup K M = B ⊓ finiteZerothGroup K M := by
  let L := absoluteFiniteExtension K M
  let T := L.canonicalTopologicalData
  obtain ⟨hwild, _, hcyc, _⟩ := finiteTameInertiaStructure p K L T
  let P := finiteWildInInertia T K.Carrier
  let : P.Normal := (lowerRamificationGroup_normal T K.Carrier 1).subgroupOf _
  let : IsCyclic (finiteZerothGroup K M ⧸ P) := hcyc
  have hle : lowerRamificationGroup T K.Carrier 1 ≤ finiteZerothGroup K M :=
    lowerRamificationGroup_antitone T K.Carrier (by decide : 0 ≤ 1)
  have hP : IsPGroup p P := hwild.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have he := subgroup_eq_of_tame_index hm P hP
    (A.subgroupOf (finiteZerothGroup K M)) (B.subgroupOf (finiteZerothGroup K M)) hA hB
  simpa only [Subgroup.subgroupOf_map_subtype] using
    congrArg (fun H => H.map (finiteZerothGroup K M).subtype) he

private theorem finite_inertia_intersection_normal {m : ℕ} (hm : ¬ p ∣ m)
    (M : FiniteGaloisField) (A : Subgroup Gal(M/K.Carrier))
    (hA : A.relIndex (finiteZerothGroup K M) = m) :
    (A ⊓ finiteZerothGroup K M).Normal := by
  let N := finiteZerothGroup K M
  let : N.Normal := lowerRamificationGroup_normal _ K.Carrier 0
  apply Subgroup.normal_iff_map_conj_eq.mpr
  intro g
  let f : Gal(M/K.Carrier) →* Gal(M/K.Carrier) := MulAut.conj g
  have hf : Function.Injective f := (MulAut.conj g).injective
  have hN : N.map f = N := Subgroup.Normal.map_conj_eq N g
  have hAf : (A.map f).relIndex N = m := by
    rw [← hN, Subgroup.relIndex_map_map_of_injective A N hf]
    exact hA
  change (A ⊓ N).map f = A ⊓ N
  rw [Subgroup.map_inf A N f hf, hN]
  exact finite_inertia_intersections_eq K hm M (A.map f) A hAf hA

/-- Above a finite field containing the embedded extension, its fixing
subgroup is the preimage of its finite restriction image. -/
private theorem fixing_eq_comap_restriction (M : FiniteGaloisField)
    (E : FiniteIntermediateExtension K.Carrier) (hE : E.field ≤ M.toIntermediateField) :
    ((fieldFixing K E).map (absoluteFiniteRestriction K M).toMonoidHom).comap
      (absoluteFiniteRestriction K M).toMonoidHom = fieldFixing K E := by
  let : IsGalois K.Carrier M.toIntermediateField := M.isGalois
  let r := AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := Closure) M.toIntermediateField
  change (E.field.fixingSubgroup.map r).comap r = E.field.fixingSubgroup
  rw [Subgroup.comap_map_eq, sup_eq_left, IntermediateField.restrictNormalHom_ker]
  exact IntermediateField.fixingSubgroup_le hE

private theorem common_tame_inertia {m : ℕ} (hm : ¬ p ∣ m)
    (E₀ : TameTotallyRamifiedExtensions K m) :
    (fieldFixing K E₀.1 ⊓ Iₐ).Normal ∧
      ∀ E : TameTotallyRamifiedExtensions K m,
        fieldFixing K E.1 ⊓ Iₐ = fieldFixing K E₀.1 ⊓ Iₐ := by
  have compare (E : TameTotallyRamifiedExtensions K m) :
      (fieldFixing K E₀.1 ⊓ Iₐ).Normal ∧
        fieldFixing K E.1 ⊓ Iₐ = fieldFixing K E₀.1 ⊓ Iₐ := by
    let D := E₀.1.field ⊔ E.1.field
    let L := IntermediateField.normalClosure K.Carrier D Closure
    let M : FiniteGaloisField :=
      { toIntermediateField := L, isGalois := IsGalois.normalClosure _ _ _ }
    let r := (absoluteFiniteRestriction K M).toMonoidHom
    let N := finiteZerothGroup K M
    have hI : (Iₐ).map r = N := absolute_inertia_map_finite K M
    have hD : D ≤ M.toIntermediateField := IntermediateField.le_normalClosure D
    have transport (E' : TameTotallyRamifiedExtensions K m) (hE : E'.1.field ≤ M.toIntermediateField) :
        let A := (fieldFixing K E'.1).map r
        A.relIndex N = m ∧ fieldFixing K E'.1 ⊓ Iₐ = (A ⊓ N).comap r ⊓ Iₐ := by
      dsimp only
      have hfix := fixing_eq_comap_restriction K M E'.1 hE
      constructor
      · rw [← hI, ← Subgroup.relIndex_comap, hfix]
        exact fixing_relIndex_inertia K E'
      · rw [Subgroup.comap_inf, hfix]
        ext x
        exact ⟨fun hx => ⟨⟨hx.1, hI ▸ Subgroup.mem_map_of_mem r hx.2⟩, hx.2⟩,
          fun hx => ⟨hx.1.1, hx.2⟩⟩
    obtain ⟨h₀, he₀⟩ := transport E₀ (le_sup_left.trans hD)
    obtain ⟨he, he₁⟩ := transport E (le_sup_right.trans hD)
    rw [he₀, he₁]
    let : ((Subgroup.map r (fieldFixing K E₀.1) ⊓ N).comap r).Normal :=
      (finite_inertia_intersection_normal K hm M _ h₀).comap r
    exact ⟨inferInstance, congrArg (fun S : Subgroup Gal(M/K.Carrier) => S.comap r ⊓ Iₐ)
      (finite_inertia_intersections_eq K hm M _ _ he h₀)⟩
  exact ⟨(compare E₀).1, fun E => (compare E).2⟩

private theorem exists_unique_tame_field_for_lift {m : ℕ} (hm : ¬ p ∣ m)
    (J : Subgroup Γ) [J.Normal] (hclosed : IsClosed (J : Set Γ)) (hJI : J ≤ Iₐ)
    (hindex : J.relIndex Iₐ = m)
    (hcommon : ∀ E : TameTotallyRamifiedExtensions K m, fieldFixing K E.1 ⊓ Iₐ = J)
    (w : W) (hw : localDegreeInt K w = 1) :
    ∃! E : TameTotallyRamifiedExtensions K m, w ∈ tameFieldWeilImage K E := by
  obtain ⟨s, hs, hpow⟩ := exists_residue_section K w hw
  let D := J ⊔ s.toMonoidHom.range
  have hmem (x : Γ) : x ∈ D ↔ x * (s (δ x))⁻¹ ∈ J := by
    constructor
    · intro hx
      obtain ⟨j, hj, _, ⟨t, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      have hj' : δ j = 1 := by
        have h := hJI hj
        rwa [← localResidueDegree_ker K] at h
      change j * s t * (s (δ (j * s t)))⁻¹ ∈ J
      rwa [map_mul, hj', one_mul, hs, mul_assoc, mul_inv_cancel, mul_one]
    · intro hx
      have hy : s (δ x) ∈ s.toMonoidHom.range := ⟨_, rfl⟩
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using Subgroup.mul_mem_sup hx hy
  have hDclosed : IsClosed (D : Set Γ) := by
    rw [show (D : Set Γ) = (fun x : Γ => x * (s (δ x))⁻¹) ⁻¹' (J : Set Γ) from Set.ext hmem]
    exact hclosed.preimage (continuous_id.mul (s.continuous.comp (localResidueDegree K).continuous).inv)
  have hinter : D ⊓ Iₐ = J := by
    apply le_antisymm
    · rintro x ⟨hx, hi⟩
      have hd : δ x = 1 := by rwa [← localResidueDegree_ker K] at hi
      simpa only [hd, map_one, inv_one, mul_one] using (hmem x).mp hx
    · exact le_inf le_sup_left hJI
  have htop := inertia_sup_eq_top_of_section K s hs D le_sup_right
  have hDindex : D.index = m := by
    rw [← Subgroup.relIndex_top_right, ← htop, Langlands.Ramification.HerbrandBridge.relIndex_normal_sup,
      ← Subgroup.inf_relIndex_right D Iₐ, hinter]
    exact hindex
  let : D.FiniteIndex := ⟨fun h => hm (hDindex ▸ h ▸ dvd_zero p)⟩
  let DC : ClosedSubgroup Gal(Closure/K.Carrier) := ⟨D, hDclosed⟩
  let L := IntermediateField.fixedField DC.toSubgroup
  let H : Subgroup Γ := L.fixingSubgroup
  have hfix : H = D := InfiniteGalois.fixingSubgroup_fixedField DC
  have hopen : IsOpen (H : Set Γ) := hfix.symm ▸ D.isOpen_of_isClosed_of_finiteIndex hDclosed
  have hfinite : FiniteDimensional K.Carrier L := (InfiniteGalois.isOpen_iff_finite L).mp hopen
  let E : FiniteIntermediateExtension K.Carrier := ⟨L, hfinite⟩
  let EP := E.asPadicField (p := p)
  let f := intermediateEmbedding K E
  have hdegree : extensionDegree K EP f = m := by
    rw [K.extensionDegree_intermediateEmbedding E,
      IntermediateField.finrank_eq_fixingSubgroup_index Closure]
    change H.index = m
    exact (congrArg (fun S : Subgroup Γ => S.index) hfix).trans hDindex
  have hwD : π w ∈ D := by
    have h := hpow (Multiplicative.ofAdd 1)
    change s (frobenius (Multiplicative.ofAdd 1)) = π w ^ (1 : ℤ) at h
    rw [zpow_one] at h
    exact Subgroup.mem_sup_right (show π w ∈ s.toMonoidHom.range from ⟨_, h⟩)
  have hwE : w ∈ pullbackFixingSubgroup K.Carrier E.field (localResidueDegree K) := by
    change π w ∈ H
    rwa [hfix]
  have hres : extensionResidueDegree K EP f = 1 := by
    let wE : pullbackFixingSubgroup K.Carrier E.field (localResidueDegree K) := ⟨w, hwE⟩
    have h := intermediateWeilEquiv_symm_degree K E wE
    change localDegreeInt K w = (extensionResidueDegree K EP f : ℤ) *
      localDegreeInt EP ((intermediateWeilEquiv K E).symm wE) at h
    rw [hw] at h
    have hz : (extensionResidueDegree K EP f : ℤ) = 1 :=
      (Int.mul_eq_one_iff_eq_one_or_neg_one.mp h.symm).elim And.left (fun hh => by omega)
    exact_mod_cast hz
  let E' : TameTotallyRamifiedExtensions K m := ⟨E, hdegree, hres, hm⟩
  refine ⟨E', ?_, ?_⟩
  · change w ∈ tameFieldWeilImage K E'
    rw [tame_weil_image_eq_comap]
    exact hwE
  · intro F hwF
    change w ∈ tameFieldWeilImage K F at hwF
    rw [tame_weil_image_eq_comap] at hwF
    let B := fieldFixing K F.1
    have hB : s.toMonoidHom.range ≤ B := section_range_le K hpow
      (InfiniteGalois.fixingSubgroup_isClosed F.1.field) hwF
    have hBJ : B ⊓ Iₐ = J := hcommon F
    have hBD : B = D := by
      apply le_antisymm
      · intro x hx
        apply (hmem x).mpr
        rw [← hBJ]
        exact ⟨B.mul_mem hx (B.inv_mem (hB ⟨_, rfl⟩)), residue_section_remainder K s hs x⟩
      · exact sup_le (hBJ ▸ inf_le_left) hB
    apply Subtype.ext
    apply Subtype.ext
    change F.1.field = L
    have hfix' : F.1.field.fixingSubgroup = DC.toSubgroup := hBD
    exact (InfiniteGalois.fixedField_fixingSubgroup F.1.field).symm.trans
      (congrArg IntermediateField.fixedField hfix')

private theorem weil_inertia_map_projection :
    (I).map (localProjection K).toMonoidHom = Iₐ := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (localInertiaEquiv K ⟨w, hw⟩).2
  · intro hx
    let w := (localInertiaEquiv K).symm ⟨x, hx⟩
    exact ⟨w, w.property, congrArg Subtype.val ((localInertiaEquiv K).apply_symm_apply ⟨x, hx⟩)⟩

private theorem tameWeilFrobeniusParametrizationFor (m : ℕ) (hm : ¬ p ∣ m)
    (φ : W) (hφ : localDegreeInt K φ = 1) : Nonempty (TameWeilFrobeniusData K m φ) := by
  obtain ⟨E₀⟩ := exists_radical_tame_field K hm
  let J := fieldFixing K E₀.1 ⊓ Iₐ
  obtain ⟨hJn, hcommon⟩ := common_tame_inertia K hm E₀
  let : J.Normal := hJn
  have hclosed : IsClosed (J : Set Γ) :=
    (InfiniteGalois.fixingSubgroup_isClosed E₀.1.field).inter
      (K.absoluteInertia_isClosed K.canonicalTopologicalData)
  have hindex : J.relIndex Iₐ = m := by
    rw [Subgroup.inf_relIndex_right]
    exact fixing_relIndex_inertia K E₀
  let Jw : OpenNormalSubgroup W :=
    { toSubgroup := J.comap (localProjection K).toMonoidHom
      isOpen' := by
        change IsOpen (((fieldFixing K E₀.1 ⊓ Iₐ).comap (localProjection K).toMonoidHom :
          Subgroup W) : Set W)
        rw [Subgroup.comap_inf, ← localInertia_eq_comap]
        exact (E₀.1.field.fixingSubgroup_isOpen.preimage (localProjection K).continuous).inter
          (localInertia_isOpen K)
      isNormal' := inferInstance }
  have hJw : Jw.toSubgroup ≤ I := by
    rw [localInertia_eq_comap]
    exact Subgroup.comap_mono inf_le_right
  have hinter (E : TameTotallyRamifiedExtensions K m) :
      tameFieldWeilImage K E ⊓ I = Jw.toSubgroup := by
    rw [tame_weil_image_eq_comap, localInertia_eq_comap, ← Subgroup.comap_inf, hcommon E]
  let Q := tameInertiaCosets K Jw
  have hcard : Nat.card Q = m := by
    change (J.comap (localProjection K).toMonoidHom).relIndex I = m
    rw [Subgroup.relIndex_comap, weil_inertia_map_projection, hindex]
  have hQfin : Finite Q := Nat.finite_of_card_ne_zero (hcard.symm ▸ fun h => hm (h ▸ dvd_zero p))
  let : Fintype Q := Fintype.ofFinite Q
  let enum : Fin m ≃ Q := (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := Q)).symm.trans hcard)).symm
  have lift_degree (g : I) : localDegreeInt K ((g : W) * φ) = 1 := by
    change (localDegree K ((g : W) * φ)).toAdd = 1
    rw [map_mul, show localDegree K (g : W) = 1 from g.property, one_mul]
    exact hφ
  have lift_field (g : I) : ∃! E : TameTotallyRamifiedExtensions K m,
      (g : W) * φ ∈ tameFieldWeilImage K E :=
    exists_unique_tame_field_for_lift K hm J hclosed inf_le_right hindex hcommon _ (lift_degree g)
  let fieldOf (g : I) := (lift_field g).exists.choose
  have hfield (g : I) : (g : W) * φ ∈ tameFieldWeilImage K (fieldOf g) :=
    (lift_field g).exists.choose_spec
  have same_field {g h : I} (he : (QuotientGroup.mk g : Q) = QuotientGroup.mk h) :
      fieldOf g = fieldOf h := by
    apply (lift_field h).unique _ (hfield h)
    have hjI : h / g ∈ Jw.toSubgroup.subgroupOf I := QuotientGroup.eq_iff_div_mem.mp he.symm
    have hj : (h : W) / (g : W) ∈ Jw.toSubgroup := hjI
    rw [← hinter (fieldOf g)] at hj
    have hh := (tameFieldWeilImage K (fieldOf g)).mul_mem hj.1 (hfield g)
    simpa only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left] using hh
  let F : Q → TameTotallyRamifiedExtensions K m :=
    Quotient.lift fieldOf (fun _ _ h => same_field (Quotient.sound h))
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      change fieldOf g = fieldOf h at hxy
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (g : W) / (h : W) ∈ Jw.toSubgroup
      rw [← hinter (fieldOf h)]
      have hg := hfield g
      rw [hxy] at hg
      have hratio : (g : W) / (h : W) ∈ tameFieldWeilImage K (fieldOf h) := by
        have hdiv := (tameFieldWeilImage K (fieldOf h)).div_mem hg (hfield h)
        simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hdiv
      exact ⟨hratio, (localInertia K).div_mem g.property h.property⟩
    · intro E
      obtain ⟨w, hw, hwE⟩ := exists_degree_one_in_field K E
      have hEq : localDegree K w = localDegree K φ :=
        congrArg Multiplicative.ofAdd (hw.trans hφ.symm)
      have hwI : w / φ ∈ I := by
        change localDegree K (w / φ) = 1
        rw [_root_.map_div, hEq, div_self']
      let g : I := ⟨w / φ, hwI⟩
      refine ⟨QuotientGroup.mk g, (lift_field g).unique (hfield g) ?_⟩
      change (w / φ) * φ ∈ tameFieldWeilImage K E
      simpa only [div_mul_cancel] using hwE
  exact ⟨⟨Jw, hJw, enum, Equiv.ofBijective F hF, fun a => hinter (F a), hfield⟩⟩

/-- Degree-`m` tame totally ramified embedded fields are indexed by the
translates of any given geometric Frobenius, modulo their common inertia kernel. -/
theorem tameWeilFrobeniusParametrization : TameWeilFrobeniusParametrizationStatement.{u} := by
  intro p _ K m hm φ hφ
  exact tameWeilFrobeniusParametrizationFor K m hm φ hφ

end Langlands.Henniart
