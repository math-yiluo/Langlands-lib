import Langlands.Cohomology.Profinite.ClassFormation.Basic
import Langlands.Cohomology.Profinite.InflationRestriction.Higher

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

namespace QZ

theorem mem_of_nsmul_eq_zero (P : Set Nat.Primes) (H : AddSubgroup QZ)
    (hH : ∀ p ∈ P, ∀ x ∈ AddCommMonoid.primaryComponent QZ (p : ℕ), x ∈ H) :
    ∀ (n : ℕ), n ≠ 0 → (∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ P) →
      ∀ x : QZ, n • x = 0 → x ∈ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hP x hx
    rcases eq_or_ne n 1 with rfl | h1
    · rw [one_smul] at hx
      rw [hx]
      exact H.zero_mem
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at hnm
        exact hn hnm
      have ha : 0 < a := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [pow_zero, one_mul] at hnm
          exact absurd (hnm ▸ Nat.minFac_dvd n) hpm
        · exact ha
      have hcop : Nat.Coprime (p ^ a) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)

      have hbez := Nat.gcd_eq_gcd_ab (p ^ a) m
      rw [hcop.gcd_eq_one] at hbez
      have hx' : x = ((p ^ a : ℕ) * Nat.gcdA (p ^ a) m : ℤ) • x +
          ((m : ℕ) * Nat.gcdB (p ^ a) m : ℤ) • x := by
        rw [← add_smul, ← hbez]
        simp
      rw [hx']
      refine H.add_mem ?_ ?_
      ·
        have hmn : m < n := by
          rw [hnm]
          calc m = 1 * m := (one_mul m).symm
            _ < p ^ a * m := by
              apply Nat.mul_lt_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0)
              exact Nat.one_lt_pow ha.ne' hp.one_lt
        refine ih m hmn hm0 (fun q hq => hP q (hnm ▸ Dvd.dvd.mul_left hq _)) _ ?_
        rw [← natCast_zsmul, smul_smul]
        have : ((m : ℤ) * ((p ^ a : ℕ) * Nat.gcdA (p ^ a) m : ℤ)) =
            (Nat.gcdA (p ^ a) m) * (n : ℤ) := by
          rw [hnm]
          push_cast
          ring
        rw [this, ← smul_smul, natCast_zsmul, hx, smul_zero]
      ·
        have hpP : (⟨p, hp⟩ : Nat.Primes) ∈ P := hP ⟨p, hp⟩ (Nat.minFac_dvd n)
        refine hH _ hpP _ ⟨a, ?_⟩
        change (p : ℕ) ^ a • _ = 0
        rw [← natCast_zsmul, smul_smul]
        have : ((p ^ a : ℕ) : ℤ) * ((m : ℕ) * Nat.gcdB (p ^ a) m : ℤ) =
            (Nat.gcdB (p ^ a) m) * (n : ℤ) := by
          rw [hnm]
          push_cast
          ring
        rw [Nat.cast_pow] at this ⊢
        rw [this, ← smul_smul, natCast_zsmul, hx, smul_zero]

end QZ

variable {k G : Type u} [CommRing k] [Group G]

section Preimage

variable (U V : Subgroup G) [(V.subgroupOf U).Normal]

def quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) : Subgroup G :=
  (S.comap (QuotientGroup.mk' (V.subgroupOf U))).map U.subtype

variable {U V}

theorem quotPreimage_le (S : Subgroup (U ⧸ V.subgroupOf U)) : quotPreimage U V S ≤ U :=
  Subgroup.map_subtype_le _

theorem mem_quotPreimage {S : Subgroup (U ⧸ V.subgroupOf U)} {g : G} (hg : g ∈ U) :
    g ∈ quotPreimage U V S ↔ ((⟨g, hg⟩ : U) : U ⧸ V.subgroupOf U) ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem le_quotPreimage (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    V ≤ quotPreimage U V S := by
  intro v hv
  rw [mem_quotPreimage (hVU hv), (QuotientGroup.eq_one_iff _).2 (by exact hv)]
  exact S.one_mem

def quotPreimageHom (S : Subgroup (U ⧸ V.subgroupOf U)) : quotPreimage U V S →* S :=
  ((QuotientGroup.mk' (V.subgroupOf U)).comp
    (Subgroup.inclusion (quotPreimage_le S))).codRestrict S fun w =>
      (mem_quotPreimage (quotPreimage_le S w.2)).1 w.2

@[simp]
theorem coe_quotPreimageHom_apply (S : Subgroup (U ⧸ V.subgroupOf U)) (w : quotPreimage U V S) :
    (quotPreimageHom S w : U ⧸ V.subgroupOf U) =
      ((⟨w.1, quotPreimage_le S w.2⟩ : U) : U ⧸ V.subgroupOf U) :=
  rfl

theorem quotPreimageHom_surjective (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Function.Surjective (quotPreimageHom S) := by
  rintro ⟨s, hs⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  exact ⟨⟨x.1, (mem_quotPreimage x.2).2 hs⟩, rfl⟩

theorem quotPreimageHom_eq_one_iff (S : Subgroup (U ⧸ V.subgroupOf U)) (w : quotPreimage U V S) :
    quotPreimageHom S w = 1 ↔ (w : G) ∈ V := by
  rw [← Subtype.coe_inj, coe_quotPreimageHom_apply, Subgroup.coe_one, QuotientGroup.eq_one_iff]
  exact Iff.rfl

theorem quotPreimageHom_ker (S : Subgroup (U ⧸ V.subgroupOf U)) :
    (quotPreimageHom S).ker = V.subgroupOf (quotPreimage U V S) := by
  ext w
  rw [MonoidHom.mem_ker, quotPreimageHom_eq_one_iff]
  exact Iff.rfl

theorem normal_subgroupOf_quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) :
    (V.subgroupOf (quotPreimage U V S)).Normal := by
  rw [← quotPreimageHom_ker]
  exact MonoidHom.normal_ker _

attribute [instance] normal_subgroupOf_quotPreimage

noncomputable def quotPreimageEquiv (S : Subgroup (U ⧸ V.subgroupOf U)) :
    quotPreimage U V S ⧸ V.subgroupOf (quotPreimage U V S) ≃* S :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ (quotPreimageHom S) (quotPreimageHom_ker S).ge)
    ⟨(QuotientGroup.injective_lift_iff _ _ _).2 (quotPreimageHom_ker S).symm, by
      intro s
      obtain ⟨w, rfl⟩ := quotPreimageHom_surjective S s
      exact ⟨w, rfl⟩⟩

theorem relIndex_quotPreimage (S : Subgroup (U ⧸ V.subgroupOf U)) :
    V.relIndex (quotPreimage U V S) = Nat.card S := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_congr (quotPreimageEquiv S).toEquiv

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in

theorem continuous_quotPreimageHom (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageHom S) :=
  (QuotientGroup.continuous_mk.comp (continuous_subgroup_inclusion (quotPreimage_le S))).subtype_mk
    _

omit [IsTopologicalGroup G] in

theorem continuous_quotPreimageEquiv (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageEquiv S).toMonoidHom := by
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_quotPreimageHom S)

omit [IsTopologicalGroup G] in
theorem isOpen_subgroupOf {V : Subgroup G} (hV : IsOpen (V : Set G)) (W : Subgroup G) :
    IsOpen (V.subgroupOf W : Set W) :=
  hV.preimage continuous_subtype_val

omit [(V.subgroupOf U).Normal] in

theorem discreteTopology_quot (hV : IsOpen (V : Set G)) :
    DiscreteTopology (U ⧸ V.subgroupOf U) :=
  QuotientGroup.discreteTopology (isOpen_subgroupOf hV U)

theorem continuous_quotPreimageEquiv_symm (hV : IsOpen (V : Set G))
    (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Continuous (quotPreimageEquiv S).symm.toMonoidHom := by
  have := discreteTopology_quot (U := U) hV
  exact continuous_of_discreteTopology

end Preimage

section Cohomology

variable [TopologicalSpace G] [IsTopologicalGroup G] {U V : Subgroup G} [(V.subgroupOf U).Normal]
  (C : Rep.{u} k G) [IsSmoothRep C]

instance isSmoothRep_res_quotientToInvariants_res (S : Subgroup (U ⧸ V.subgroupOf U)) :
    IsSmoothRep (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) :=
  isSmoothRep_res_subtype _ _

noncomputable def quotPreimageRepHom (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Rep.res (quotPreimageHom S)
        (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) ⟶
      Rep.res (quotPreimage U V S).subtype C :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

noncomputable def inflQuot (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    cohomology (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) n ⟶
      cohomology (Rep.res (quotPreimage U V S).subtype C) n :=
  map ⟨quotPreimageHom S, continuous_quotPreimageHom S⟩ (quotPreimageRepHom C S) n

@[reassoc]
theorem res_comp_inflQuot (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    res ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) S n ≫
        inflQuot C S n =
      infl (Rep.res U.subtype C) (V.subgroupOf U) n ≫
        resOfLE C (quotPreimage_le S) n := by
  have : IsSmoothRep (Rep.of (Rep.res U.subtype C).ρ) := isSmoothRep_res_subtype C U
  rw [res, inflQuot, ← map_comp, infl,
    resOfLE, ← map_comp]
  exact map_congr _ _ (by ext; rfl) (fun _ => rfl) n

noncomputable def quotPreimageInvHom (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Rep.res (quotPreimageEquiv S).toMonoidHom
        (Rep.res S.subtype ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U))) ⟶
      (Rep.res (quotPreimage U V S).subtype C).quotientToInvariants
        (V.subgroupOf (quotPreimage U V S)) :=
  Rep.ofHom
    { toFun := fun m => ⟨m.1, fun n => m.2 ⟨⟨n.1.1, hVU n.2⟩, n.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun x => by
        induction x using QuotientGroup.induction_on
        rfl }

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep C] in
theorem quotPreimageInvHom_bijective (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    Function.Bijective (quotPreimageInvHom C hVU S).hom := by
  refine ⟨fun a b h => ?_, fun c => ?_⟩
  · apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  refine ⟨⟨c.1, fun n => c.2 ⟨⟨n.1.1, le_quotPreimage hVU S n.2⟩, n.2⟩⟩, rfl⟩

theorem inflQuot_eq (hVU : V ≤ U) (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    inflQuot C S n =
      map ⟨(quotPreimageEquiv S).toMonoidHom, continuous_quotPreimageEquiv S⟩
          (quotPreimageInvHom C hVU S) n ≫
        infl (Rep.res (quotPreimage U V S).subtype C)
          (V.subgroupOf (quotPreimage U V S)) n := by
  rw [infl, ← map_comp, inflQuot]
  exact map_congr _ _ (by ext; rfl) (fun _ => rfl) n

theorem isIso_map_quotPreimageEquiv (hV : IsOpen (V : Set G)) (hVU : V ≤ U)
    (S : Subgroup (U ⧸ V.subgroupOf U)) (n : ℕ) :
    IsIso (map ⟨(quotPreimageEquiv S).toMonoidHom, continuous_quotPreimageEquiv S⟩
      (quotPreimageInvHom C hVU S) n) :=
  isIso_map_of_mulEquiv _ _ (continuous_quotPreimageEquiv_symm hV S) _
    (quotPreimageInvHom_bijective C hVU S) n

end Cohomology

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits

universe u

namespace QZ

theorem cyclic_of_injective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (Φ : X →+ Y)
    (hΦ : Function.Injective Φ) (inv : Y →+ QZ) (hinv : Function.Injective inv) {n : ℕ}
    (hn : 0 < n) (hker : ∀ x, n • inv (Φ x) = 0) (e : X) (he : inv (Φ e) = mk (1 / n)) :
    addOrderOf e = n ∧ ∀ x, ∃ m : ℤ, x = m • e := by
  have hι : Function.Injective (inv.comp Φ) := hinv.comp hΦ
  refine ⟨?_, fun x => ?_⟩
  · rw [← addOrderOf_injective (inv.comp Φ) hι e, AddMonoidHom.comp_apply, he,
      addOrderOf_mk_one_div hn]
  · obtain ⟨m, hm⟩ := exists_eq_nsmul_mk_one_div hn (hker x)
    refine ⟨m, hι ?_⟩
    rw [map_zsmul, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, he, hm, natCast_zsmul]

theorem nsmul_mk_one_div_mul {a b : ℕ} (ha : a ≠ 0) : a • mk (1 / (a * b : ℕ)) = mk (1 / b) := by
  rw [← mk_nsmul, nsmul_eq_mul]
  congr 1
  push_cast
  field_simp

end QZ

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compactSpace_of_isOpen [CompactSpace G] {W : Subgroup G} (hW : IsOpen (W : Set G)) :
    CompactSpace W :=
  isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact

section InfRes

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  (A : Rep.{u} k G) [IsSmoothRep A] {U V : Subgroup G} (hU : IsOpen (U : Set G))
  (hV : IsOpen (V : Set G)) (hVU : V ≤ U) [(V.subgroupOf U).Normal]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [(V.subgroupOf U).Normal] in
include hVU in

theorem isZero_H1_subgroupOf (h1 : IsZero (cohomology (Rep.res V.subtype A) 1)) :
    IsZero (cohomology (Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A)) 1) :=
  h1.of_iso (asIso (map (subgroupOfEquivOfLeSymmHom hVU) (resSubgroupOfHom hVU A) 1))

include hU hV hVU in

theorem infl_two_injective_of_open (h1 : IsZero (cohomology (Rep.res V.subtype A) 1)) :
    Function.Injective (infl (Rep.res U.subtype A) (V.subgroupOf U) 2).hom := by
  have := compactSpace_of_isOpen hU
  exact infl_injective_of_isZero (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf hV U))
    two_ne_zero fun i hi hi2 => by
      obtain rfl : i = 1 := by omega
      exact isZero_H1_subgroupOf A hVU h1

include hU hV in

theorem mem_range_infl_two_iff (h1 : IsZero (cohomology (Rep.res V.subtype A) 1))
    (x : cohomology (Rep.res U.subtype A) 2) :
    (∃ y, (infl (Rep.res U.subtype A) (V.subgroupOf U) 2).hom y = x) ↔
      (resOfLE A hVU 2).hom x = 0 := by
  rw [resOfLE_apply_eq_zero_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← ModuleCat.comp_apply, infl_comp_res _ _ 1]
    rfl
  · intro hx
    have := compactSpace_of_isOpen hU
    have hx' : x ∈ LinearMap.ker (res (Rep.res U.subtype A) (V.subgroupOf U) 2).hom := hx
    rw [← range_infl_eq_ker_res
      (Subgroup.isClosed_of_isOpen _ (isOpen_subgroupOf hV U)) two_ne_zero fun i hi hi2 => by
        obtain rfl : i = 1 := by omega
        exact isZero_H1_subgroupOf A hVU h1] at hx'
    exact hx'

end InfRes

theorem relIndex_ne_zero_of_isOpen [CompactSpace G] {V : Subgroup G} (hV : IsOpen (V : Set G))
    (U : Subgroup G) : V.relIndex U ≠ 0 := by
  have := Subgroup.quotient_finite_of_isOpen V hV
  have := Subgroup.finiteIndex_of_finite_quotient (H := V)
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := V) (K := U)
  exact Subgroup.relIndex_ne_zero

def quotPreimageOpen {U V : OpenSubgroup G} [((V : Subgroup G).subgroupOf U).Normal]
    (hVU : V ≤ U) (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) : OpenSubgroup G where
  toSubgroup := quotPreimage (U : Subgroup G) V S
  isOpen' := Subgroup.isOpen_mono (le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S) V.isOpen

instance normal_subgroupOf_quotPreimageOpen {U V : OpenSubgroup G}
    [((V : Subgroup G).subgroupOf U).Normal] (hVU : V ≤ U)
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    ((V : Subgroup G).subgroupOf (quotPreimageOpen hVU S : Subgroup G)).Normal :=
  normal_subgroupOf_quotPreimage S

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsSmoothRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

theorem mem_range_infl_two_iff (x : H2Open C U) :
    (∃ y, (infl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom y = x) ↔
      (resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x = 0 :=
  Langlands.ProfiniteCohomology.mem_range_infl_two_iff C U.isOpen V.isOpen hVU (F.isZero_H1_open_subgroups V) x

include hVU in

theorem inv_infl_fundamentalClass (hVinj : Function.Injective (F.inv V))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    F.inv U ((infl (Rep.res (U : Subgroup G).subtype C)
        ((V : Subgroup G).subgroupOf U) 2).hom (F.fundamentalClass U V)) =
      QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)) := by
  obtain ⟨x, hx⟩ := hex
  have hres : (resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x = 0 :=
    (F.resLE_eq_zero_iff hVU hVinj x).2 (by rw [hx]; exact QZ.nsmul_mk_one_div _)
  obtain ⟨y, hy⟩ := (F.mem_range_infl_two_iff hVU x).2 hres
  have : Nonempty (H2Quotient C U V) := ⟨0⟩
  exact Function.invFun_eq (f := fun y : H2Quotient C U V => F.inv U ((infl
    (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) 2).hom y))
    ⟨y, by simp only [hy, hx]⟩

section Subgroup

variable (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U))

omit [CompactSpace G] [TotallyDisconnectedSpace G] F in
include hVU in

theorem inflQuot_one_injective : Function.Injective (inflQuot C S 1).hom := by
  rw [inflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 1, ModuleCat.hom_comp]
  have := isIso_map_quotPreimageEquiv C V.isOpen
    (show (V : Subgroup G) ≤ U from hVU) S 1
  exact (infl_one_injective _ _).comp ((ModuleCat.mono_iff_injective _).1 inferInstance)

include hVU in

theorem inflQuot_two_injective : Function.Injective (inflQuot C S 2).hom := by
  have hVW : (V : Subgroup G) ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  rw [inflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 2, ModuleCat.hom_comp]
  have := isIso_map_quotPreimageEquiv C V.isOpen
    (show (V : Subgroup G) ≤ U from hVU) S 2
  exact (infl_two_injective_of_open C (quotPreimageOpen hVU S).isOpen V.isOpen hVW
    (F.isZero_H1_open_subgroups V)).comp ((ModuleCat.mono_iff_injective _).1 inferInstance)

theorem resLE_inflQuot (y) :
    (resOfLE C (le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S) 2).hom
      ((inflQuot C S 2).hom y) = 0 := by
  have hVW : (V : Subgroup G) ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  refine (Langlands.ProfiniteCohomology.mem_range_infl_two_iff C (quotPreimageOpen hVU S).isOpen V.isOpen
    hVW (F.isZero_H1_open_subgroups V) _).1 ?_
  rw [inflQuot_eq C (show (V : Subgroup G) ≤ U from hVU) S 2, ModuleCat.hom_comp]
  exact ⟨_, rfl⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem inv_inflQuot_res (z : H2Quotient C U V) :
    F.inv (quotPreimageOpen hVU S) ((inflQuot C S 2).hom
        ((res ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom z)) =
      ((quotPreimageOpen hVU S : Subgroup G).relIndex U) •
        F.inv U ((infl (Rep.res (U : Subgroup G).subtype C)
          ((V : Subgroup G).subgroupOf U) 2).hom z) := by
  have h := congrArg (fun φ => φ.hom z) (res_comp_inflQuot C S 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  exact F.inv_res U (quotPreimageOpen hVU S) (quotPreimage_le S) _

include hVU in

theorem inv_inflQuot_res_fundamentalClass
    (hVinj : Function.Injective (F.inv V))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    F.inv (quotPreimageOpen hVU S) ((inflQuot C S 2).hom
        ((res ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V))) =
      QZ.mk (1 / ((V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) : ℚ)) := by
  have hVW : V ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  have hidx : (V : Subgroup G).relIndex U =
      (quotPreimageOpen hVU S : Subgroup G).relIndex U *
        (V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) := by
    rw [mul_comm]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ hVW (quotPreimage_le S)).symm
  rw [F.inv_inflQuot_res hVU S, F.inv_infl_fundamentalClass hVU
    hVinj hex, hidx, QZ.nsmul_mk_one_div_mul (relIndex_ne_zero_of_isOpen
      (quotPreimageOpen hVU S).isOpen _)]

include hVU in

theorem cyclic_res_fundamentalClass (hinj : ∀ W : OpenSubgroup G, Function.Injective (F.inv W))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ))) :
    addOrderOf ((res ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (res ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V) := by
  have hVW : V ≤ quotPreimageOpen hVU S :=
    le_quotPreimage (show (V : Subgroup G) ≤ U from hVU) S
  have hcard : (V : Subgroup G).relIndex (quotPreimageOpen hVU S : Subgroup G) = Nat.card S :=
    relIndex_quotPreimage S
  refine QZ.cyclic_of_injective (inflQuot C S 2).hom.toAddMonoidHom
    (F.inflQuot_two_injective hVU S) (F.inv (quotPreimageOpen hVU S))
    (hinj _) (hcard ▸ Nat.pos_of_ne_zero (relIndex_ne_zero_of_isOpen V.isOpen _)) (fun y => ?_) _ ?_
  · rw [← hcard]
    exact (F.resLE_eq_zero_iff hVW (hinj V) _).1 (F.resLE_inflQuot hVU S y)
  · change F.inv (quotPreimageOpen hVU S) ((inflQuot C S 2).hom _) = _
    rw [F.inv_inflQuot_res_fundamentalClass hVU S (hinj V) hex, hcard]

end Subgroup

noncomputable def groupFundamentalClass (U V : OpenSubgroup G)
    [((V : Subgroup G).subgroupOf U).Normal] :
    groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
      ((V : Subgroup G).subgroupOf U)) 2 :=
  (toGroupCohomology _ 2).hom (F.fundamentalClass U V)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem groupCohomology_map_groupFundamentalClass
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    (groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V) =
      (toGroupCohomology _ 2).hom
        ((res ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U)) S 2).hom (F.fundamentalClass U V)) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ (F.fundamentalClass U V))
    (res_comp_toGroupCohomology
      ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants ((V : Subgroup G).subgroupOf U))
      S 2)
  exact h.symm

include hVU in

theorem tate_hypotheses (hinj : ∀ W : OpenSubgroup G, Function.Injective (F.inv W))
    (hex : ∃ x : H2Open C U, F.inv U x = QZ.mk (1 / ((V : Subgroup G).relIndex U : ℚ)))
    (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V)) =
        Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom (F.groupFundamentalClass U V) := by
  have := discreteTopology_quot (U := (U : Subgroup G)) V.isOpen
  refine ⟨?_, ?_, ?_⟩
  · refine IsZero.of_iso ?_ (isoGroupCohomology _ 1).symm
    have : Subsingleton (cohomology (Rep.res (quotPreimage (U : Subgroup G) V S).subtype C) 1) :=
      ModuleCat.subsingleton_of_isZero (F.isZero_H1_open_subgroups (quotPreimageOpen hVU S))
    have : Subsingleton (cohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) :=
      (inflQuot_one_injective hVU S).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have hinj' : Function.Injective (isoGroupCohomology (Rep.res S.subtype
        ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U))) 2).hom.hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    rw [groupCohomology_map_groupFundamentalClass, ← isoGroupCohomology_hom]
    exact (addOrderOf_injective (isoGroupCohomology (Rep.res S.subtype
        ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
          ((V : Subgroup G).subgroupOf U))) 2).hom.hom.toAddMonoidHom hinj' _).trans
      (F.cyclic_res_fundamentalClass hVU S hinj hex).1
  · intro y
    obtain ⟨m, hm⟩ := (F.cyclic_res_fundamentalClass hVU S hinj hex).2
      ((isoGroupCohomology _ 2).inv.hom y)
    refine ⟨m, ?_⟩
    rw [groupCohomology_map_groupFundamentalClass, ← isoGroupCohomology_hom, ← map_zsmul,
      ← hm]
    exact (ModuleCat.hom_inv_apply (isoGroupCohomology _ 2) y).symm

end PreClassFormation

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section QuotQuot

variable {U V V' : Subgroup G} [(V.subgroupOf U).Normal] [(V'.subgroupOf U).Normal]

def quotQuotHom (h : V' ≤ V) : U ⧸ V'.subgroupOf U →* U ⧸ V.subgroupOf U :=
  QuotientGroup.map _ _ (MonoidHom.id U) fun _ hx => h hx

omit [IsTopologicalGroup G] in
theorem continuous_quotQuotHom (h : V' ≤ V) : Continuous (quotQuotHom (U := U) h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 QuotientGroup.continuous_mk

variable (C : Rep.{u} k G)

noncomputable def quotQuotRepHom (h : V' ≤ V) :
    Rep.res (quotQuotHom (U := U) h)
        ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) ⟶
      (Rep.res U.subtype C).quotientToInvariants (V'.subgroupOf U) :=
  Rep.ofHom
    { toFun := fun m => ⟨m.1, fun n => m.2 ⟨n.1, h n.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun x => by
        induction x using QuotientGroup.induction_on
        rfl }

variable [IsSmoothRep C]

noncomputable def inflQuotQuot (h : V' ≤ V) (n : ℕ) :
    cohomology ((Rep.res U.subtype C).quotientToInvariants (V.subgroupOf U)) n ⟶
      cohomology ((Rep.res U.subtype C).quotientToInvariants (V'.subgroupOf U)) n :=
  map ⟨quotQuotHom h, continuous_quotQuotHom h⟩ (quotQuotRepHom C h) n

end QuotQuot

namespace PreClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsSmoothRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G]
  {C : Rep.{u} k G} [IsSmoothRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inv_injective (W : OpenSubgroup G) : Function.Injective (F.inv W) :=
  (F.inv_bijective W).1

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem exists_inv_eq (W : OpenSubgroup G) (q : QZ) : ∃ x : H2Open C W, F.inv W x = q :=
  (F.inv_bijective W).2 q

include hVU in

theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective (F.exists_inv_eq U _) S

end ClassFormation

namespace ClassFormation.At

variable [CompactSpace G] [TotallyDisconnectedSpace G] {P : Set Nat.Primes}
  {C : Rep.{u} k G} [IsSmoothRep C] (F : ClassFormation.At P C)
  {U V : OpenSubgroup G} (hVU : V ≤ U) [((V : Subgroup G).subgroupOf U).Normal]

include F

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem exists_inv_eq_one_div (W : OpenSubgroup G) {n : ℕ} (hn : n ≠ 0)
    (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ P) :
    ∃ x : H2Open C W, F.inv W x = QZ.mk (1 / (n : ℚ)) :=
  (AddMonoidHom.mem_range).1 (QZ.mem_of_nsmul_eq_zero P (F.inv W).range
    (F.primaryComponent_le_range W) n hn hP _ (QZ.nsmul_mk_one_div n))

variable (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ (V : Subgroup G).relIndex U → p ∈ P)

include hVU hP in

theorem tate_hypotheses (S : Subgroup (U ⧸ (V : Subgroup G).subgroupOf U)) :
    IsZero (groupCohomology (Rep.res S.subtype ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants
        ((V : Subgroup G).subgroupOf U))) 1) ∧
      addOrderOf ((groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V)) = Nat.card S ∧
      ∀ y, ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 _) 2).hom
        (F.groupFundamentalClass U V) :=
  F.toPreClassFormation.tate_hypotheses hVU F.inv_injective
    (F.exists_inv_eq_one_div U (relIndex_ne_zero_of_isOpen V.isOpen _) hP) S

end ClassFormation.At

end Langlands.ProfiniteCohomology
