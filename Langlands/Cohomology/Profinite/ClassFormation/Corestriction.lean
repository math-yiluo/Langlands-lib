import Langlands.Cohomology.Profinite.ClassFormation.FundamentalClass
import Langlands.Cohomology.Profinite.Corestriction

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section SubgroupOf

variable {U V : Subgroup G} (h : V ≤ U) (A : Rep.{u} k G)

def resSubgroupOfInvHom :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (Rep.res V.subtype A) ⟶
      Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [IsSmoothRep A]

@[reassoc]
theorem map_resSubgroupOfHom_comp (n : ℕ) :
    map (subgroupOfEquivOfLeSymmHom h) (resSubgroupOfHom h A) n ≫
      map (subgroupOfEquivOfLeHom h) (resSubgroupOfInvHom h A) n = 𝟙 _ := by
  rw [← map_comp]
  exact map_eq_id _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

abbrev openSubgroupOf (U V : OpenSubgroup G) : OpenSubgroup (U : Subgroup G) where
  toSubgroup := (V : Subgroup G).subgroupOf U
  isOpen' := V.isOpen.preimage continuous_subtype_val

variable [CompactSpace G] (C : Rep.{u} k G) [IsSmoothRep C]

noncomputable def coresOfLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res (V : Subgroup G).subtype C) n ⟶
      cohomology (Rep.res (U : Subgroup G).subtype C) n :=
  map (subgroupOfEquivOfLeHom (show (V : Subgroup G) ≤ U from h)) (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from h) C) n ≫
    cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem coresOfLE_eq {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    coresOfLE C h n =
      map (subgroupOfEquivOfLeHom (show (V : Subgroup G) ≤ U from h)) (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from h) C) n ≫
        cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n :=
  rfl

theorem resOfLE_comp_coresOfLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    resOfLE C (show (V : Subgroup G) ≤ U from h) n ≫ coresOfLE C h n =
      (V : Subgroup G).relIndex U • 𝟙 _ := by
  rw [resOfLE_eq_res_comp, coresOfLE, Category.assoc,
    map_resSubgroupOfHom_comp_assoc]
  exact res_comp_cores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem coresOfLE_resOfLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype C) n) :
    (coresOfLE C h n).hom ((resOfLE C (show (V : Subgroup G) ≤ U from h) n).hom x) =
      (V : Subgroup G).relIndex U • x := by
  have := congrArg (fun φ => φ.hom x) (resOfLE_comp_coresOfLE C h n)
  simpa using this

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace QZ

theorem exists_nsmul_eq {n : ℕ} (hn : n ≠ 0) (x : QZ) : ∃ y : QZ, n • y = x := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (toAddCircle x)
  refine ⟨mk (r / n), ?_⟩
  rw [← mk_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hn)]
  change toAddCircle.symm (r : AddCircle (1 : ℚ)) = x
  rw [show ((r : AddCircle (1 : ℚ))) = toAddCircle x from hr]
  exact toAddCircle.symm_apply_apply x

end QZ

namespace PreClassFormation

variable [CompactSpace G] {C : Rep.{u} k G} [IsSmoothRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U)

theorem inv_coresOfLE_resOfLE (x : H2Open C U) :
    F.inv U ((coresOfLE C hVU 2).hom
        ((resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x)) =
      F.inv V ((resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x) := by
  rw [coresOfLE_resOfLE, map_nsmul, F.inv_res U V hVU x]

omit [CompactSpace G] in

theorem resOfLE_eq_of_inv (hVinj : Function.Injective (F.inv V)) {x : H2Open C V}
    {y : H2Open C U} (hy : (V : Subgroup G).relIndex U • F.inv U y = F.inv V x) :
    (resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom y = x :=
  hVinj (by rw [F.inv_res U V hVU y, hy])

theorem inv_coresOfLE_of (hVinj : Function.Injective (F.inv V)) {x : H2Open C V}
    (hx : ∃ y : H2Open C U, (V : Subgroup G).relIndex U • F.inv U y = F.inv V x) :
    F.inv U ((coresOfLE C hVU 2).hom x) = F.inv V x := by
  obtain ⟨y, hy⟩ := hx
  rw [← F.resOfLE_eq_of_inv hVU hVinj hy]
  exact F.inv_coresOfLE_resOfLE hVU y

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] {C : Rep.{u} k G} [IsSmoothRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U)

include F in

theorem resOfLE_surjective :
    Function.Surjective (resOfLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom := by
  intro x
  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq (relIndex_ne_zero_of_isOpen V.isOpen (U : Subgroup G))
    (F.inv V x)
  obtain ⟨y, rfl⟩ := F.exists_inv_eq U q
  exact ⟨y, F.toPreClassFormation.resOfLE_eq_of_inv hVU (F.inv_injective V) hq⟩

theorem inv_coresOfLE (x : H2Open C V) :
    F.inv U ((coresOfLE C hVU 2).hom x) = F.inv V x := by
  obtain ⟨y, rfl⟩ := F.resOfLE_surjective hVU x
  exact F.toPreClassFormation.inv_coresOfLE_resOfLE hVU y

end ClassFormation

section Quot

variable {U V : Subgroup G} [(V.subgroupOf U).Normal]

abbrev quotOpenSubgroup (hV : IsOpen (V : Set G)) (S : Subgroup (U ⧸ V.subgroupOf U)) :
    OpenSubgroup (U ⧸ V.subgroupOf U) where
  toSubgroup := S
  isOpen' := @isOpen_discrete _ _ (discreteTopology_quot hV) _

instance compactSpace_quotientGroup {H : Type*} [Group H] [TopologicalSpace H] [CompactSpace H]
    (N : Subgroup H) : CompactSpace (H ⧸ N) :=
  Quotient.compactSpace

end Quot

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G] {C : Rep.{u} k G} [IsSmoothRep C]
  (F : ClassFormation C) {U V : OpenSubgroup G} (hVU : V ≤ U)
  [((V : Subgroup G).subgroupOf U).Normal]

end ClassFormation

namespace ClassFormation.At

variable [CompactSpace G] {P : Set Nat.Primes} {C : Rep.{u} k G} [IsSmoothRep C]
  (F : ClassFormation.At P C) {U V : OpenSubgroup G} (hVU : V ≤ U)

theorem inv_coresOfLE
    (hP : ∀ p : Nat.Primes, (p : ℕ) ∣ (V : Subgroup G).relIndex U → p ∈ P) (x : H2Open C V)
    {n : ℕ} (hn : n ≠ 0) (hnP : ∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ P) (hx : n • F.inv V x = 0) :
    F.inv U ((coresOfLE C hVU 2).hom x) = F.inv V x := by
  have hi : (V : Subgroup G).relIndex U ≠ 0 := relIndex_ne_zero_of_isOpen V.isOpen _
  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hi (F.inv V x)
  have hmem : q ∈ (F.inv U).range := by
    refine QZ.mem_of_nsmul_eq_zero P (F.inv U).range (F.primaryComponent_le_range U)
      (n * (V : Subgroup G).relIndex U) (Nat.mul_ne_zero hn hi) (fun p hp => ?_) q ?_
    · rcases (Nat.Prime.dvd_mul p.2).1 hp with h | h
      · exact hnP p h
      · exact hP p h
    · rw [mul_smul, hq, hx]
  obtain ⟨y, rfl⟩ := (AddMonoidHom.mem_range).1 hmem
  exact F.toPreClassFormation.inv_coresOfLE_of hVU (F.inv_injective V) ⟨y, hq⟩

end ClassFormation.At

end Langlands.ProfiniteCohomology
