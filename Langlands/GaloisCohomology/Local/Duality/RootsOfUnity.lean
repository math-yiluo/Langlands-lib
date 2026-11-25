import Langlands.Cohomology.Profinite.ClassFormation.Corestriction
import Langlands.Cohomology.Profinite.Duality.DualModule
import Langlands.GaloisCohomology.Local.Finiteness

/-!
# The invariant on `H²(U, μ_n)` of a local field

For a nonarchimedean local field `K`, a separable closure `Ksep`, `n` invertible in `K` and an open
subgroup `U` of `Gal(Ksep/K)`: `μ_n ≅ ℤ/n` as groups, and the Kummer sequence identifies
`H²(U, μ_n)` with the `n`-torsion of `H²(U, Ksepˣ) ≅ ℚ/ℤ`, whence an isomorphism
`rootsOfUnityInvariant hn U : H²(U, μ_n) ≃ ℤ/n`, compatible with corestriction. These are the data
`t_U` of the duality theorem for the dualizing module `μ_n`.
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace Langlands.ProfiniteCohomology

section CoresNaturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

theorem coindMap_res_comp_coindTrace (U : OpenSubgroup G) {A B : Rep.{u} k G} (φ : A ⟶ B) :
    Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ) ≫
        coindTrace (U : Subgroup G) B =
      coindTrace (U : Subgroup G) A ≫ φ := by
  ext f
  change (coindTrace (U : Subgroup G) B).hom
      ((Rep.coindMap (U : Subgroup G).subtype
        ((Rep.resFunctor (U : Subgroup G).subtype).map φ)).hom f) =
    φ.hom ((coindTrace (U : Subgroup G) A).hom f)
  rw [coindTrace_hom_apply, coindTrace_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [coindTraceTerm_apply, coindTraceTerm_apply]
    change B.ρ x (φ.hom (f.1 x⁻¹)) = φ.hom (A.ρ x (f.1 x⁻¹))
    rw [Rep.hom_comm_apply]

/-- Corestriction is natural in the coefficients. -/
theorem cores_naturality (U : OpenSubgroup G) {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] (φ : A ⟶ B) (n : ℕ) :
    cores U A n ≫ coeffMap φ n =
      coeffMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n ≫ cores U B n := by
  rw [cores, cores, Category.assoc, ← coeffMap_comp, ← coindMap_res_comp_coindTrace, coeffMap_comp,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact shapiroMap_naturality U ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n

/-- Corestriction between open subgroups is natural in the coefficients. -/
theorem coresOfLE_naturality {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (φ : A ⟶ B) {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    coresOfLE A h n ≫ coeffMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n =
      coeffMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n ≫ coresOfLE B h n := by
  have h1 := cores_naturality (openSubgroupOf U V)
    ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n
  have h2 : coeffMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n ≫
      map (subgroupOfEquivOfLeHom (show (V : Subgroup G) ≤ U from h))
        (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from h) B) n =
      map (subgroupOfEquivOfLeHom (show (V : Subgroup G) ≤ U from h))
        (resSubgroupOfInvHom (show (V : Subgroup G) ≤ U from h) A) n ≫
      coeffMap ((Rep.resFunctor ((V : Subgroup G).subgroupOf U).subtype).map
        ((Rep.resFunctor (U : Subgroup G).subtype).map φ)) n := by
    refine (map_comp _ _ _ _ n).symm.trans (Eq.trans ?_ (map_comp _ _ _ _ n))
    apply ProfiniteCohomology.map_congr
    · exact ContinuousMonoidHom.ext fun _ => rfl
    · exact fun _ => rfl
  rw [coresOfLE_eq, coresOfLE_eq, Category.assoc, h1, ← Category.assoc, ← Category.assoc, ← h2]

theorem coresOfLE_coeffMap {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (φ : A ⟶ B) {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (x : cohomology (Rep.res (V : Subgroup G).subtype A) n) :
    (coresOfLE B h n).hom ((coeffMap ((Rep.resFunctor (V : Subgroup G).subtype).map φ) n).hom x) =
      (coeffMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n).hom
        ((coresOfLE A h n).hom x) :=
  (congrArg (fun ψ => ψ.hom x) (coresOfLE_naturality φ h n)).symm

end CoresNaturality

end Langlands.ProfiniteCohomology

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology ClassFieldTheory.Local

section RootsOfUnity

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- For `n` invertible in `K`, `μ_n(Ksep) ≅ ℤ/n` as groups. -/
theorem nonempty_addEquiv_rootsOfUnityModule {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (rootsOfUnityModule K Ksep n ≃+ ZMod n) := by
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have hn' : (n : Ksep) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero _).2 hn
  have : NeZero (n : Ksep) := ⟨hn'⟩
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  have hcard : Nat.card (rootsOfUnity n Ksep) = Nat.card (Multiplicative (ZMod n)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  exact ⟨MulEquiv.toAdditive (mulEquivOfCyclicCardEq hcard)⟩

theorem nsmul_res_rootsOfUnityModule_eq_zero {n : ℕ} (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K))
    (d : Rep.res W.subtype (rootsOfUnityModule K Ksep n)) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule (Ksep := Ksep) hn) d

omit [IsSepClosure K Ksep] in
theorem kummerSequenceRes_g_hom_apply (n : ℕ) (W : Subgroup Gal(Ksep/K))
    (x : Rep.res W.subtype (unitsModule K Ksep)) :
    (kummerSequenceRes (K := K) (Ksep := Ksep) n W).g.hom x = n • x :=
  nsmul_id_hom_apply (unitsModule K Ksep) n x

end RootsOfUnity

namespace Local

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type u} [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem injective_coeffMap_kummerSequenceRes_f_two (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective
      (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom :=
  cohomologyMap_f_injective_of_subsingleton (kummerSequenceRes_shortExact n _ hn) 1
    (subsingleton_cohomology_one_res_unitsModule K Ksep U)

variable (n) in
/-- The invariant of `H²(U, μ_n)`: the image in `H²(U, Ksepˣ)` followed by the invariant of the
class formation. -/
def rootsOfUnityInv (U : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 2 →+ QZ :=
  ((classFormation K Ksep).inv U).comp
    (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom.toAddMonoidHom

theorem rootsOfUnityInv_apply (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 2) :
    rootsOfUnityInv n U x = (classFormation K Ksep).inv U
      ((coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))).f 2).hom
        x) :=
  rfl

theorem rootsOfUnityInv_injective (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective (rootsOfUnityInv (Ksep := Ksep) n U) :=
  ((classFormation K Ksep).inv_bijective U).1.comp (injective_coeffMap_kummerSequenceRes_f_two hn U)

theorem range_rootsOfUnityInv (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    (rootsOfUnityInv (Ksep := Ksep) n U).range = (zmodToQZ n).range := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set F := classFormation K Ksep
  set S := kummerSequenceRes (K := K) (Ksep := Ksep) n (U : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSequenceRes_shortExact n _ hn
  ext q
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine exists_zmodToQZ_eq ?_
    have h0 : n • (coeffMap S.f 2).hom x = 0 := by
      rw [← cohomologyMap_kummerSequenceRes_g_apply n (U : Subgroup Gal(Ksep/K)) 2]
      exact cohomologyMap_g_cohomologyMap_f_apply (S := S) 2 x
    calc n • rootsOfUnityInv n U x = F.inv U (n • (coeffMap S.f 2).hom x) :=
          (map_nsmul (F.inv U) n ((coeffMap S.f 2).hom x)).symm
      _ = 0 := by rw [h0]; exact (F.inv U).map_zero
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := (F.inv_bijective U).2 (zmodToQZ n a)
    have hny : n • y = 0 := by
      apply (F.inv_bijective U).1
      rw [map_nsmul, hy, ← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self,
        zero_smul, map_zero, map_zero]
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSequenceRes_g_apply n _ 2 y).trans hny)
    exact ⟨x, show F.inv U ((coeffMap S.f 2).hom x) = _ by rw [hx, hy]⟩

/-- The invariant `H²(U, μ_n) ≃+ ℤ/n` for an open subgroup `U` and `n` invertible in `K`. -/
def rootsOfUnityInvariant (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 2 ≃+
      ZMod n :=
  haveI : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  (AddMonoidHom.ofInjective (rootsOfUnityInv_injective hn U)).trans
    ((AddEquiv.addSubgroupCongr (range_rootsOfUnityInv hn U)).trans
      (AddMonoidHom.ofInjective (zmodToQZ_injective (n := n))).symm)

theorem zmodToQZ_rootsOfUnityInvariant (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 2) :
    zmodToQZ n (rootsOfUnityInvariant hn U x) = rootsOfUnityInv n U x := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  set w := AddEquiv.addSubgroupCongr (range_rootsOfUnityInv hn U)
    (AddMonoidHom.ofInjective (rootsOfUnityInv_injective hn U) x) with hw
  have h1 : (w : QZ) = rootsOfUnityInv n U x :=
    AddMonoidHom.ofInjective_apply (rootsOfUnityInv_injective hn U) (x := x)
  have h2 := AddMonoidHom.ofInjective_apply (zmodToQZ_injective (n := n))
    (x := (AddMonoidHom.ofInjective (zmodToQZ_injective (n := n))).symm w)
  rw [AddEquiv.apply_symm_apply] at h2
  exact h2.symm.trans h1

/-- The invariants of `H²(·, μ_n)` are compatible with corestriction. -/
theorem rootsOfUnityInvariant_coresOfLE (hn : (n : K) ≠ 0) (U V : OpenSubgroup Gal(Ksep/K))
    (h : V ≤ U)
    (x : cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 2) :
    rootsOfUnityInvariant hn U (coresOfLE (rootsOfUnityModule K Ksep n) h 2 x) =
      rootsOfUnityInvariant hn V x := by
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  apply zmodToQZ_injective
  rw [zmodToQZ_rootsOfUnityInvariant, zmodToQZ_rootsOfUnityInvariant]
  exact (congrArg ((classFormation K Ksep).inv U)
      (coresOfLE_coeffMap (kummerSequence K Ksep n).f h 2 x).symm).trans
    (ClassFormation.inv_coresOfLE _ h _)

end Local

end Langlands.GaloisCohomology
