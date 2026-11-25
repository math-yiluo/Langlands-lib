import Langlands.Cohomology.Profinite.ClassFormation.Corestriction
import Langlands.Cohomology.Profinite.ClassFormation.TateTheorem

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits MonoidalCategory groupCohomology GroupCoh

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem subsingleton_cohomology_of_top {k : Type u} [CommRing k] (A : Rep.{u} k G) [IsSmoothRep A]
    (r : ℕ) (h : Subsingleton (cohomology (Rep.res (⊤ : Subgroup G).subtype A) r)) :
    Subsingleton (cohomology A r) := by
  let φ := map ⟨(Subgroup.topEquiv (G := G)).toMonoidHom, continuous_subtype_val⟩
    (B := Rep.res (⊤ : Subgroup G).subtype A) (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) r
  have hi : IsIso φ := isIso_map_of_mulEquiv (Subgroup.topEquiv (G := G))
    continuous_subtype_val (continuous_id.subtype_mk _) (B := Rep.res (⊤ : Subgroup G).subtype A)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) Function.bijective_id r
  exact ((ModuleCat.mono_iff_injective φ).1 inferInstance).subsingleton

theorem exists_openSubgroup_subgroupOf_eq (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    (hN : IsOpen (N : Set (U : Subgroup G))) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ (V : Subgroup G).subgroupOf U = N := by
  refine ⟨⟨N.map (U : Subgroup G).subtype, ?_⟩, Subgroup.map_subtype_le N, ?_⟩
  · exact U.isOpen.isOpenMap_subtype_val _ hN
  · exact Subgroup.comap_map_eq_self_of_injective (U : Subgroup G).subtype_injective N

section Int

variable {C : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep C] (F : ClassFormation C)

include F in

theorem ClassFormation.exists_cupH_quot (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) (n : ℕ) [NeZero n]
    (w : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) (n + 2)) :
    ∃ (a : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 2)
      (y : groupCohomology (Rep.trivial (ULift.{u} ℤ) ((U : Subgroup G) ⧸ N) (ULift.{u} ℤ)) n),
      (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
        w = groupCohomology.map (MonoidHom.id _) (ρ_ _).hom (n + 2) (cupH (add_comm 2 n) a y) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact ⟨_, exists_cupH_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses hVU S).1) (fun S => (F.tate_hypotheses hVU S).2.1)
    (fun S => (F.tate_hypotheses hVU S).2.2) n w⟩

def trivialToInvariantsHom {k H : Type u} [CommRing k] [Group H] (N : Subgroup H) [N.Normal] :
    Rep.trivial k (H ⧸ N) k ⟶ (Rep.trivial k H k).quotientToInvariants N :=
  Rep.ofHom ⟨⟨⟨fun a => ⟨a, fun _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun g => by
    induction g using QuotientGroup.induction_on
    rfl⟩

theorem rightUnitor_quotientToInvariants {k H : Type u} [CommRing k] [Group H] (A : Rep.{u} k H)
    (N : Subgroup H) [N.Normal] :
    ((𝟙 (A.quotientToInvariants N) ⊗ₘ trivialToInvariantsHom (k := k) N) ≫
        invariantsTensorHom A (Rep.trivial k H k) N ≫
        (Rep.quotientToInvariantsFunctor k N).map (ρ_ A).hom).hom.toLinearMap =
      (ρ_ (A.quotientToInvariants N)).hom.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => Subtype.ext rfl

include F in

theorem ClassFormation.subsingleton_cohomology_of_three_le (U : OpenSubgroup G) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have : NeZero n := ⟨by omega⟩
  suffices h : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) (n + 2), z = 0 from
    ⟨fun a b => by rw [h a, h b]⟩
  intro z
  set A := Rep.res (U : Subgroup G).subtype C
  set B := Rep.trivial (ULift.{u} ℤ) (U : Subgroup G) (ULift.{u} ℤ)
  obtain ⟨W, w, rfl⟩ := exists_inflation_eq A (n + 2) z
  obtain ⟨a, y, ⟨m, hm, hmy⟩, hw⟩ :=
    F.exists_cupH_quot U (W : Subgroup (U : Subgroup G)) W.isOpen n w

  change inflation A W (n + 2) w = 0
  set t := inflation B W n
    (groupCohomology.map (MonoidHom.id _)
      (A := Rep.trivial (ULift.{u} ℤ) ((U : Subgroup G) ⧸ (W : Subgroup (U : Subgroup G)))
        (ULift.{u} ℤ))
      (trivialToInvariantsHom (k := ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))) n y) with ht
  have hmt : m • t = 0 := by
    rw [ht, ← map_nsmul, ← map_nsmul, hmy, map_zero, map_zero]

  have hz : inflation A W (n + 2) w =
      coeffMap (ρ_ A).hom (n + 2) (cup (add_comm 2 n) (inflation A W 2 a) t) := by
    have key := groupCohomology.map_congr
      (f := MonoidHom.id ((U : Subgroup G) ⧸ (W : Subgroup (U : Subgroup G))))
      (g := MonoidHom.id _)
      (φ := (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))) ≫
        invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor (ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))).map
          (ρ_ A).hom)
      (ψ := (ρ_ (A.quotientToInvariants (W : Subgroup (U : Subgroup G)))).hom) rfl
      (rightUnitor_quotientToInvariants A (W : Subgroup (U : Subgroup G))) (n + 2)
    have hc := map_cupH (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))))
      (trivialToInvariantsHom (k := ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))) (add_comm 2 n)
      a y
    simp only [groupCohomology.map_id, ModuleCat.hom_id, LinearMap.id_apply] at hc
    rw [ht, cup_inflation W A B (add_comm 2 n) a,
      cohomologyMap_inflation W (A := A ⊗ B) (A' := A) (ρ_ A).hom, hw, ← hc]
    congr 1
    refine (congrArg (fun f => f.hom (cupH (add_comm 2 n) a y)) key).symm.trans ?_
    have e1 := groupCohomology.map_id_comp
      (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ULift.{u} ℤ) (W : Subgroup (U : Subgroup G)))
      (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor (ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))).map
          (ρ_ A).hom) (n + 2)
    have e2 := groupCohomology.map_id_comp
      (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)))
      ((Rep.quotientToInvariantsFunctor (ULift.{u} ℤ) (W : Subgroup (U : Subgroup G))).map
        (ρ_ A).hom) (n + 2)
    refine (congrArg (fun f => f.hom (cupH (add_comm 2 n) a y)) e1).trans ?_
    exact congrArg (fun g => (groupCohomology.map (MonoidHom.id _)
      (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
        trivialToInvariantsHom (k := ULift.{u} ℤ) (W : Subgroup (U : Subgroup G)))
        (n + 2) ≫ g).hom (cupH (add_comm 2 n) a y)) e2

  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hm (F.inv U (inflation A W 2 a))
  obtain ⟨β, rfl⟩ := (F.inv_bijective U).2 q
  have hβ : m • β = inflation A W 2 a :=
    (F.inv_bijective U).1 (by rw [map_nsmul, hq])
  rw [hz, ← hβ, map_nsmul, LinearMap.smul_apply, ← map_nsmul, hmt, map_zero, map_zero]

include F in

theorem ClassFormation.subsingleton_cohomology_top_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology C r) :=
  subsingleton_cohomology_of_top C r (F.subsingleton_cohomology_of_three_le ⊤ hr)

end Int

end Langlands.ProfiniteCohomology
