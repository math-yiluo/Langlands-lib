import Langlands.AlgebraicGeometry.Descent.FpqcClosedLocusDescent
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement
import Langlands.GroupScheme.HomScheme.AdmissibleSheaf
import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Torus.RelativeTorusFpqcDescent

/-! # Fpqc descent of actual closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Closed subgroup representatives descend from a matching family on an fpqc cover. -/
theorem isClosedRepresentable_subgroup_fpqc
    (𝒰 : Scheme.Cover.{u} Scheme.fpqcPrecoverage S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (hF : IsMatching 𝒰 F) (hc : ∀ i, (F i).IsClosedRepresentable) :
    (subgroup 𝒰 F).IsClosedRepresentable := by
  let 𝒱 := 𝒰.pullback₁ G.X.hom
  let E := (subgroup 𝒰 F).membershipSieve
  have hE := isClosed_membershipSieve_subgroup_of_subcanonical 𝒰 F Scheme.fpqcTopology hc
  have hlocal (i : 𝒰.I₀) :
      ∃ (Z : Scheme.{u}) (j : Z ⟶ 𝒱.X i), IsClosedImmersion j ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ 𝒱.X i),
          (∃ c : T ⟶ Z, c ≫ j = g) ↔ E (g ≫ 𝒱.f i) := by
    obtain ⟨L, k, hk, hclosed⟩ := hc i
    refine ⟨L.X.left, k.hom.hom.left, hclosed, fun T g => ?_⟩
    change _ ↔ (subgroup 𝒰 F).schemeCondition (g ≫ pullback.fst G.X.hom (𝒰.f i))
    rw [schemeCondition_baseChange_iff, baseChange_subgroup 𝒰 F hF i]
    exact ((F i).schemeCondition_iff_exists_of_isRepresentedBy hk g).symm
  have hcover : Sieve.generate 𝒱.presieve₀ ∈ Scheme.fpqcTopology G.X.left :=
    Precoverage.generate_mem_toGrothendieck 𝒱.mem₀
  obtain ⟨Z, j, hj, hfac⟩ := Langlands.AlgebraicGeometry.fpqcClosedLocusDescent G.X.left E hE
    ⟨Sieve.generate 𝒱.presieve₀, hcover, by
      rintro Y' f ⟨_, m, _, ⟨i⟩, hm⟩
      obtain ⟨Z, j, hj, hZ⟩ := hlocal i
      let : IsClosedImmersion j := hj
      obtain ⟨W, k, hk, hW⟩ := exists_closedRepresentative_pullback
        (E.pullback (𝒱.f i)) j hZ m
      refine ⟨W, k, hk, fun T g => ?_⟩
      rw [hW g]
      change E ((g ≫ m) ≫ 𝒱.f i) ↔ E (g ≫ f)
      rw [Category.assoc, hm]⟩
  let : IsClosedImmersion j := hj
  exact (subgroup 𝒰 F).isClosedRepresentable_of_schemeCondition j
    (fun T g => (hfac g).symm)

end Langlands.GroupScheme.SubgroupFunctor.CoverDescent

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {T M : Over S}

/-- The closed torus-subgroup presheaf satisfies the singleton fpqc sheaf
condition in Murre's representability criterion. -/
def AdmissibleFpqcSheafStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), FaithfullyFlatSheaf (smallAdmissiblePresheaf G)

private theorem eq_of_restrict_eq_fpqc (a : M ⟶ T)
    [Flat a.left] [Surjective a.left] [QuasiCompact a.left]
    (F F' : AdmissibleSubgroup ((baseChange T.hom).obj G))
    (h : restrict a F = restrict a F') : F = F' := by
  let e := Descent.pullbackComparison T.hom a.left M.hom (Over.w a) G
  have h' := congrArg (fun ξ : AdmissibleSubgroup _ => ξ.val.comap e.hom) h
  simp only [restrict_val_eq, ← comap_comp, Iso.hom_inv_id, comap_id, e] at h'
  apply Subtype.ext
  exact eq_of_isRepresentedBy_baseChange_eq a.left
    (admissibleRepresentative F).represents (admissibleRepresentative F').represents h'

set_option maxHeartbeats 800000 in
private theorem exists_restrict_eq_fpqc (a : M ⟶ T)
    [Flat a.left] [Surjective a.left] [QuasiCompact a.left]
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G))
    (h : ∀ {A : Over S} (b c : A ⟶ M), b ≫ a = c ≫ a → restrict b F = restrict c F) :
    ∃ F₀ : AdmissibleSubgroup ((baseChange T.hom).obj G), restrict a F₀ = F := by
  let H := (baseChange T.hom).obj G
  let e := Descent.pullbackComparison T.hom a.left M.hom (Over.w a) G
  let F' : AdmissibleSubgroup ((baseChange a.left).obj H) :=
    ⟨F.val.comap e.hom, isAdmissible_comapIso F e⟩
  let 𝒰 : Scheme.Cover.{u} Scheme.fpqcPrecoverage T.left :=
    (a.left.cover (P := @Flat) inferInstance).ofQuasiCompactCover
  let L : ∀ i, SubgroupFunctor ((baseChange (𝒰.f i)).obj H) := fun _ => F'.val
  have hL : CoverDescent.IsMatching 𝒰 L := by
    intro i j V W d x hx
    let v := (baseChangePointsEquiv a.left H V).symm
      (d ≫ baseChangePointsEquiv a.left H W x)
    let xv := v ≫ e.hom.hom.hom
    let xw := x ≫ e.hom.hom.hom
    have hxw : xw ∈ F.val.carrier W := hx
    let A : Over S := Over.mk (V.hom ≫ M.hom)
    let b : A ⟶ M := Over.homMk V.hom rfl
    have hbase : (d.left ≫ W.hom) ≫ a.left = V.hom ≫ a.left := by
      have hd : d.left ≫ (W.hom ≫ a.left) = V.hom ≫ a.left := Over.w d
      simpa only [Category.assoc] using hd
    let c : A ⟶ M := Over.homMk (d.left ≫ W.hom) (by
      change (d.left ≫ W.hom) ≫ M.hom = V.hom ≫ M.hom
      rw [← Over.w a, ← Category.assoc, ← Category.assoc, hbase])
    have hbc : b ≫ a = c ≫ a := Over.OverMorphism.ext hbase.symm
    let dw : Over.mk c.left ⟶ W := Over.homMk d.left rfl
    have hp : xv.left ≫ pullback.fst G.X.hom M.hom =
        (dw ≫ xw).left ≫ pullback.fst G.X.hom M.hom := by
      have hv := congrArg (fun z => z.left ≫ pullback.fst G.X.hom T.hom)
        ((baseChangePointsEquiv a.left H V).apply_symm_apply
          (d ≫ baseChangePointsEquiv a.left H W x))
      simpa only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
        H, v, xv, xw, e, dw, Over.homMk_left, Descent.pullbackComparison_hom_fst,
        Descent.pullbackComparison_hom_fst_assoc] using hv
    change xv ∈ F.val.carrier V
    exact mem_of_restrict_eq b c F F (h b c hbc) xv (dw ≫ xw) hp (F.val.comp_mem dw hxw)
  let F₀ := CoverDescent.subgroup 𝒰 L
  have hB : F₀.baseChange a.left = F'.val :=
    CoverDescent.baseChange_subgroup 𝒰 L hL PUnit.unit
  have hC : F₀.IsClosedRepresentable :=
    CoverDescent.isClosedRepresentable_subgroup_fpqc 𝒰 L hL fun i => by
      obtain ⟨K, j, hj, _, hrep⟩ := F'.property
      exact ⟨K, j, hrep, hj⟩
  obtain ⟨K, j, hj, hc⟩ := hC
  let r := admissibleRepresentative F'
  have hrep := hj.baseChange a.left
  rw [hB] at hrep
  have hK : RelativeTorus.IsTorus K := RelativeTorus.IsTorus.of_fpqc_baseChange a.left
    (RelativeTorus.IsTorus.of_iso (hrep.isoOfIsRepresentedBy r.represents) r.torus)
  refine ⟨⟨F₀, K, j, hc, hK, hj⟩, ?_⟩
  apply Subtype.ext
  rw [restrict_val_eq]
  change (F₀.baseChange a.left).comap e.inv = F.val
  rw [hB]
  change (F.val.comap e.hom).comap e.inv = F.val
  rw [← comap_comp, Iso.inv_hom_id, comap_id]

/-- Effective fpqc descent and uniqueness for the actual closed torus-subgroup presheaf. -/
theorem smallAdmissiblePresheaf_faithfullyFlatSheaf : AdmissibleFpqcSheafStatement.{u} := by
  intro S G M T a hflat hsurj hqc
  let := hflat
  let := hsurj
  let := hqc
  apply Presieve.isSheafFor_singleton.mpr
  intro x hx
  let F := smallAdmissibleEquiv G M x
  obtain ⟨F₀, hF₀⟩ := exists_restrict_eq_fpqc a F (fun {_} b c hbc => by
    have hh := congrArg (smallAdmissibleEquiv G _) (hx b c hbc)
    simpa only [smallAdmissibleEquiv_map] using hh)
  refine ⟨(smallAdmissibleEquiv G T).symm F₀, ?_, ?_⟩
  · apply (smallAdmissibleEquiv G M).injective
    rw [smallAdmissibleEquiv_map, Equiv.apply_symm_apply]
    exact hF₀
  · intro y hy
    apply (smallAdmissibleEquiv G T).injective
    rw [Equiv.apply_symm_apply]
    apply eq_of_restrict_eq_fpqc a
    rw [← smallAdmissibleEquiv_map, hy, hF₀]

end Langlands.GroupScheme.TorusSubgroupModuli
