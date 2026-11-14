import Langlands.GroupScheme.SmoothIsomorphismLocus
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Dynamic comparison near a field-valued point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.LocalDynamicComparison

local instance smooth_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [Smooth H.X.hom] :
    Smooth ((baseChange b).obj H).X.hom :=
  DynamicBaseSmoothConnected.smooth_baseChange b

local instance affine_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [IsAffineHom H.X.hom] :
    IsAffineHom ((baseChange b).obj H).X.hom :=
  DynamicBaseSmoothConnected.isAffineHom_baseChange b

local instance connected_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (H : GroupScheme S) [GeometricallyConnected H.X.hom] :
    GeometricallyConnected ((baseChange b).obj H).X.hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom b))

local instance mono_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    {H G : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom] :
    Mono ((baseChange b).map i).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom))

private theorem baseChangeCocharacter_comp {S T : Scheme.{u}} (b : T ⟶ S)
    {P G : GroupScheme S} (χ : (Gm S).toGrp ⟶ P) (i : P ⟶ G) :
    Dynamic.baseChangeCocharacter b (χ ≫ i) =
      Dynamic.baseChangeCocharacter b χ ≫ (baseChange b).map i := by
  simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]

/-- A cocharacter that describes a closed fibre subgroup also describes the
given monic subgroup over some open neighbourhood of that field point. -/
theorem exists_open {S : Scheme.{u}} {P G : GroupScheme S}
    [Smooth P.X.hom] [IsAffineHom P.X.hom] [GeometricallyConnected P.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : P ⟶ G) [Mono i.hom.hom] (χ : (Gm S).toGrp ⟶ P)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)
    (hclosed : IsClosedSubgroup ((baseChange x).map i))
    (hx : (Dynamic.parabolic (Dynamic.baseChangeCocharacter x (χ ≫ i))).IsRepresentedBy
      ((baseChange x).map i)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        (Dynamic.parabolic (Dynamic.baseChangeCocharacter q (χ ≫ i))).IsRepresentedBy
          ((baseChange q).map i) := by
  obtain ⟨D, j, hjc, -, hj⟩ := (dynamicBaseRepresentability S P χ).1
  obtain ⟨Q, k, hkc, -, hk⟩ := (dynamicBaseRepresentability S G (χ ≫ i)).1
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsClosedImmersion k.hom.hom.left := hkc
  let : Mono j.hom.hom := hj.1
  let : Mono k.hom.hom := hk.1
  let : Smooth D.X.hom := ((dynamicBaseSmoothConnected S P χ D j).2.1 hj).1
  let : GeometricallyConnected D.X.hom :=
    ((dynamicBaseSmoothConnected S P χ D j).2.1 hj).2 inferInstance
  let : Smooth Q.X.hom := ((dynamicBaseSmoothConnected S G (χ ≫ i) Q k).2.1 hk).1
  let : GeometricallyConnected Q.X.hom :=
    ((dynamicBaseSmoothConnected S G (χ ≫ i) Q k).2.1 hk).2 inferInstance
  let : IsAffineHom D.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : IsAffineHom Q.X.hom := by
    rw [← Over.w k.hom.hom]
    infer_instance
  have hle : SubgroupFunctor.range (j ≫ i) ≤ Dynamic.parabolic (χ ≫ i) := by
    intro T z hz
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    have hy : y ≫ j.hom.hom ∈ (Dynamic.parabolic χ).carrier T := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    simpa only [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, Category.assoc] using
      Dynamic.parabolic_le_comap χ i T hy
  let f : D ⟶ Q := hk.liftOfLE (j ≫ i) hle
  have hfac : f ≫ k = j ≫ i := hk.liftOfLE_comp (j ≫ i) hle
  let : Mono (j ≫ i).hom.hom := by
    change Mono (j.hom.hom ≫ i.hom.hom)
    infer_instance
  let : Mono f.hom.hom :=
    mono_of_mono_fac (congrArg (fun a => a.hom.hom) hfac)
  have hself : Dynamic.parabolic (Dynamic.baseChangeCocharacter x χ) = ⊤ := by
    rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ _ hclosed]
    have hx' : (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter x χ ≫ (baseChange x).map i)).IsRepresentedBy
          ((baseChange x).map i) := by
      simpa only [baseChangeCocharacter_comp] using hx
    rw [← hx'.2]
    exact SubgroupFunctor.range_le_iff_comap_eq_top.mp le_rfl
  have hjx := hj.baseChange x
  rw [← Dynamic.parabolic_baseChange, hself] at hjx
  have hjxi : IsIso ((baseChange x).map j) := by
    rw [← hjx.topIso_hom]
    infer_instance
  have hkx := hk.baseChange x
  rw [← Dynamic.parabolic_baseChange] at hkx
  let ex := hx.isoOfIsRepresentedBy hkx
  have hex : ex.hom ≫ (baseChange x).map k = (baseChange x).map i :=
    hx.isoOfIsRepresentedBy_hom_comp hkx
  have hfx : (baseChange x).map f = (baseChange x).map j ≫ ex.hom := by
    apply hkx.hom_ext
    rw [Category.assoc, hex]
    simpa only [Functor.map_comp] using congrArg ((baseChange x).map) hfac
  have hfxi : IsIso ((baseChange x).map f) := by
    rw [hfx]
    infer_instance
  obtain ⟨V₁, q₁, hq₁, bx₁, hbx₁, hj₁⟩ :=
    SmoothIsomorphismLocus.exists_open j K x hjxi
  obtain ⟨V₂, q₂, hq₂, bx₂, hbx₂, hf₂⟩ :=
    SmoothIsomorphismLocus.exists_open f K x hfxi
  let := hq₁
  let := hq₂
  let := hj₁
  let := hf₂
  let V := pullback q₁ q₂
  let q : V ⟶ S := pullback.fst q₁ q₂ ≫ q₁
  let bx : Spec (CommRingCat.of K) ⟶ V :=
    pullback.lift bx₁ bx₂ (hbx₁.trans hbx₂.symm)
  have hbx : bx ≫ q = x := by
    simp only [bx, q, pullback.lift_fst_assoc, hbx₁]
  have hji : IsIso ((baseChange q).map j) :=
    (TorusIsomorphismLocus.isIso_comp_baseChange_iff q₁ (pullback.fst q₁ q₂) j).mpr
      inferInstance
  have hfi : IsIso ((baseChange q).map f) := by
    have hq : q = pullback.snd q₁ q₂ ≫ q₂ := pullback.condition
    rw [hq]
    exact (TorusIsomorphismLocus.isIso_comp_baseChange_iff q₂ (pullback.snd q₁ q₂) f).mpr
      inferInstance
  let e : (baseChange q).obj P ⟶ (baseChange q).obj Q :=
    inv ((baseChange q).map j) ≫ (baseChange q).map f
  have he : e ≫ (baseChange q).map k = (baseChange q).map i := by
    have h := congrArg ((baseChange q).map) hfac
    simp only [Functor.map_comp] at h
    dsimp only [e]
    rw [Category.assoc, h, IsIso.inv_hom_id_assoc]
  have hkr := hk.baseChange q
  rw [← Dynamic.parabolic_baseChange] at hkr
  refine ⟨V, q, inferInstance, bx, hbx, inferInstance, ?_⟩
  calc
    _ = SubgroupFunctor.range (e ≫ (baseChange q).map k) :=
      congrArg SubgroupFunctor.range he.symm
    _ = SubgroupFunctor.range ((baseChange q).map k) :=
      SubgroupFunctor.range_iso_comp (asIso e) _
    _ = _ := hkr.2

/-- The dynamic subgroup comparison over an arbitrary base. -/
def OpenDynamicComparisonStatement : Prop :=
  ∀ (S : Scheme.{u}) (P G : GroupScheme S)
    [Smooth P.X.hom] [IsAffineHom P.X.hom] [GeometricallyConnected P.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    (i : P ⟶ G) [Mono i.hom.hom] (χ : (Gm S).toGrp ⟶ P)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S),
    IsClosedSubgroup ((baseChange x).map i) →
    (Dynamic.parabolic (Dynamic.baseChangeCocharacter x (χ ≫ i))).IsRepresentedBy
      ((baseChange x).map i) →
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        (Dynamic.parabolic (Dynamic.baseChangeCocharacter q (χ ≫ i))).IsRepresentedBy
          ((baseChange q).map i)

/-- The comparison follows by comparing both represented dynamic subgroups. -/
theorem openDynamicComparison : OpenDynamicComparisonStatement.{u} := by
  intro S P G _ _ _ _ _ _ i _ χ K _ x hclosed hx
  exact exists_open i χ K x hclosed hx

end Langlands.GroupScheme.LocalDynamicComparison
