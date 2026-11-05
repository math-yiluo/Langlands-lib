import Langlands.GroupScheme.Adjoint.CenterQuotientCore
import Langlands.GroupScheme.ReducedSubgroupAction
import Langlands.GroupScheme.Absolute.NoCocharacterUnipotent
import Langlands.GroupScheme.Unipotent.TorusHom
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.KernelCoreQuotientDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Central isogenies preserve connected reductivity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteCentralQuotient

variable {K : Type u} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- A smooth connected group over a field whose identity point is open is trivial. -/
theorem id_eq_one_of_isOpen_identityPoint {U : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsOpen ({IdentityComponent.identityPoint U} : Set U.X.left)) :
    𝟙 U.X = (1 : U.X ⟶ U.X) := by
  have hs : η[U.X].left ≫ U.X.hom = 𝟙 _ := η[U.X].w
  have : IsClosedImmersion η[U.X].left := isClosedImmersion_of_comp_eq_id U.X.hom _ hs
  have hr : Set.range η[U.X].left = {IdentityComponent.identityPoint U} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact IdentityComponent.unit_left_apply U x
    · rintro rfl
      exact ⟨_, rfl⟩
  have hrange : Set.range η[U.X].left = Set.univ := by
    refine (show IsClopen (Set.range η[U.X].left) from
      ⟨η[U.X].left.isClosedEmbedding.isClosed_range, hr ▸ hU⟩).eq_univ ?_
    rw [hr]
    exact Set.singleton_nonempty _
  have : Surjective η[U.X].left := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K _ U.X.hom
  have : IsIso η[U.X].left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso U.X.hom := by
    have : IsIso (η[U.X].left ≫ U.X.hom) := by rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left η[U.X].left U.X.hom
  apply Over.OverMorphism.ext
  apply (cancel_mono U.X.hom).mp
  exact (Over.w (𝟙 U.X)).trans (Over.w (1 : U.X ⟶ U.X)).symm

/-- **The geometric core.** Over an algebraically closed field, let `q : G ⟶ Q` be a flat
homomorphism, locally of finite presentation, from a smooth affine group with trivial
unipotent radical to an affine group, whose actual kernel is killed by a fixed positive
power. Then `Q` has trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_of_kernel_pow_eq_one
    {G Q : GroupScheme (Spec (CommRingCat.of K))} (q : G ⟶ Q)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Flat q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hG : HasTrivialUnipotentRadical G) {n : ℕ} (hn : 0 < n)
    (hker : ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (kernel q).X), x ^ n = 1) :
    HasTrivialUnipotentRadical Q := by
  intro U j hj hUs hUc hUu hUn
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  -- The inverse image `A` of `U` in `G`, a normal closed subgroup.
  have ha : IsClosedSubgroup (SubgroupPreimage.inclusion q j) :=
    SubgroupPreimage.isClosedSubgroup q j hj
  have han : (SubgroupFunctor.range (SubgroupPreimage.inclusion q j)).IsNormal :=
    SubgroupPreimage.isNormal q j hUn
  have : IsClosedImmersion (SubgroupPreimage.inclusion q j).hom.hom.left := ha
  have : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme q j).X.hom := by
    rw [← Over.w (SubgroupPreimage.inclusion q j).hom.hom]
    infer_instance
  -- Its reduced identity component `H`, a smooth connected normal closed subgroup of `G`.
  have hHn : (SubgroupFunctor.range (ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j)).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp _ ha han
  have : IsClosedImmersion (ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j).hom.hom.left := by
    change IsClosedImmersion ((ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j)).hom.hom.left ≫
        (SubgroupPreimage.inclusion q j).hom.hom.left)
    infer_instance
  have hHc : IsClosedSubgroup (ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j) :=
    inferInstanceAs (IsClosedImmersion _)
  have : Mono (ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j).hom.hom :=
    Over.mono_of_mono_left _
  -- Every cocharacter of `H` maps trivially to `U`, so it lands in the kernel; the kernel is
  -- killed by `n`, and multiplication by `n` on `Gm` is an epimorphism.
  have hcochar : ∀ z : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      ReducedSubgroup.identityCore (SubgroupPreimage.groupScheme q j), z = 0 := by
    intro z
    have hz0 : z ≫ ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
        SubgroupPreimage.projection q j = 0 :=
      (isSplitTorus_gm (S := Spec (CommRingCat.of K))).isTorus.hom_eq_zero_of_isUnipotent
        hUu _
    have hx : (z ≫ ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
        SubgroupPreimage.inclusion q j).hom.hom ≫ q.hom.hom = 1 := by
      have h := congrArg (fun f => f.hom.hom ≫ j.hom.hom) hz0
      simp only [Grp.comp_hom_hom, Category.assoc] at h ⊢
      rw [(SubgroupPreimage.isPullback q j).w, h]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff q _).mpr hx)
    let m := multiplication (Gm (Spec (CommRingCat.of K))).toGrp (n : ℤ)
    obtain ⟨hmf, hms⟩ := (isSplitTorus_gm (S := Spec (CommRingCat.of K))).flat_and_surjective_multiplication
      (n := (n : ℤ)) (by omega)
    have : Flat m.hom.hom.left := hmf
    have : Surjective m.hom.hom.left := hms
    have : Epi m.hom.hom.left := Flat.epi_of_flat_of_surjective _
    have : Epi m.hom.hom := Over.epi_of_epi_left _
    have hm : m.hom.hom ≫ (z ≫ ReducedSubgroup.identityCoreι
        (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j).hom.hom = 1 := by
      rw [multiplication_hom, GrpObj.zpow_comp, Category.id_comp, ← hy, zpow_natCast,
        ← MonObj.pow_comp, hker, MonObj.one_comp]
    have hx1 : (z ≫ ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
        SubgroupPreimage.inclusion q j).hom.hom = 1 := by
      apply (cancel_epi m.hom.hom).mp
      rw [hm, MonObj.comp_one]
    apply Grp.hom_ext
    apply (cancel_mono (ReducedSubgroup.identityCoreι
      (SubgroupPreimage.groupScheme q j) ≫ SubgroupPreimage.inclusion q j).hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, zero_comp, hx1]
    rfl
  -- Hence `H` is unipotent, and so trivial.
  have hHu : IsUnipotent (ReducedSubgroup.identityCore (SubgroupPreimage.groupScheme q j)) :=
    AbsoluteNoCocharacter.isUnipotent hcochar
  have hbot := hG _ _ hHc inferInstance inferInstance hHu hHn
  -- So `H` maps trivially to `U`. As `H` is open in `A` and the projection `A ⟶ U` is an open
  -- map, the identity point of `U` is open.
  have hι1 : (ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
      SubgroupPreimage.inclusion q j).hom.hom = 1 := by
    have hmem : (ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
        SubgroupPreimage.inclusion q j).hom.hom ∈ (SubgroupFunctor.range
          (ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
            SubgroupPreimage.inclusion q j)).carrier _ :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
    exact hmem
  have hφ : ReducedSubgroup.identityCoreι (SubgroupPreimage.groupScheme q j) ≫
      SubgroupPreimage.projection q j = 0 := by
    apply Grp.hom_ext
    change _ = (1 : _ ⟶ U.X)
    apply (cancel_mono j.hom.hom).mp
    rw [MonObj.one_comp, Grp.comp_hom_hom, Category.assoc, ← (SubgroupPreimage.isPullback q j).w,
      ← Category.assoc, ← Grp.comp_hom_hom, hι1, MonObj.one_comp]
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  have : LocallyOfFinitePresentation (SubgroupPreimage.projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j) inferInstance
  have hopen := (SubgroupPreimage.projection q j).hom.hom.left.isOpenMap _
    (ReducedSubgroup.isOpen_range_identityCoreι (SubgroupPreimage.groupScheme q j))
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← Over.comp_left,
    ← Grp.comp_hom_hom, hφ, range_zero_hom] at hopen
  -- A connected smooth group with open identity point is trivial.
  have : Smooth U.X.hom := hUs
  have : ConnectedSpace U.X.left := hUc
  exact CenterQuotient.range_eq_bot_of_id_eq_one j (id_eq_one_of_isOpen_identityPoint hopen)

end FiniteCentralQuotient

/-- **Central isogenies preserve connected reductivity.** If `q : G ⟶ Q` is a central isogeny
of affine groups over a field `k` and `G` is connected reductive, then so is `Q`. -/
theorem isConnectedReductive_of_isCentralIsogeny {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q) (hG : IsConnectedReductive G)
    [IsAffineHom Q.X.hom] (hq : IsCentralIsogeny q) : IsConnectedReductive Q := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Flat q.hom.hom.left := hq.flat
  have : Surjective q.hom.hom.left := hq.surjective
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  let b := toAlgebraicClosure k
  have hGa : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have hGs : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hQa : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  have hqb := hq.baseChange b
  have : Flat ((GroupScheme.baseChange b).map q).hom.hom.left := hqb.flat
  have : LocallyOfFinitePresentation ((GroupScheme.baseChange b).map q).hom.hom.left :=
    hqb.locallyOfFinitePresentation
  obtain ⟨n, hn, hker⟩ := hqb.exists_pow_eq_one_kernel
  exact
    { smooth := smooth_target_of_surjective_flat_hom q
      isAffineHom := inferInstance
      connectedSpace := hq.surjective.surj.connectedSpace q.hom.hom.left.continuous
      hasTrivialGeometricUnipotentRadical :=
        FiniteCentralQuotient.hasTrivialUnipotentRadical_of_kernel_pow_eq_one
          ((GroupScheme.baseChange b).map q) hG.hasTrivialGeometricUnipotentRadical hn hker }

end Langlands.GroupScheme
