import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalStatement
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # Dynamic rigidity for relative unipotent radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeLevi

variable {S : Scheme.{u}} {P N U : GroupScheme S}

/-- Identity-limit subgroups of automorphic Gm-actions on smooth affine groups
are smooth over an arbitrary base. -/
theorem smooth_of_action_unipotent
    [IsAffineHom N.X.hom] [Smooth N.X.hom]
    (a : AutomorphicAction (Gm S).toGrp N) {K : GroupScheme S} {j : K ⟶ N}
    (hj : a.unipotent.IsRepresentedBy j) : Smooth K.X.hom := by
  let : IsAffineHom (Gm S).X.hom := isSplitTorus_gm.isAffineHom
  let : Smooth (Gm S).X.hom := smooth_gm S
  obtain ⟨V, v, hvc, hvfp, hv⟩ :=
    (dynamicBaseRepresentability S a.semidirectProduct a.semidirectInr).2.1
  have hv' : a.unipotent.IsRepresentedBy
      (a.semidirectUnipotentLift (𝟙 _) (by simpa using hv)) := by
    simpa only [AutomorphicAction.restrict_id] using
      a.isRepresentedBy_semidirectUnipotentLift (𝟙 _) (by simpa using hv)
  have hVs : Smooth V.X.hom :=
    ((dynamicBaseSmoothConnected S a.semidirectProduct a.semidirectInr V v).1 hv).1
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (hj.isoOfIsRepresentedBy hv')) hVs

/-- Normalized conjugation is equivariant for ambient conjugation. -/
theorem normalized_isEquivariant (n : N ⟶ P) (χ : (Gm S).toGrp ⟶ P)
    [Mono n.hom.hom]
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ)) :
    (AutomorphicAction.ofNormalizedConjugation n χ hn).IsEquivariant
      (AutomorphicAction.cocharacterAction χ) n := by
  intro T t x
  rw [AutomorphicAction.cocharacterAction_act]
  exact SubgroupFunctor.lift_comp_normalizedConjugation_comp n χ hn t x

/-- The intersection with the dynamic subgroup represents the identity-limit
subgroup of the induced action on a normalized closed subgroup. -/
theorem intersection_represents_action_unipotent
    (n : N ⟶ P) (r : U ⟶ P) (χ : (Gm S).toGrp ⟶ P)
    (hnc : IsClosedSubgroup n) (hrc : IsClosedSubgroup r)
    (hr : (Dynamic.unipotent χ).IsRepresentedBy r)
    (hn : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ)) :
    let _ : IsClosedImmersion n.hom.hom.left := hnc
    let _ : Mono n.hom.hom := Over.mono_of_mono_left n.hom.hom
    (AutomorphicAction.ofNormalizedConjugation n χ hn).unipotent.IsRepresentedBy
      (subgroupIntersectionFst n r) := by
  let : IsClosedImmersion n.hom.hom.left := hnc
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  have hfc : IsClosedSubgroup (subgroupIntersectionFst n r) :=
    isClosedSubgroup_subgroupIntersectionFst n hrc
  let : IsClosedImmersion (subgroupIntersectionFst n r).hom.hom.left := hfc
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  rw [AutomorphicAction.IsEquivariant.unipotent_eq_comap_of_isClosedSubgroup
      (normalized_isEquivariant n χ hn) hnc,
    AutomorphicAction.cocharacterAction_unipotent]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, ← hr.2,
    SubgroupFunctor.mem_range]
  let hp := subgroupIntersection_isPullback n r
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (subgroupIntersectionSnd n r).hom.hom, ?_⟩
    rw [Category.assoc, ← hp.w, ← Category.assoc]
  · rintro ⟨y, hy⟩
    exact ⟨hp.lift x y hy.symm, hp.lift_fst _ _ _⟩

/-- A morphism of flat, locally finitely presented group schemes is an
isomorphism if it is so on every geometric fibre and the target is locally
of finite type over the base. -/
theorem isIso_of_geometricFibres {X Y : GroupScheme S} (f : X ⟶ Y)
    [Flat X.X.hom] [LocallyOfFinitePresentation X.X.hom]
    [LocallyOfFiniteType Y.X.hom]
    (hf : ∀ s : S, IsIso (geometricFiberHom f s)) : IsIso f := by
  have hres (s : S) : IsIso (residueFiberHom f s) := by
    let a := S.fromSpecResidueField s
    let b := toAlgebraicClosure (S.residueField s)
    have hb := fieldExtension_fpqc (S.residueField s)
      (AlgebraicClosure (S.residueField s))
    let : Surjective b := hb.1
    let : Flat b := hb.2.1
    let : QuasiCompact b := hb.2.2
    have : IsIso ((GroupScheme.baseChange (b ≫ a)).map f) := hf s
    have hnat :
        (GroupScheme.baseChange (b ≫ a)).map f ≫ (baseChangeCompIso a b Y).hom =
          (baseChangeCompIso a b X).hom ≫
            (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f) :=
      ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
        Functor.mapGrpCompIso).hom.naturality f
    have hfactor :
        (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f) =
          (baseChangeCompIso a b X).inv ≫
            (GroupScheme.baseChange (b ≫ a)).map f ≫
              (baseChangeCompIso a b Y).hom := by
      rw [hnat, Iso.inv_hom_id_assoc]
    have : IsIso
        ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f)) := by
      rw [hfactor]
      infer_instance
    exact isIso_of_baseChange b ((GroupScheme.baseChange a).map f)
  have hres' (s : S) :
      IsIso ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom) := by
    let := hres s
    exact inferInstanceAs (IsIso (residueFiberHom f s).hom.hom)
  have : IsOpenImmersion f.hom.hom.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f.hom.hom fun s => by
      let := hres' s
      exact inferInstanceAs
        (IsOpenImmersion (((Over.forget _).map
          ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom))))
  have : Surjective f.hom.hom.left := by
    refine ⟨fun y => ?_⟩
    let s : S := Y.X.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.X.hom) (g := S.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (S.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    let := hres' s
    have : IsIso
        ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left :=
      Functor.map_isIso (Over.forget (Spec (S.residueField s)))
        ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom)
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left).surjective y'
    have hcomp : pullback.fst X.X.hom (S.fromSpecResidueField s) ≫ f.hom.hom.left =
        ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left ≫
          pullback.fst Y.X.hom (S.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    change (pullback.fst X.X.hom (S.fromSpecResidueField s) ≫ f.hom.hom.left) x' =
      (((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left ≫
        pullback.fst Y.X.hom (S.fromSpecResidueField s)) x'
    exact congrArg (fun a => a x') hcomp
  have : IsIso f.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget S).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget S)
  let e : X ≅ Y := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- An intersection projects isomorphically to a subgroup already contained in
the other subgroup, where containment is tested on every scheme over the base. -/
theorem isIso_subgroupIntersectionFst_of_range_le
    (n : N ⟶ P) (r : U ⟶ P) [Mono r.hom.hom]
    (hle : SubgroupFunctor.range n ≤ SubgroupFunctor.range r) :
    IsIso (subgroupIntersectionFst n r) := by
  let : Mono r := (Grp.forget (Over S)).mono_of_mono_map
    (show Mono r.hom.hom from inferInstance)
  have hr : (SubgroupFunctor.range r).IsRepresentedBy r := ⟨inferInstance, rfl⟩
  let l : N ⟶ U := hr.factorHom n hle
  have hl : l ≫ r = n := hr.factorHom_comp n hle
  let v : N ⟶ subgroupIntersection n r :=
    pullback.lift (𝟙 N) l (by simpa using hl.symm)
  let e : subgroupIntersection n r ≅ N :=
    { hom := subgroupIntersectionFst n r
      inv := v
      hom_inv_id := by
        apply (cancel_mono (pullback.fst n r)).mp
        simp [v, subgroupIntersectionFst]
      inv_hom_id := pullback.lift_fst _ _ _ }
  exact e.isIso_hom

/-- The symmetric intersection projection criterion. -/
theorem isIso_subgroupIntersectionSnd_of_range_le
    (n : N ⟶ P) (r : U ⟶ P) [Mono n.hom.hom]
    (hle : SubgroupFunctor.range r ≤ SubgroupFunctor.range n) :
    IsIso (subgroupIntersectionSnd n r) := by
  let : IsIso (pullback.fst r n) :=
    isIso_subgroupIntersectionFst_of_range_le r n hle
  change IsIso (pullback.snd n r)
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

/-- Two relative radicals agree if their scheme-theoretic intersection is
smooth over the base. -/
theorem radical_range_eq_of_smooth_intersection
    (n : N ⟶ P) (r : U ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r)
    (hK : Smooth (subgroupIntersection n r).X.hom) :
    SubgroupFunctor.range n = SubgroupFunctor.range r := by
  let : Smooth N.X.hom := hn.smooth
  let : Smooth U.X.hom := hr.smooth
  let : Smooth (subgroupIntersection n r).X.hom := hK
  have hfst (s : S) : IsIso (geometricFiberHom (subgroupIntersectionFst n r) s) := by
    let b := geometricPoint S s
    let : IsClosedImmersion ((GroupScheme.baseChange b).map r).hom.hom.left :=
      (hr.geometricFiber s).isClosedSubgroup
    let : Mono ((GroupScheme.baseChange b).map r).hom.hom := Over.mono_of_mono_left _
    let : IsIso (pullback.fst ((GroupScheme.baseChange b).map n)
        ((GroupScheme.baseChange b).map r)) :=
      isIso_subgroupIntersectionFst_of_range_le _ _
        ((hn.geometricFiber s).range_eq (hr.geometricFiber s)).le
    change IsIso ((GroupScheme.baseChange b).map (pullback.fst n r))
    rw [← PreservesPullback.iso_hom_fst]
    infer_instance
  have hsnd (s : S) : IsIso (geometricFiberHom (subgroupIntersectionSnd n r) s) := by
    let b := geometricPoint S s
    let : IsClosedImmersion ((GroupScheme.baseChange b).map n).hom.hom.left :=
      (hn.geometricFiber s).isClosedSubgroup
    let : Mono ((GroupScheme.baseChange b).map n).hom.hom := Over.mono_of_mono_left _
    let : IsIso (pullback.snd ((GroupScheme.baseChange b).map n)
        ((GroupScheme.baseChange b).map r)) :=
      isIso_subgroupIntersectionSnd_of_range_le _ _
        ((hr.geometricFiber s).range_eq (hn.geometricFiber s)).le
    change IsIso ((GroupScheme.baseChange b).map (pullback.snd n r))
    rw [← PreservesPullback.iso_hom_snd]
    infer_instance
  let : IsIso (subgroupIntersectionFst n r) :=
    isIso_of_geometricFibres _ hfst
  let : IsIso (subgroupIntersectionSnd n r) :=
    isIso_of_geometricFibres _ hsnd
  have h₁ : SubgroupFunctor.range (subgroupIntersectionHom n r) =
      SubgroupFunctor.range n :=
    SubgroupFunctor.range_iso_comp (asIso (subgroupIntersectionFst n r)) n
  have h₂ : SubgroupFunctor.range (subgroupIntersectionHom n r) =
      SubgroupFunctor.range r := by
    rw [subgroupIntersectionHom, subgroupIntersection_condition]
    exact SubgroupFunctor.range_iso_comp (asIso (subgroupIntersectionSnd n r)) r
  exact h₁.symm.trans h₂

/-- A dynamic relative radical of an affine group is the only relative radical
on all test schemes, over an arbitrary base scheme. -/
theorem radical_range_eq_of_dynamic_unipotent
    [IsAffineHom P.X.hom]
    (n : N ⟶ P) (r : U ⟶ P) (χ : (Gm S).toGrp ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r)
    (hdyn : (Dynamic.unipotent χ).IsRepresentedBy r) :
    SubgroupFunctor.range n = SubgroupFunctor.range r := by
  let : Smooth N.X.hom := hn.smooth
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := by
    rw [← Over.w n.hom.hom]
    infer_instance
  have hnorm : (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range χ) :=
    fun T g x _ hx => hn.isNormal T g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation n χ hnorm
  have hKrep : a.unipotent.IsRepresentedBy (subgroupIntersectionFst n r) :=
    intersection_represents_action_unipotent n r χ hn.isClosedSubgroup
      hr.isClosedSubgroup hdyn hnorm
  exact radical_range_eq_of_smooth_intersection n r hn hr
    (smooth_of_action_unipotent a hKrep)

/-- The canonical comparison with a dynamic relative radical. -/
def dynamicRadicalIso [IsAffineHom P.X.hom]
    (n : N ⟶ P) (r : U ⟶ P) (χ : (Gm S).toGrp ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r)
    (hdyn : (Dynamic.unipotent χ).IsRepresentedBy r) : N ≅ U := by
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  have hnrep : (SubgroupFunctor.range r).IsRepresentedBy n :=
    ⟨Over.mono_of_mono_left _, radical_range_eq_of_dynamic_unipotent n r χ hn hr hdyn⟩
  exact hnrep.isoOfIsRepresentedBy ⟨Over.mono_of_mono_left _, rfl⟩

/-- The comparison preserves the two inclusions into the ambient group. -/
theorem dynamicRadicalIso_hom_comp [IsAffineHom P.X.hom]
    (n : N ⟶ P) (r : U ⟶ P) (χ : (Gm S).toGrp ⟶ P)
    (hn : IsRelativeUnipotentRadical n) (hr : IsRelativeUnipotentRadical r)
    (hdyn : (Dynamic.unipotent χ).IsRepresentedBy r) :
    (dynamicRadicalIso n r χ hn hr hdyn).hom ≫ r = n :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end RelativeLevi

end Langlands.GroupScheme
