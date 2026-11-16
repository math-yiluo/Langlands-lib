import Langlands.GroupScheme.LocalGroupIsoSubgroup
import Langlands.GroupScheme.Rational.InnerDiscrepancyRefinement
import Langlands.GroupScheme.RelativeLevi.BorelConjugacyProof
import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.RelativeLevi.ConjugatorBaseChange
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Borel-preserving refinements of natural local group isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A B C : GroupScheme S} {U : Over S}

/-- Twisting both a local family and its cocycle retains the discrepancy equation. -/
theorem HasDiscrepancy.twist {e : LocalGroupIso G H U} {a : AutomorphicAction A G}
    {ξ : Cocycle A U} (h : e.HasDiscrepancy a ξ) (f : U ⟶ A.X) :
    (e.twist a f).HasDiscrepancy a (ξ.twist f) := by
  intro T b c g
  change e.toFun b (a.act (b ≫ f)
      (a.act ((b ≫ f)⁻¹ * ξ.toFun b c * (c ≫ f)) g)) =
    e.toFun c (a.act (c ≫ f) g)
  rw [← a.act_mul_left]
  have hc : (b ≫ f) * ((b ≫ f)⁻¹ * ξ.toFun b c * (c ≫ f)) =
      ξ.toFun b c * (c ≫ f) := by group
  rw [hc, a.act_mul_left, h]

/-- Innerness is preserved by every change of local trivialization. -/
theorem HasInnerDiscrepancy.twist {e : LocalGroupIso G H U} {a : AutomorphicAction A G}
    (h : e.HasInnerDiscrepancy a) (f : U ⟶ A.X) :
    (e.twist a f).HasInnerDiscrepancy a := by
  intro T b c
  obtain ⟨x, hx⟩ := h b c
  refine ⟨(b ≫ f)⁻¹ * x * (c ≫ f), ?_⟩
  intro W t g
  change e.toFun (t ≫ b) (a.act ((t ≫ b) ≫ f)
      (a.act (t ≫ ((b ≫ f)⁻¹ * x * (c ≫ f))) g)) =
    e.toFun (t ≫ c) (a.act ((t ≫ c) ≫ f) g)
  rw [← a.act_mul_left]
  have hc : ((t ≫ b) ≫ f) * (t ≫ ((b ≫ f)⁻¹ * x * (c ≫ f))) =
      (t ≫ x) * ((t ≫ c) ≫ f) := by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    simp only [Category.assoc]
    group
  rw [hc, a.act_mul_left, hx t]

/-- Twisting by a group point agrees with twisting by its image in a compatible action. -/
theorem twist_conjugation_eq (e : LocalGroupIso G H U)
    (a : AutomorphicAction A G) (q : G ⟶ A)
    (hq : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) (f : U ⟶ G.X) :
    e.twist (AutomorphicAction.conjugation (𝟙 G)) f = e.twist a (f ≫ q.hom.hom) := by
  apply ext_toFun
  intro T b g
  change e.toFun b ((AutomorphicAction.conjugation (𝟙 G)).act (b ≫ f) g) =
    e.toFun b (a.act (b ≫ (f ≫ q.hom.hom)) g)
  rw [← hq, AutomorphicAction.restrict_act, Category.assoc]

/-- Membership in a represented subgroup is retained by the cover-point equivalence. -/
theorem mem_range_coverPointsEquiv (i : B ⟶ G) {T : Over S} (a : T ⟶ U)
    (x : coverTest a ⟶ ((baseChange U.hom).obj G).X) :
    coverPointsEquiv G a x ∈ (SubgroupFunctor.range i).carrier T ↔
      x ∈ (SubgroupFunctor.range ((baseChange U.hom).map i)).carrier (coverTest a) := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(coverPointsEquiv B a).symm y, ?_⟩
    apply (coverPointsEquiv G a).injective
    rw [coverPointsEquiv_comp, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨coverPointsEquiv B a y, (coverPointsEquiv_comp i a y).symm⟩

/-- The recovered base-change isomorphism evaluates to the original family at cover points. -/
theorem toBaseChangeIso_coverPoints (e : LocalGroupIso G H U)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    coverPointsEquiv H a
        ((coverPointsEquiv G a).symm g ≫ e.toBaseChangeIso.hom.hom.hom) =
      e.toFun a g := by
  exact congrArg (fun f : LocalGroupIso G H U => f.toFun a g)
    (ofBaseChangeIso_toBaseChangeIso e)

/-- A conjugator of the two subgroup images supplies a subgroup-preserving local family. -/
theorem preservesSubgroup_of_baseChange_conjugator (e : LocalGroupIso G H U)
    (i : B ⟶ G) (j : C ⟶ H) (T : Over U.left)
    (n : T ⟶ ((baseChange U.hom).obj H).X)
    (hn : RelativeLevi.IsRangeConjugator
      ((baseChange U.hom).map i ≫ e.toBaseChangeIso.hom)
      ((baseChange U.hom).map j) n) :
    ((e.refine (baseChangeTestPoint T)).twist
      (AutomorphicAction.conjugation (𝟙 G))
      ((e.toFun (baseChangeTestPoint T)).symm
        (baseChangePointsEquiv U.hom H T n))).PreservesSubgroup
          (SubgroupFunctor.range i) (SubgroupFunctor.range j) := by
  intro V b g
  let a := b ≫ baseChangeTestPoint T
  let t : coverTest a ⟶ T := Over.homMk b.left rfl
  let x := (coverPointsEquiv G a).symm g
  let y := x ≫ e.toBaseChangeIso.hom.hom.hom
  have hnproj : coverPointsEquiv H a (t ≫ n) =
      b ≫ baseChangePointsEquiv U.hom H T n := by
    apply Over.OverMorphism.ext
    rw [coverPointsEquiv_left]
    change (b.left ≫ n.left) ≫ pullback.fst H.X.hom U.hom =
      b.left ≫ (baseChangePointsEquiv U.hom H T n).left
    rw [baseChangePointsEquiv_left]
    exact Category.assoc _ _ _
  have hvalue : ((e.refine (baseChangeTestPoint T)).twist
      (AutomorphicAction.conjugation (𝟙 G))
      ((e.toFun (baseChangeTestPoint T)).symm
        (baseChangePointsEquiv U.hom H T n))).toFun b g =
      coverPointsEquiv H a ((t ≫ n) * y * (t ≫ n)⁻¹) := by
    change e.toFun a ((AutomorphicAction.conjugation (𝟙 G)).act
        (b ≫ (e.toFun (baseChangeTestPoint T)).symm
          (baseChangePointsEquiv U.hom H T n)) g) = _
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
      map_mul, map_mul, map_inv]
    have hs := e.symm.naturality b (baseChangeTestPoint T)
      (baseChangePointsEquiv U.hom H T n)
    change (e.toFun a).symm (b ≫ baseChangePointsEquiv U.hom H T n) =
      b ≫ (e.toFun (baseChangeTestPoint T)).symm
        (baseChangePointsEquiv U.hom H T n) at hs
    rw [← hs, MulEquiv.apply_symm_apply, ← hnproj,
      map_mul, map_mul, map_inv, toBaseChangeIso_coverPoints]
  rw [hvalue, mem_range_coverPointsEquiv]
  have hc := hn (coverTest a) t ((t ≫ n) * y * (t ≫ n)⁻¹)
  have hcancel : (t ≫ n)⁻¹ * ((t ≫ n) * y * (t ≫ n)⁻¹) * (t ≫ n) = y := by group
  rw [hc, hcancel, MaximalTorusParameterExistence.mem_range_comp_iso_iff]
  have hy : y ≫ e.toBaseChangeIso.inv.hom.hom = x := by
    change (x ≫ e.toBaseChangeIso.hom.hom.hom) ≫ e.toBaseChangeIso.inv.hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
  rw [hy, ← mem_range_coverPointsEquiv, MulEquiv.apply_symm_apply]

/-- Data for a refinement on which a source conjugation makes a local
isomorphism identify the two specified subgroup functors. -/
structure BorelPreservingRefinement (e : LocalGroupIso G H U)
    (i : B ⟶ G) (j : C ⟶ H) where
  parameter : Over S
  map : parameter ⟶ U
  etale : Etale map.left
  surjective : Surjective map.left
  cochain : parameter ⟶ G.X
  preserves : ((e.refine map).twist
    (AutomorphicAction.conjugation (𝟙 G)) cochain).PreservesSubgroup
      (SubgroupFunctor.range i) (SubgroupFunctor.range j)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def conjugatorOnSigma {S' : Scheme.{u}} {P L L' : GroupScheme S'}
    (k : L ⟶ P) (l : L' ⟶ P) [Mono k.hom.hom] [Mono l.hom.hom]
    (𝒱 : S'.Cover.{u} (Scheme.precoverage @Etale))
    (nlocal : (a : 𝒱.I₀) → Over.mk (𝒱.f a) ⟶ P.X)
    (hnlocal : ∀ a, RelativeLevi.IsRangeConjugator k l (nlocal a)) :
    Σ T : Over S', {n : T ⟶ P.X //
      Etale T.hom ∧ Surjective T.hom ∧ RelativeLevi.IsRangeConjugator k l n} := by
  let T : Over S' := Over.mk (Sigma.desc 𝒱.f)
  let nleft : T.left ⟶ P.X.left := Sigma.desc (fun a => (nlocal a).left)
  have hnleft : nleft ≫ P.X.hom = T.hom := by
    apply Sigma.hom_ext
    intro a
    change Sigma.ι 𝒱.X a ≫ Sigma.desc (fun b => (nlocal b).left) ≫ P.X.hom =
      Sigma.ι 𝒱.X a ≫ Sigma.desc 𝒱.f
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact Over.w (nlocal a)
  let n : T ⟶ P.X := Over.homMk nleft hnleft
  let ℰ := (sigmaOpenCover 𝒱.X).changeProp
    (Q := @Etale) (fun a => inferInstance)
  have hn : RelativeLevi.IsRangeConjugator k l n := by
    apply (RelativeLevi.isRangeConjugator_iff_etaleCover k l ℰ n).mpr
    intro a
    let t : SubgroupFunctor.etaleCoverObj (T := T) ℰ a ⟶ Over.mk (𝒱.f a) :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ 𝒱.f a = Sigma.ι 𝒱.X a ≫ Sigma.desc 𝒱.f
        simp)
    have ht : SubgroupFunctor.etaleCoverMap ℰ a ≫ n = t ≫ nlocal a := by
      apply Over.OverMorphism.ext
      change Sigma.ι 𝒱.X a ≫ Sigma.desc (fun b => (nlocal b).left) =
        𝟙 _ ≫ (nlocal a).left
      simp
    rw [ht]
    exact (hnlocal a).comp t
  refine ⟨T, n, ?_, ?_, hn⟩
  · change Etale (Sigma.desc 𝒱.f)
    exact 𝒱.sigma.map_prop default
  · change Surjective (Sigma.desc 𝒱.f)
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, hy⟩ := 𝒱.exists_eq x
    exact ⟨Sigma.ι 𝒱.X a y, by
      simpa only [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hy⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def etaleBorelConjugator {S' : Scheme.{u}} {P L L' : GroupScheme S'}
    (hP : IsReductive P) (k : L ⟶ P) (l : L' ⟶ P)
    (hk : IsRelativeBorelSubgroup k) (hl : IsRelativeBorelSubgroup l) :
    Σ T : Over S', {n : T ⟶ P.X //
      Etale T.hom ∧ Surjective T.hom ∧ RelativeLevi.IsRangeConjugator k l n} := by
  let d := relativeBorelEtaleConjugacyData
    relativeParabolicEtaleLocalConjugacyStatement hP hk hl
  let 𝒱 := d.1
  let nlocal (a : 𝒱.I₀) : Over.mk (𝒱.f a) ⟶ P.X :=
    baseChangeBasePointsEquiv (𝒱.f a) P (d.2 a).1
  have hnlocal (a : 𝒱.I₀) : RelativeLevi.IsRangeConjugator k l (nlocal a) := by
    apply (RelativeLevi.isRangeConjugator_iff_range_baseChange_eq
      k l (Over.mk (𝒱.f a)) (nlocal a)).mpr
    change SubgroupFunctor.range ((baseChange (𝒱.f a)).map l) =
      SubgroupFunctor.range ((baseChange (𝒱.f a)).map k ≫
        (((baseChange (𝒱.f a)).obj P).innerIso
          ((baseChangeBasePointsEquiv (𝒱.f a) P).symm
            (baseChangeBasePointsEquiv (𝒱.f a) P (d.2 a).1))).hom)
    rw [MulEquiv.symm_apply_apply]
    exact (d.2 a).2.symm
  let : Mono k.hom.hom := hk.isRelativeParabolicSubgroup.mono
  let : Mono l.hom.hom := hl.isRelativeParabolicSubgroup.mono
  exact conjugatorOnSigma k l 𝒱 nlocal hnlocal

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Relative Borel conjugacy gives a single surjective etale refinement
and an actual conjugating cochain for a natural local group isomorphism. -/
def borelPreservingRefinement (e : LocalGroupIso G H U)
    (hG : IsReductive G) (hH : IsReductive H)
    (i : B ⟶ G) (j : C ⟶ H)
    (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j) :
    BorelPreservingRefinement e i j := by
  let k := (baseChange U.hom).map i ≫ e.toBaseChangeIso.hom
  let l := (baseChange U.hom).map j
  have hk : IsRelativeBorelSubgroup k :=
    (hi.baseChange hG U.hom).comp_iso e.toBaseChangeIso
  have hl : IsRelativeBorelSubgroup l := hj.baseChange hH U.hom
  obtain ⟨T, n, het, hs, hn⟩ :=
    etaleBorelConjugator (hH.baseChange U.hom) k l hk hl
  exact ⟨(Over.map U.hom).obj T, baseChangeTestPoint T, het, hs,
    (e.toFun (baseChangeTestPoint T)).symm
      (baseChangePointsEquiv U.hom H T n),
    e.preservesSubgroup_of_baseChange_conjugator i j T n hn⟩

/-- Refinement and twisting by the image of the chosen cochain retain
the original all-refinement innerness for any action. -/
theorem BorelPreservingRefinement.hasInnerDiscrepancy
    {e : LocalGroupIso G H U} {i : B ⟶ G} {j : C ⟶ H}
    (d : BorelPreservingRefinement e i j)
    (a : AutomorphicAction A G) (q : G ⟶ A)
    (he : e.HasInnerDiscrepancy a) :
    ((e.refine d.map).twist a (d.cochain ≫ q.hom.hom)).HasInnerDiscrepancy a :=
  HasInnerDiscrepancy.twist (HasInnerDiscrepancy.refine he d.map) _

/-- The same quotient-action twist identifies the specified Borel subgroups. -/
theorem BorelPreservingRefinement.preservesSubgroup
    {e : LocalGroupIso G H U} {i : B ⟶ G} {j : C ⟶ H}
    (d : BorelPreservingRefinement e i j)
    (a : AutomorphicAction A G) (q : G ⟶ A)
    (hq : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    ((e.refine d.map).twist a (d.cochain ≫ q.hom.hom)).PreservesSubgroup
      (SubgroupFunctor.range i) (SubgroupFunctor.range j) := by
  rw [← twist_conjugation_eq _ a q hq]
  exact d.preserves

end LocalGroupIso

end Langlands.GroupScheme
