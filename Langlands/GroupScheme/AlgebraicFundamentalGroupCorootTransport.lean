import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugators
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.FieldExtensionProof
import Langlands.Geometry.Building.SimplyConnectedImageNormal

/-! # Geometric conjugators preserve the coroot images of the derived covers -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A simply connected cover of the derived subgroup stays one after field extension. -/
theorem IsSimplyConnectedDerivedCover.fieldBaseChange {k : Type u} [Field k]
    (K : Type u) [Field K] [Algebra k K]
    {H D C : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ H} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) :
    IsSimplyConnectedDerivedCover ((GroupScheme.baseChange (algebraBaseMap k K)).map d)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map π) := by
  have : IsAffineHom H.X.hom := h.isConnectedReductive.isAffineHom
  exact ⟨connectedReductiveFieldExtensionStatement k K H h.isConnectedReductive,
    h.isDerivedSubgroup.baseChange_of_eq _ (derivedSubgroup_baseChange_eq_of_field _ H),
    isSimplyConnectedCover_fieldExtension k K C D π h.isSimplyConnectedCover⟩

namespace AlgebraicFundamentalGroup

namespace Choice

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
variable {E : Type u} [Field E] [Algebra k E]

/-- A geometric cocharacter of `T` lies in the coroot image as soon as its composite with
`T → G` lifts through the derived cover `G_sc → D → G`: the lift and the cocharacter define
a cocharacter of the actual preimage torus. -/
theorem mem_corootImage_of_lift (a : Choice k G)
    (x : (Gm (Spec (CommRingCat.of E))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k E)).obj a.cover)
    (ν : a.lattice E)
    (hx : x ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.covering ≫ a.derivedInclusion) =
      CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion) :
    ν ∈ a.corootImage E := by
  let bcIso := subgroupIntersectionBaseChangeIso (algebraBaseMap k E)
    (a.covering ≫ a.derivedInclusion) a.inclusion
  let l : (Gm (Spec (CommRingCat.of E))).toGrp ⟶
      subgroupIntersection ((GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.covering ≫ a.derivedInclusion))
        ((GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion) :=
    pullback.lift x (CommGroupScheme.groupHom ν) hx
  refine ⟨Additive.ofMul (l ≫ bcIso.inv), ?_⟩
  apply Additive.toMul.injective
  change (l ≫ bcIso.inv) ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map
      (subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion) =
    CommGroupScheme.groupHom ν
  rw [Category.assoc]
  change l ≫ (PreservesPullback.iso (GroupScheme.baseChange (algebraBaseMap k E))
      (a.covering ≫ a.derivedInclusion) a.inclusion).inv ≫
    (GroupScheme.baseChange (algebraBaseMap k E)).map
      (pullback.snd (a.covering ≫ a.derivedInclusion) a.inclusion) = _
  rw [PreservesPullback.iso_inv_snd]
  exact pullback.lift_snd _ _ _

/-- A geometric conjugator carries the coroot image of one presentation into the coroot
image of the other: conjugation lifts to the simply connected covers. -/
theorem IsConjugationComparison.corootImage_le {a b : Choice k G}
    {g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) :
    a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom) := by
  obtain ⟨ψ, hψ⟩ := (a.isCover.fieldBaseChange E).exists_comp_eq_comp_iso
    (b.isCover.fieldBaseChange E) (((GroupScheme.baseChange (algebraBaseMap k E)).obj G).innerIso g)
  rintro _ ⟨ν, rfl⟩
  refine b.mem_corootImage_of_lift (CommGroupScheme.groupHom ν ≫
    (GroupScheme.baseChange (algebraBaseMap k E)).map a.scInclusion ≫ ψ) _ ?_
  have hsq := congrArg (GroupScheme.baseChange (algebraBaseMap k E)).map
    (subgroupIntersection_condition (a.covering ≫ a.derivedInclusion) a.inclusion)
  simp only [Functor.map_comp] at hsq hψ ⊢
  unfold IsConjugationComparison at h
  change _ = CommGroupScheme.groupHom ν ≫
    (GroupScheme.baseChange (algebraBaseMap k E)).map
      (subgroupIntersectionSnd (a.covering ≫ a.derivedInclusion) a.inclusion) ≫
    CommGroupScheme.groupHom e.hom ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
  rw [← h]
  simp only [Category.assoc, hψ]
  rw [reassoc_of% hsq]

end Choice

end AlgebraicFundamentalGroup

end Langlands.GroupScheme
