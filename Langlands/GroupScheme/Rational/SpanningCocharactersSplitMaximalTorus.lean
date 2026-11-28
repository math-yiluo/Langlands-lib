import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Reductive.MultiplicationBaseChange
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Split maximal tori from two spanning rational cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

private theorem range_prodHom_le {S : Scheme.{u}} {A B H G : GroupScheme S}
    (a : A ⟶ G) (b : B ⟶ G) (t : H ⟶ G) (hcomm)
    (ha : SubgroupFunctor.range a ≤ SubgroupFunctor.range t)
    (hb : SubgroupFunctor.range b ≤ SubgroupFunctor.range t) :
    SubgroupFunctor.range (prodHom a b hcomm) ≤ SubgroupFunctor.range t := by
  rintro X _ ⟨y, rfl⟩
  change y ≫ (prodHom a b hcomm).hom.hom ∈ (SubgroupFunctor.range t).carrier X
  rw [comp_prodHom]
  exact (SubgroupFunctor.range t).carrier X |>.mul_mem
    (ha X (SubgroupFunctor.mem_range.mpr ⟨(productPointsEquiv A B X y).1, rfl⟩))
    (hb X (SubgroupFunctor.mem_range.mpr ⟨(productPointsEquiv A B X y).2, rfl⟩))

section Field

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]

local notation "b" => algebraBaseMap k E
local notation "B" => GroupScheme.baseChange b
local notation "U" => CommGroupScheme.toGrp (Gm (Spec (CommRingCat.of k)))

/-- If two commuting rational cocharacters base change to nonzero multiples
of generators of a geometric maximal torus, their split image is a maximal
torus over the original field. -/
theorem hasSplitMaximalTorus_of_two_spanning_cocharacters
    (χ ψ : U ⟶ G)
    (hcomm : ∀ (X : Over (Spec (CommRingCat.of k))) (x y : X ⟶ (U).X),
      Commute (x ≫ χ.hom.hom) (y ≫ ψ.hom.hom))
    (T : CommGroupScheme (Spec (CommRingCat.of E))) (t : T.toGrp ⟶ (B).obj G)
    (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (eta theta : cocharacterLattice T) (hspan : Submodule.span ℤ {eta, theta} = ⊤)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hχ : Dynamic.baseChangeCocharacter b χ = CommGroupScheme.groupHom (m • eta) ≫ t)
    (hψ : Dynamic.baseChangeCocharacter b ψ = CommGroupScheme.groupHom (n • theta) ≫ t) :
    HasSplitMaximalTorus G := by
  let hU : IsSplitTorus (U ⊗ U) := isSplitTorus_gm.tensor isSplitTorus_gm
  let P : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { (U ⊗ U : GroupScheme (Spec (CommRingCat.of k))) with comm := hU.isCommMonObj }
  let Φ : P.toGrp ⟶ G := prodHom χ ψ hcomm
  let d := hU.dominantFactorization Φ
  let s := (B).map d.inclusion
  let f := (B).map d.factor
  have hΦ : f ≫ s = (B).map Φ := by
    change (B).map d.factor ≫ (B).map d.inclusion = _
    rw [← Functor.map_comp, d.factor_comp]
  have hχ' : (B).map χ = (Gm.baseChangeIso b).hom ≫ CommGroupScheme.groupHom (m • eta) ≫ t := by
    change (Gm.baseChangeIso b).inv ≫ (B).map χ = _ at hχ
    simpa only [Iso.hom_inv_id_assoc] using congrArg (fun f => (Gm.baseChangeIso b).hom ≫ f) hχ
  have hψ' : (B).map ψ = (Gm.baseChangeIso b).hom ≫ CommGroupScheme.groupHom (n • theta) ≫ t := by
    change (Gm.baseChangeIso b).inv ≫ (B).map ψ = _ at hψ
    simpa only [Iso.hom_inv_id_assoc] using congrArg (fun f => (Gm.baseChangeIso b).hom ≫ f) hψ
  let : Flat b := (fieldExtension_fpqc k E).2.1
  let : IsAffineHom P.X.hom := hU.isAffineHom
  let : IsAffineHom d.image.X.hom := d.isSplitSubtorus.1.isAffineHom
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : IsAffine d.image.X.left := isAffine_of_isAffineHom d.image.X.hom
  let : QuasiCompact d.factor.hom.hom.left := inferInstance
  let : IsSchemeTheoreticallyDominant d.factor.hom.hom.left := d.dominant
  let : IsSchemeTheoreticallyDominant f.hom.hom.left := isSchemeTheoreticallyDominant_baseChange b d.factor
  have hcommE (X : Over (Spec (CommRingCat.of E))) (x y : X ⟶ ((B).obj U).X) :
      Commute (x ≫ ((B).map χ).hom.hom) (y ≫ ((B).map ψ).hom.hom) := by
    apply (commute_iff_eq _ _).mpr
    apply (baseChangePointsEquiv b G X).injective
    simp only [map_mul, baseChangePointsEquiv_comp]
    exact (hcomm _ _ _).eq
  have hst : SubgroupFunctor.range s ≤ SubgroupFunctor.range t := by
    apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant f s t ht.2.1).mp
    rw [hΦ, show Φ = prodHom χ ψ hcomm from rfl, baseChange_prodHom b χ ψ hcomm hcommE]
    apply (SubgroupFunctor.range_comp_le _ _).trans
    apply range_prodHom_le _ _ t hcommE
    · rw [hχ', ← Category.assoc]
      exact SubgroupFunctor.range_comp_le _ _
    · rw [hψ', ← Category.assoc]
      exact SubgroupFunctor.range_comp_le _ _
  have hsc : IsClosedSubgroup s := d.isSplitSubtorus.2.baseChange b
  let V := cocharactersLandingIn t (SubgroupFunctor.range s)
  have h1 : m • eta ∈ V := by
    have hι : CommGroupScheme.groupHom (m • eta) ≫ t =
        ((Gm.baseChangeIso b).inv ≫ (B).map (prodInl U U) ≫ f) ≫ s := by
      rw [← hχ, Category.assoc, Category.assoc, hΦ, ← Functor.map_comp]
      rw [show prodInl U U ≫ Φ = χ from prodInl_prodHom χ ψ hcomm]
      rfl
    intro X x
    exact (SubgroupFunctor.range_comp_le _ s) X
      (SubgroupFunctor.mem_range.mpr ⟨x, by rw [hι]⟩)
  have h2 : n • theta ∈ V := by
    have hι : CommGroupScheme.groupHom (n • theta) ≫ t =
        ((Gm.baseChangeIso b).inv ≫ (B).map (prodInr U U) ≫ f) ≫ s := by
      rw [← hψ, Category.assoc, Category.assoc, hΦ, ← Functor.map_comp]
      rw [show prodInr U U ≫ Φ = ψ from prodInr_prodHom χ ψ hcomm]
      rfl
    intro X x
    exact (SubgroupFunctor.range_comp_le _ s) X
      (SubgroupFunctor.mem_range.mpr ⟨x, by rw [hι]⟩)
  have htop : V = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with h | h
    · change x = eta at h
      exact h.symm ▸ mem_cocharactersLandingIn_of_zsmul_mem t hsc hm h1
    · change x = theta at h
      exact h.symm ▸ mem_cocharactersLandingIn_of_zsmul_mem t hsc hn h2
  have hR : SubgroupFunctor.range s = SubgroupFunctor.range t :=
    le_antisymm hst (hT.range_le_of_cocharacters t _ htop)
  let : Mono s.hom.hom.left := hsc.mono
  let : Mono t.hom.hom.left := ht.2.1.mono
  have hsrep : (SubgroupFunctor.range s).IsRepresentedBy s := ⟨Over.mono_of_mono_left _, rfl⟩
  have htrep : (SubgroupFunctor.range s).IsRepresentedBy t := ⟨Over.mono_of_mono_left _, hR.symm⟩
  let e : ((CommGroupScheme.baseChange b).obj d.image).toGrp ≅ T.toGrp :=
    hsrep.isoOfIsRepresentedBy htrep
  have hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj d.image) s := by
    rw [← hsrep.isoOfIsRepresentedBy_hom_comp htrep]
    exact ht.iso_comp e
  exact ⟨d.image, d.inclusion, d.isSplitSubtorus.1,
    (maximalTorusBaseChange k E G d.image d.inclusion d.isSplitSubtorus.1.isTorus
      d.isSplitSubtorus.2).mpr hmax⟩

end Field

section ClosedSubgroup

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [Smooth H.X.hom]

local notation "b" => algebraBaseMap k E
local notation "B" => GroupScheme.baseChange b
local notation "U" => CommGroupScheme.toGrp (Gm (Spec (CommRingCat.of k)))
local notation "V" => CommGroupScheme.toGrp (Gm (Spec (CommRingCat.of E)))

omit [IsAffineHom H.X.hom] [Smooth H.X.hom] in
private theorem exists_factor_cocharacter (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (χ : U ⟶ G) (x : V ⟶ (B).obj H)
    (hx : Dynamic.baseChangeCocharacter b χ = x ≫ (B).map j) :
    ∃ ψ : U ⟶ H, ψ ≫ j = χ ∧ Dynamic.baseChangeCocharacter b ψ = x := by
  let : Mono j.hom.hom.left := hj.mono
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let hre : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k E
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hq
  have hle : SubgroupFunctor.range χ ≤ SubgroupFunctor.range j := by
    apply (SubgroupFunctor.baseChange_le_range_iff b j).mp
    rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
    have hχ : (B).map χ = (Gm.baseChangeIso b).hom ≫ x ≫ (B).map j := by
      change (Gm.baseChangeIso b).inv ≫ (B).map χ = _ at hx
      simpa only [Iso.hom_inv_id_assoc] using congrArg (fun y => (Gm.baseChangeIso b).hom ≫ y) hx
    rw [hχ, ← Category.assoc]
    exact SubgroupFunctor.range_comp_le _ _
  let ψ := hre.factorHom χ hle
  have hψ : ψ ≫ j = χ := hre.factorHom_comp _ _
  refine ⟨ψ, hψ, ?_⟩
  apply (hre.baseChange b).hom_ext
  change ((Gm.baseChangeIso b).inv ≫ (B).map ψ) ≫ (B).map j = _
  rw [Category.assoc, ← Functor.map_comp, hψ]
  exact hx

/-- The spanning criterion applies when the two rational directions are
given in an ambient group and land geometrically in a closed subgroup. -/
theorem hasSplitMaximalTorus_of_two_spanning_cocharacters_in_subgroup
    (j : H ⟶ G) (hj : IsClosedSubgroup j) (χ ψ : U ⟶ G)
    (hcomm : ∀ (X : Over (Spec (CommRingCat.of k))) (x y : X ⟶ (U).X),
      Commute (x ≫ χ.hom.hom) (y ≫ ψ.hom.hom))
    (T : CommGroupScheme (Spec (CommRingCat.of E))) (t : T.toGrp ⟶ (B).obj H)
    (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (eta theta : cocharacterLattice T) (hspan : Submodule.span ℤ {eta, theta} = ⊤)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hχ : Dynamic.baseChangeCocharacter b χ = CommGroupScheme.groupHom (m • eta) ≫ t ≫ (B).map j)
    (hψ : Dynamic.baseChangeCocharacter b ψ = CommGroupScheme.groupHom (n • theta) ≫ t ≫ (B).map j) :
    HasSplitMaximalTorus H := by
  obtain ⟨a, ha, haE⟩ := exists_factor_cocharacter j hj χ
    (CommGroupScheme.groupHom (m • eta) ≫ t) (by rw [Category.assoc]; exact hχ)
  obtain ⟨d, hd, hdE⟩ := exists_factor_cocharacter j hj ψ
    (CommGroupScheme.groupHom (n • theta) ≫ t) (by rw [Category.assoc]; exact hψ)
  refine hasSplitMaximalTorus_of_two_spanning_cocharacters a d ?_ T t hT ht eta theta hspan m n hm hn
    haE hdE
  intro X x y
  let : Mono j.hom.hom.left := hj.mono
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (commute_iff_eq _ _).mpr
  apply (cancel_mono j.hom.hom).mp
  simp only [MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, ha, hd]
  exact (hcomm X x y).eq

end ClosedSubgroup

/-- Two rational cocharacters whose base changes give nonzero multiples
of spanning directions provide a split maximal torus of the closed group. -/
def SpanningCocharactersSplitMaximalTorusStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E]
    (G H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] [Smooth H.X.hom]
    (j : H ⟶ G), IsClosedSubgroup j →
    let S := Spec (CommRingCat.of k)
    let b := algebraBaseMap k E
    let B := GroupScheme.baseChange b
    ∀ (a d : (Gm S).toGrp ⟶ G),
    (∀ (X : Over S) (x y : X ⟶ (Gm S).X),
      Commute (x ≫ a.hom.hom) (y ≫ d.hom.hom)) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of E))) (t : T.toGrp ⟶ B.obj H),
    IsSplitTorus T.toGrp → IsMaximalTorus t →
    ∀ (eta theta : cocharacterLattice T), Submodule.span ℤ {eta, theta} = ⊤ →
    ∀ (m n : ℤ), m ≠ 0 → n ≠ 0 →
    Dynamic.baseChangeCocharacter b a = CommGroupScheme.groupHom (m • eta) ≫ t ≫ B.map j →
    Dynamic.baseChangeCocharacter b d = CommGroupScheme.groupHom (n • theta) ≫ t ≫ B.map j →
    HasSplitMaximalTorus H

theorem spanningCocharactersSplitMaximalTorus : SpanningCocharactersSplitMaximalTorusStatement.{u} := by
  intro k E _ _ _ G H _ _ j hj
  dsimp only
  exact hasSplitMaximalTorus_of_two_spanning_cocharacters_in_subgroup j hj

end Langlands.GroupScheme
