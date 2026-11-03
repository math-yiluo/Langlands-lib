import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.PointDecomposition

/-! # The all-test opposite-cell step in normalizer separation -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Pulling a base point back to a test scheme preserves subgroup-functor membership. -/
theorem SubgroupFunctor.constantPoint_mem {S : Scheme.{u}} {G : GroupScheme S}
    (F : SubgroupFunctor G) (X : Over S) {g : Over.mk (𝟙 S) ⟶ G.X}
    (hg : g ∈ F.carrier (Over.mk (𝟙 S))) : G.constantPoint g X ∈ F.carrier X :=
  F.comp_mem (T := Over.mk (𝟙 S)) (T' := X) (x := g)
    (Over.homMk X.hom (by simp)) hg

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Injectivity of multiplication from opposite-unipotent points and
parabolic points, on every test scheme. -/
def HasInjectiveOppositeCellMultiplication : Prop :=
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  ∀ X : Over (Spec (CommRingCat.of k)),
    Function.Injective (fun z : (Dynamic.unipotent χminus).carrier X ×
        (Dynamic.parabolic χ).carrier X =>
      (z.1 : X ⟶ G.X) * z.2)

/-- Trivial intersection of the opposite unipotent group with the parabolic
on every test implies injectivity of their multiplication. -/
theorem hasInjectiveOppositeCellMultiplication_of_trivial_intersection
    (htriv : ∀ (X : Over (Spec (CommRingCat.of k))) (g : X ⟶ G.X),
      g ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
          (CommGroupScheme.groupHom ν ≫ i))).carrier X →
      g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier X → g = 1) :
    HasInjectiveOppositeCellMultiplication i ν := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  intro X a b hab
  change (a.1 : X ⟶ G.X) * (a.2 : X ⟶ G.X) =
    (b.1 : X ⟶ G.X) * (b.2 : X ⟶ G.X) at hab
  have hg : (b.1 : X ⟶ G.X)⁻¹ * a.1 =
      (b.2 : X ⟶ G.X) * (a.2 : X ⟶ G.X)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    rw [mul_assoc, hab, inv_mul_cancel_left]
  have hgu : (b.1 : X ⟶ G.X)⁻¹ * a.1 ∈ (Dynamic.unipotent χminus).carrier X :=
    ((Dynamic.unipotent χminus).carrier X).mul_mem
      (((Dynamic.unipotent χminus).carrier X).inv_mem b.1.property) a.1.property
  have hgp : (b.1 : X ⟶ G.X)⁻¹ * a.1 ∈ (Dynamic.parabolic χ).carrier X := by
    rw [hg]
    exact ((Dynamic.parabolic χ).carrier X).mul_mem b.2.property
      (((Dynamic.parabolic χ).carrier X).inv_mem a.2.property)
  have hu : (a.1 : X ⟶ G.X) = b.1 :=
    (inv_mul_eq_one.mp (htriv X _ hgu hgp)).symm
  have hp : (a.2 : X ⟶ G.X) = b.2 := by
    rw [hu] at hab
    exact mul_left_cancel hab
  exact Prod.ext (Subtype.ext hu) (Subtype.ext hp)

/-- The subgroup-functor form of the preceding trivial-intersection adapter. -/
theorem hasInjectiveOppositeCellMultiplication_of_inf_eq_bot
    (hinter : Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i)) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) = ⊥) :
    HasInjectiveOppositeCellMultiplication i ν := by
  apply hasInjectiveOppositeCellMultiplication_of_trivial_intersection i ν
  intro X g hu hp
  have hg : g ∈ ((Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i)) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier X) := ⟨hu, hp⟩
  rw [hinter] at hg
  exact Subgroup.mem_bot.mp hg

/-- Opposite-cell multiplication is injective on all tests for an affine
ambient group, by the actual opposite dynamic intersection theorem. -/
theorem hasInjectiveOppositeCellMultiplication_of_isAffine [IsAffine G.X.left] :
    HasInjectiveOppositeCellMultiplication i ν :=
  hasInjectiveOppositeCellMultiplication_of_inf_eq_bot i ν
    (Dynamic.opposite_unipotent_inf_parabolic (CommGroupScheme.groupHom ν ≫ i))

/-- A monomorphic represented opposite-cell multiplication is injective on
the subgroup-functor points of every test scheme. -/
theorem hasInjectiveOppositeCellMultiplication_of_mono
    (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    [Mono ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom))] :
    HasInjectiveOppositeCellMultiplication i ν := by
  intro X a b hab
  have hau : (a.1 : X ⟶ G.X) ∈ (SubgroupFunctor.range iU).carrier X := by
    rw [hU.2]
    exact a.1.property
  have hbu : (b.1 : X ⟶ G.X) ∈ (SubgroupFunctor.range iU).carrier X := by
    rw [hU.2]
    exact b.1.property
  have hap : (a.2 : X ⟶ G.X) ∈ (SubgroupFunctor.range iP).carrier X := by
    rw [hP.2]
    exact a.2.property
  have hbp : (b.2 : X ⟶ G.X) ∈ (SubgroupFunctor.range iP).carrier X := by
    rw [hP.2]
    exact b.2.property
  obtain ⟨ua, hua⟩ := SubgroupFunctor.mem_range.mp hau
  obtain ⟨ub, hub⟩ := SubgroupFunctor.mem_range.mp hbu
  obtain ⟨pa, hpa⟩ := SubgroupFunctor.mem_range.mp hap
  obtain ⟨pb, hpb⟩ := SubgroupFunctor.mem_range.mp hbp
  let m := (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have hlift : lift ua pa ≫ m = lift ub pb ≫ m := by
    simpa only [m, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      hua, hub, hpa, hpb] using hab
  have hpairs : lift ua pa = lift ub pb := (cancel_mono m).mp hlift
  have huab : ua = ub := by
    simpa only [lift_fst] using
      congrArg (fun q : X ⟶ U.X ⊗ P.X => q ≫ fst U.X P.X) hpairs
  have hpab : pa = pb := by
    simpa only [lift_snd] using
      congrArg (fun q : X ⟶ U.X ⊗ P.X => q ≫ snd U.X P.X) hpairs
  apply Prod.ext
  · apply Subtype.ext
    rw [← hua, ← hub, huab]
  · apply Subtype.ext
    rw [← hpa, ← hpb, hpab]

/-- In particular, a represented opposite-cell open immersion supplies
all-test injectivity. -/
theorem hasInjectiveOppositeCellMultiplication_of_openImmersion
    (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hopen : IsOpenImmersion
      ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left) :
    HasInjectiveOppositeCellMultiplication i ν := by
  let m := (fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)
  have : IsOpenImmersion m.left := hopen
  have : Mono m := Over.mono_of_mono_left m
  exact hasInjectiveOppositeCellMultiplication_of_mono i ν U P iU iP hU hP

variable [IsAffineHom G.X.hom]

set_option maxHeartbeats 600000 in
/-- Opposite-cell injectivity forces both factors of a normalizing point in
`U⁻ U` to commute with the whole torus, tested over arbitrary schemes. -/
theorem commute_unipotent_factors_of_normalizer_of_injectiveOppositeCell
    (hcell : HasInjectiveOppositeCellMultiplication i ν)
    (n : normalizerPoints i)
    (v : RationalPoint.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i)))
    (u : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i))
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = v * u)
    (X : Over (Spec (CommRingCat.of k))) (t : X ⟶ T.X) :
    Commute (G.constantPoint v X) (t ≫ i.hom.hom) ∧
      Commute (G.constantPoint u X) (t ≫ i.hom.hom) := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let s : X ⟶ G.X := t ≫ i.hom.hom
  let t' : X ⟶ T.X := t ≫ (CommGroupScheme.groupHom (normalizingAut i n).hom).hom.hom
  let s' : X ⟶ G.X := t' ≫ i.hom.hom
  let vX : X ⟶ G.X := G.constantPoint v X
  let uX : X ⟶ G.X := G.constantPoint u X
  let nX : X ⟶ G.X := G.constantPoint n X
  have hsZ : s ∈ (Dynamic.centralizer χ).carrier X :=
    torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν) X
      (range_le_torusCentralizer i X (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩))
  have hs'Z : s' ∈ (Dynamic.centralizer χ).carrier X :=
    torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν) X
      (range_le_torusCentralizer i X (SubgroupFunctor.mem_range.mpr ⟨t', rfl⟩))
  have hs'minus : s' ∈ (Dynamic.centralizer χminus).carrier X := by
    simpa only [Category.assoc] using torusCentralizer_le_dynamicCentralizer i
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom ν) X
      (range_le_torusCentralizer i X (SubgroupFunctor.mem_range.mpr ⟨t', rfl⟩))
  have hvX : vX ∈ (Dynamic.unipotent χminus).carrier X :=
    (Dynamic.unipotent χminus).constantPoint_mem X v.property
  have huX : uX ∈ (Dynamic.unipotent χ).carrier X :=
    (Dynamic.unipotent χ).constantPoint_mem X u.property
  have hnX : nX = vX * uX := by
    change G.constantPoint n X = G.constantPoint v X * G.constantPoint u X
    rw [hn, constantPoint_mul]
  have hσ : nX * s * nX⁻¹ = s' := by
    have h := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom)
      (isNormalizingPoint_normalizingAut i n)
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    exact h
  have hv' : s' * vX * s'⁻¹ ∈ (Dynamic.unipotent χminus).carrier X :=
    Dynamic.conj_mem_unipotent χminus
      (Dynamic.centralizer_le_parabolic χminus X hs'minus) hvX
  have hp' : s' * uX * s⁻¹ ∈ (Dynamic.parabolic χ).carrier X :=
    ((Dynamic.parabolic χ).carrier X).mul_mem
      (((Dynamic.parabolic χ).carrier X).mul_mem
        (Dynamic.centralizer_le_parabolic χ X hs'Z)
        (Dynamic.unipotent_le_parabolic χ X huX))
      (((Dynamic.parabolic χ).carrier X).inv_mem
        (Dynamic.centralizer_le_parabolic χ X hsZ))
  have hprod :
      (s' * vX * s'⁻¹) * (s' * uX * s⁻¹) = vX * uX := by
    calc
      _ = s' * (vX * uX) * s⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
      _ = (nX * s * nX⁻¹) * nX * s⁻¹ := by rw [← hnX, hσ]
      _ = nX := by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
      _ = vX * uX := hnX
  let a : (Dynamic.unipotent χminus).carrier X × (Dynamic.parabolic χ).carrier X :=
    (⟨s' * vX * s'⁻¹, hv'⟩, ⟨s' * uX * s⁻¹, hp'⟩)
  let b : (Dynamic.unipotent χminus).carrier X × (Dynamic.parabolic χ).carrier X :=
    (⟨vX, hvX⟩, ⟨uX, Dynamic.unipotent_le_parabolic χ X huX⟩)
  have hpairs : a = b := hcell X hprod
  have hvconj : s' * vX * s'⁻¹ = vX :=
    congrArg (fun z : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (z.1 : X ⟶ G.X)) hpairs
  have huconj : s' * uX * s⁻¹ = uX :=
    congrArg (fun z : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (z.2 : X ⟶ G.X)) hpairs
  have hlimu : Dynamic.HasLimit χ uX 1 := huX
  have hlims : Dynamic.HasLimit χ s s := Dynamic.hasLimit_of_mem_centralizer χ hsZ
  have hlims' : Dynamic.HasLimit χ s' s' := Dynamic.hasLimit_of_mem_centralizer χ hs'Z
  have hlim : Dynamic.HasLimit χ (s' * uX * s⁻¹) (s' * s⁻¹) := by
    simpa only [mul_one] using (hlims'.mul χ hlimu).mul χ (hlims.inv χ)
  have hss : s' = s := by
    have hu' : Dynamic.HasLimit χ (s' * uX * s⁻¹) 1 := by
      rw [huconj]
      exact hlimu
    have h := hlim.unique χ hu'
    exact mul_inv_eq_one.mp h
  rw [hss] at hvconj huconj
  exact ⟨((mul_inv_eq_iff_eq_mul).mp hvconj).symm,
    ((mul_inv_eq_iff_eq_mul).mp huconj).symm⟩

/-- The normalizer has trivial intersection with the product of the opposite
and original unipotent groups when opposite-cell multiplication is injective. -/
theorem normalizer_eq_one_of_injectiveOppositeCell
    (hcell : HasInjectiveOppositeCellMultiplication i ν)
    (n : normalizerPoints i)
    (v : RationalPoint.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i)))
    (u : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i))
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = v * u) :
    n = 1 := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hvZ : (v : Over.mk (𝟙 _) ⟶ G.X) ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := by
    apply (mem_torusCentralizer_base_iff i _).mpr
    apply hom_ext_points
    intro X t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    have hc := (commute_unipotent_factors_of_normalizer_of_injectiveOppositeCell
      i ν hcell n v u hn X t).1
    rw [hc.eq, mul_inv_cancel_right]
  have huZ : (u : Over.mk (𝟙 _) ⟶ G.X) ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := by
    apply (mem_torusCentralizer_base_iff i _).mpr
    apply hom_ext_points
    intro X t
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    have hc := (commute_unipotent_factors_of_normalizer_of_injectiveOppositeCell
      i ν hcell n v u hn X t).2
    rw [hc.eq, mul_inv_cancel_right]
  have hvminus : (v : Over.mk (𝟙 _) ⟶ G.X) ∈ (Dynamic.centralizer χminus).carrier
      (Over.mk (𝟙 _)) := by
    simpa only [Category.assoc] using
      torusCentralizer_le_dynamicCentralizer i
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
          CommGroupScheme.groupHom ν) _ hvZ
  have hvone : (v : Over.mk (𝟙 _) ⟶ G.X) = 1 :=
    Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χminus
      (fun _ _ _ _ hl hl' => hl.unique χminus hl') hvminus v.property
  have huone : (u : Over.mk (𝟙 _) ⟶ G.X) = 1 :=
    Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
      (fun _ _ _ _ hl hl' => hl.unique χ hl')
      (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν) _ huZ) u.property
  apply Subtype.ext
  change (n : Over.mk (𝟙 _) ⟶ G.X) = 1
  rw [hn, hvone, huone, one_mul]

/-- In an affine ambient group, every normalizing point that is a product
of opposite and original unipotent points is the identity. -/
theorem normalizer_eq_one_of_unipotent_product [IsAffine G.X.left]
    (n : normalizerPoints i)
    (v : RationalPoint.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i)))
    (u : RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i))
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) = v * u) :
    n = 1 :=
  normalizer_eq_one_of_injectiveOppositeCell i ν
    (hasInjectiveOppositeCellMultiplication_of_isAffine i ν) n v u hn

end Langlands.GroupScheme
