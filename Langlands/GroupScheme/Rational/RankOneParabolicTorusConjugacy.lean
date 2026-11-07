import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.SplitTorusCentralDifference
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy
import Langlands.GroupScheme.Dynamic.UnipotentTorusAction
import Langlands.GroupScheme.Rational.TorusUnipotenceProof
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Split tori inside a rank-one parabolic with descended conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Dynamic

/-- The actual limit in the ambient group of a homomorphism whose range lies in
the dynamic parabolic. -/
def parabolicLimitHomOfRange {S : Scheme.{u}} {D G P Z : GroupScheme S}
    [IsSeparated G.X.hom] {χ : (Gm S).toGrp ⟶ G}
    {iP : P ⟶ G} {iZ : Z ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (s : D ⟶ G) (hsP : SubgroupFunctor.range s ≤ parabolic χ) : D ⟶ G :=
  hP.factorHom s hsP ≫ limitGroupHom hP hZ ≫ iZ

end Dynamic

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T D : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (he : e.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)

include hi ha he hpos

/-- The actual parabolic limit of a split torus factors through the fixed maximal
split torus; its difference from the original map belongs to the contracting group
on every scheme test. -/
theorem exists_limit_factor_of_range_le_parabolic_descendedAction
    (s : D.toGrp ⟶ G) (hD : IsSplitTorus D.toGrp)
    (hsP : SubgroupFunctor.range s ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ∃ f : D.toGrp ⟶ T.toGrp,
      ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ D.X),
        (x ≫ s.hom.hom) * (x ≫ (f ≫ i).hom.hom)⁻¹ ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier V := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let sP := hP.factorHom s hsP
  let b := Dynamic.parabolicLimitHomOfRange hP hZ s hsP
  have hb : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ D.X),
      x ≫ b.hom.hom ∈ (torusCentralizer i).carrier V := by
    intro V x
    rw [← dynamicCentralizer_eq_torusCentralizer_of_descendedAction i hi.1.1 a ha e he ν
      (ne_of_gt hpos)]
    change (x ≫ sP.hom.hom ≫ (Dynamic.limitGroupHom hP hZ).hom.hom) ≫
      (Dynamic.Affine.centralizerHom χ).hom.hom ∈ (Dynamic.centralizer χ).carrier V
    exact (hZ.pointsEquiv V _).2
  obtain ⟨f, hf⟩ := hi.exists_factor_of_commute hD b (fun V x y => by
    simpa only [Category.id_comp] using hb V x V (𝟙 V) y)
  refine ⟨f, ?_⟩
  intro V x
  rw [hf]
  have hsp : x ≫ s.hom.hom =
      (hP.pointsEquiv V (x ≫ sP.hom.hom) : V ⟶ G.X) := by
    change x ≫ s.hom.hom = (x ≫ sP.hom.hom) ≫
      (Dynamic.Affine.parabolicHom χ).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hP.factorHom_comp]
  have hbp : x ≫ b.hom.hom =
      Dynamic.limit χ (hP.pointsEquiv V (x ≫ sP.hom.hom)) := by
    change ((x ≫ sP.hom.hom) ≫ (Dynamic.limitGroupHom hP hZ).hom.hom) ≫
      (Dynamic.Affine.centralizerHom χ).hom.hom = _
    exact Dynamic.limitGroupHom_comp hP hZ _
  rw [hsp, hbp]
  exact Dynamic.mul_inv_limit_mem_unipotent χ _

omit hpos in
/-- For an ambient maximal split torus the limiting character cannot vanish. -/
theorem limit_factor_character_ne_zero_of_descendedAction
    [Smooth G.X.hom] (s : D.toGrp ⟶ G) (hs : IsMaximalSplitTorus s)
    (f : D.toGrp ⟶ T.toGrp)
    (hf : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ D.X),
      (x ≫ s.hom.hom) * (x ≫ (f ≫ i).hom.hom)⁻¹ ∈
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier V) :
    f ≫ CommGroupScheme.groupHom a ≠ 0 := by
  intro hzero
  let χ := CommGroupScheme.groupHom ν ≫ i
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := Dynamic.Affine.unipotentHom χ
  have hj := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  let : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom := hc.isAffineHom
  let : IsAffine (Dynamic.Affine.unipotentScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom
  have hU := Dynamic.isUnipotent_of_torusActionUnipotence χ torusActionUnipotence hj hc
  have hsfi : s = f ≫ i :=
    Dynamic.splitTorus_eq_of_central_difference_unipotent hs.1.1 hU j
      (by change (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ)).IsRepresentedBy _
          rw [hj.2]
          exact hj) s (f ≫ i)
      (AutomorphicAction.isCentral_comp_of_character_eq_zero i a e he f hzero)
      (by intro V x
          change _ ∈ (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ)).carrier V
          rw [hj.2]
          exact hf V x)
  let : IsIso f := hs.2 T i hi.1 f hsfi.symm
  have hz : CommGroupScheme.groupHom a = 0 := by
    have h := congrArg (fun g => inv f ≫ g) hzero
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
      Limits.comp_zero] using h
  exact ha (congrArg Additive.ofMul hz)

/-- In the descended rank-one setting, any ambient maximal split torus contained
in the dynamic parabolic is conjugate to the fixed torus by a rational point of
its actual contracting subgroup. -/
theorem exists_unipotent_conjugacy_of_range_le_parabolic_descendedAction
    [Smooth G.X.hom] (s : D.toGrp ⟶ G) (hs : IsMaximalSplitTorus s)
    (hsP : SubgroupFunctor.range s ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      ∃ f : D.toGrp ⟶ T.toGrp, IsIso f ∧
        (f ≫ i) ≫ (G.innerIso u).hom = s := by
  obtain ⟨f, hf⟩ := exists_limit_factor_of_range_le_parabolic_descendedAction
    i hi a ha e he ν hpos s hs.1.1 hsP
  have hfnz := limit_factor_character_ne_zero_of_descendedAction
    i hi a ha e he ν s hs f hf
  let af : characterLattice D := Additive.ofMul (f ≫ CommGroupScheme.groupHom a)
  have haf : af ≠ 0 := by
    intro hzero
    exact hfnz (congrArg CommGroupScheme.groupHom hzero)
  obtain ⟨N, hN, ζ, hζ⟩ := hs.1.1.exists_pairing_eq_pos haf
  have hζpos : 0 < latticePairing D af ζ := by rw [hζ]; exact_mod_cast hN
  let nu2 : cocharacterLattice T := ζ ≫ Additive.ofMul f
  have hnu2 : 0 < latticePairing T a nu2 := by
    change 0 < gmEndEquiv k ((ζ ≫ Additive.ofMul f) ≫ a)
    rw [Category.assoc]
    exact hζpos
  let χ := CommGroupScheme.groupHom nu2 ≫ i
  let ψ := CommGroupScheme.groupHom ζ ≫ s
  have hU : Dynamic.unipotent χ =
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
    rw [dynamicUnipotent_eq_subgroup_of_descendedAction i hi.1.1 a ha e he nu2 hnu2,
      dynamicUnipotent_eq_subgroup_of_descendedAction i hi.1.1 a ha e he ν hpos]
  have hnuhom : CommGroupScheme.groupHom nu2 = CommGroupScheme.groupHom ζ ≫ f := rfl
  have hdiff : ψ.hom.hom * χ.hom.hom⁻¹ ∈
      (Dynamic.unipotent χ).carrier (Gm (Spec (CommRingCat.of k))).X := by
    rw [hU]
    simpa only [ψ, χ, hnuhom, Grp.comp_hom_hom, Category.assoc] using
      hf (Gm (Spec (CommRingCat.of k))).X (CommGroupScheme.groupHom ζ).hom.hom
  obtain ⟨u, hu, hconj⟩ := Dynamic.exists_unipotent_conj_of_mul_inv_mem χ ψ hdiff
  let E := G.innerIso u
  let s' := s ≫ E.inv
  have hζs : CommGroupScheme.groupHom ζ ≫ s' = χ := by
    change ψ ≫ E.inv = χ
    rw [← hconj]
    change (χ ≫ E.hom) ≫ E.inv = χ
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hZ : Dynamic.centralizer χ = torusCentralizer i :=
    dynamicCentralizer_eq_torusCentralizer_of_descendedAction i hi.1.1 a ha e he nu2
      (ne_of_gt hnu2)
  have hsZ : SubgroupFunctor.range s' ≤ torusCentralizer i := by
    rw [← hZ, ← hζs]
    exact range_le_centralizer_groupHom_comp s' ζ
  obtain ⟨f', hf'⟩ := hi.exists_factor_of_commute hs.1.1 s' (fun V x y => by
    have hz := hsZ V (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [Category.id_comp] using hz V (𝟙 V) y)
  have hs' : IsMaximalSplitTorus s' := hs.comp_iso E.symm
  refine ⟨u, ?_, f', hs'.2 T i hi.1 f' hf', ?_⟩
  · rw [← hU]
    exact hu
  · rw [hf']
    change (s ≫ E.inv) ≫ E.hom = s
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end RelativeRoot

end Langlands.GroupScheme
