import Langlands.GroupScheme.Rational.SplitSeriesPointCount
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityReduction
import Langlands.GroupScheme.Rational.SmoothTorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-! # Dynamic contracting subgroups lie in the torus envelope over a finite field -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G H : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- A point of the contracting subgroup `U_G(χ)` that normalizes a closed subgroup containing
the image of `χ` lies in that subgroup: the map `t ↦ u χ(t) u⁻¹ χ(t)⁻¹` takes values in the
subgroup and extends to the affine line with value `u` at zero. -/
theorem mem_of_mem_unipotent_of_normalizes {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hχ : SubgroupFunctor.range χ ≤ F)
    {T : Over S} {u : T ⟶ G.X} (hu : u ∈ (unipotent χ).carrier T)
    (hnorm : ∀ (V : Over S) (a : V ⟶ T) (x : V ⟶ G.X), x ∈ F.carrier V →
      (a ≫ u) * x * (a ≫ u)⁻¹ ∈ F.carrier V) :
    u ∈ F.carrier T := by
  have : IsClosedImmersion j.hom.hom.left := hjc
  obtain ⟨e, he, he0⟩ := (unipotent χ).carrier T |>.inv_mem hu
  let e' : T ⊗ AffineLine.scheme S ⟶ G.X := (fst T (AffineLine.scheme S) ≫ u) * e
  let c : T ⊗ (Gm S).X ⟶ G.X := snd T (Gm S).X ≫ χ.hom.hom
  have hc : c ∈ F.carrier (T ⊗ (Gm S).X) := hχ _ ⟨snd T (Gm S).X, rfl⟩
  have hres : T ◁ AffineLine.unitInclusion S ≫ e' ∈ F.carrier (T ⊗ (Gm S).X) := by
    have h1 : T ◁ AffineLine.unitInclusion S ≫ e' =
        ((fst T (Gm S).X ≫ u) * c * (fst T (Gm S).X ≫ u)⁻¹) * c⁻¹ := by
      rw [MonObj.comp_mul, whiskerLeft_fst_assoc, he, orbit, GrpObj.comp_inv]
      group
      rfl
    rw [h1]
    exact (F.carrier _).mul_mem (hnorm _ (fst T (Gm S).X) c hc) ((F.carrier _).inv_mem hc)
  rw [← hj.2] at hres ⊢
  obtain ⟨k', hk'⟩ := hres
  obtain ⟨e'', he''⟩ := AffineLine.exists_lift_of_unitInclusion j.hom.hom e' k' hk'
  refine ⟨evalZero e'', ?_⟩
  change evalZero e'' ≫ j.hom.hom = u
  rw [← evalZero_comp, he'', evalZero_mul, evalZero_fst, he0, mul_one]

end Dynamic

section Field

variable {k : Type u} [Field k]

/-- The image of a cocharacter lies in the closed torus envelope. -/
theorem range_cocharacter_le_closedTorusEnvelope (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    SubgroupFunctor.range χ ≤ closedTorusEnvelope G := by
  obtain ⟨Z, j, f, hZ, hj, hf⟩ :=
    torusImageClosedTorusStatement k G (Gm (Spec (CommRingCat.of k))).toGrp
      isSplitTorus_gm.isTorus χ
  rw [← hf]
  exact (SubgroupFunctor.range_comp_le f j).trans (closedTorusEnvelope_containsTori G Z j hZ hj)

/-- A rational point of the contracting subgroup of a cocharacter lies in the closed torus
envelope, because rational points normalize the envelope. -/
theorem rational_mem_closedTorusEnvelope_of_mem_unipotent
    {G : GroupScheme (Spec (CommRingCat.of k))} (D : TorusGeneratedEnvelope G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ closedTorusEnvelope G)
    {u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hu : u ∈ (Dynamic.unipotent χ).carrier _) :
    u ∈ (closedTorusEnvelope G).carrier _ :=
  Dynamic.mem_of_mem_unipotent_of_normalizes χ D.represents D.closed hχ hu
    (fun V a x hx => by
      have h := (closedTorusEnvelope_eq_comap_iso (G.innerIso u)).le V hx
      change x ≫ (G.innerIso u).hom.hom.hom ∈ (closedTorusEnvelope G).carrier V at h
      rwa [comp_innerIso_hom, ← comp_eq_constantPoint a u] at h)

/-- Over a finite field, the contracting subgroup `U_G(χ)` of every cocharacter of a smooth
affine group lies in the closed envelope of all ground-field tori, on every test scheme. -/
theorem unipotent_le_closedTorusEnvelope [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.unipotent χ ≤ closedTorusEnvelope G := by
  let D := smoothTorusGeneratedEnvelope G
  have : Smooth D.group.X.hom := smoothTorusGeneratedEnvelope_smooth G
  have : IsAffineHom D.group.X.hom := D.closed.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine D.group.X.left := isAffine_of_isAffineHom D.group.X.hom
  have hχ := range_cocharacter_le_closedTorusEnvelope G χ
  let χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D.group := D.represents.factorHom χ hχ
  have hχ' : χ' ≫ D.inclusion = χ := D.represents.factorHom_comp χ hχ
  let iU := Dynamic.Affine.unipotentHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hUc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  let iV := Dynamic.Affine.unipotentHom χ'
  have hV := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hVc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ'
  have : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom := hUc.isAffineHom
  have : IsAffineHom (Dynamic.Affine.unipotentScheme χ').X.hom := hVc.isAffineHom
  have : Smooth (Dynamic.Affine.unipotentScheme χ).X.hom := (dynamicSmooth k G χ _ iU).2.2 hU
  have : Smooth (Dynamic.Affine.unipotentScheme χ').X.hom :=
    (dynamicSmooth k D.group χ' _ iV).2.2 hV
  have : ConnectedSpace (Dynamic.Affine.unipotentScheme χ).X.left :=
    (dynamicConnected k G χ _ iU).1 hU
  have : Mono iU.hom.hom := hU.1
  have hle : SubgroupFunctor.range (iV ≫ D.inclusion) ≤ Dynamic.unipotent χ := by
    rintro T _ ⟨y, rfl⟩
    have hy : y ≫ iV.hom.hom ∈ (Dynamic.unipotent χ').carrier T := by
      rw [← hV.2]
      exact ⟨y, rfl⟩
    have h : (y ≫ iV.hom.hom) ≫ D.inclusion.hom.hom ∈
        (Dynamic.unipotent (χ' ≫ D.inclusion)).carrier T :=
      Dynamic.unipotent_le_comap χ' D.inclusion T hy
    rw [hχ'] at h
    change y ≫ (iV ≫ D.inclusion).hom.hom ∈ (Dynamic.unipotent χ).carrier T
    rwa [Grp.comp_hom_hom, ← Category.assoc]
  let f := hU.factorHom (iV ≫ D.inclusion) hle
  have hf : f ≫ iU = iV ≫ D.inclusion := hU.factorHom_comp _ hle
  have hfc : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hUc (by rw [hf]; exact hVc.comp D.closed)
  have hiso : IsIso f := by
    refine RelativeRoot.isIso_of_surjective_rationalPoints f hfc
      (Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ' hV hVc)
      (Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ hU hUc) (fun u => ?_)
    have hu : u ≫ iU.hom.hom ∈ (Dynamic.unipotent χ).carrier _ := by
      rw [← hU.2]
      exact ⟨u, rfl⟩
    have hmem := rational_mem_closedTorusEnvelope_of_mem_unipotent D χ hχ hu
    rw [← D.represents.2] at hmem
    obtain ⟨d, hd⟩ := hmem
    change d ≫ D.inclusion.hom.hom = u ≫ iU.hom.hom at hd
    have hdU : d ∈ (Dynamic.unipotent χ').carrier _ := by
      rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ' D.inclusion D.closed]
      change d ≫ D.inclusion.hom.hom ∈ (Dynamic.unipotent (χ' ≫ D.inclusion)).carrier _
      rw [hχ', hd]
      exact hu
    rw [← hV.2] at hdU
    obtain ⟨v, hv⟩ := hdU
    change v ≫ iV.hom.hom = d at hv
    refine ⟨v, (cancel_mono iU.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hf, Grp.comp_hom_hom, ← Category.assoc, hv, hd]
  rw [← hU.2]
  have hiU : iU = inv f ≫ (f ≫ iU) := by rw [IsIso.inv_hom_id_assoc]
  calc SubgroupFunctor.range iU ≤ SubgroupFunctor.range (f ≫ iU) := by
        conv_lhs => rw [hiU]
        exact SubgroupFunctor.range_comp_le _ _
    _ = SubgroupFunctor.range (iV ≫ D.inclusion) := by rw [hf]
    _ ≤ SubgroupFunctor.range D.inclusion := SubgroupFunctor.range_comp_le _ _
    _ = closedTorusEnvelope G := D.represents.2

end Field

end Langlands.GroupScheme
