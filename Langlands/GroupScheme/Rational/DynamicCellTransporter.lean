import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Conjugates of a subgroup through the opposite open cell -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Let `F` be a closed subgroup of a smooth connected affine group `G` containing both
contracting subgroups `U_G(χ)` and `U_G(χ⁻¹)` of a cocharacter `χ`. If the centralizer
`Z_G(χ)` conjugates the image of a homomorphism `i : E ⟶ G` from a smooth group into `F`,
then every point of `G` conjugates it into `F`, on every test scheme. -/
theorem conj_mem_of_centralizer_conj_mem [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {F : SubgroupFunctor G} {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hU : unipotent χ ≤ F)
    (hU' : unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)
      ≤ F)
    {E : GroupScheme (Spec (CommRingCat.of k))} [Smooth E.X.hom] (i : E ⟶ G)
    (hZ : ∀ (T : Over (Spec (CommRingCat.of k))) (z x : T ⟶ G.X),
      z ∈ (centralizer χ).carrier T → x ∈ (SubgroupFunctor.range i).carrier T →
        z * x * z⁻¹ ∈ F.carrier T)
    (T : Over (Spec (CommRingCat.of k))) (g x : T ⟶ G.X)
    (hx : x ∈ (SubgroupFunctor.range i).carrier T) :
    g * x * g⁻¹ ∈ F.carrier T := by
  let W : Over (Spec (CommRingCat.of k)) := G.X ⊗ E.X
  let c : W ⟶ G.X := fst G.X E.X * (snd G.X E.X ≫ i.hom.hom) * (fst G.X E.X)⁻¹
  suffices hc : c ∈ F.carrier W by
    obtain ⟨t, rfl⟩ := hx
    change g * (t ≫ i.hom.hom) * g⁻¹ ∈ F.carrier T
    have h := F.comp_mem (lift g t) hc
    simpa only [c, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc] using h
  let χ' := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let iU := Affine.unipotentHom χ'
  let iP := Affine.parabolicHom χ
  have hUrep := Affine.isRepresentedBy_unipotentHom χ'
  have hPrep := Affine.isRepresentedBy_parabolicHom χ
  let m : (Affine.unipotentScheme χ').X ⊗ (Affine.parabolicScheme χ).X ⟶ G.X :=
    (fst _ _ ≫ iU.hom.hom) * (snd _ _ ≫ iP.hom.hom)
  have : IsOpenImmersion m.left := oppositeCellStatement k G χ _ _ iU iP hUrep hPrep
  let Ω : G.X.left.Opens := m.left.opensRange
  let V : W.left.Opens := (fst G.X E.X).left ⁻¹ᵁ Ω
  have hV : c.left '' (V : Set W.left) ⊆ Set.range j.hom.hom.left := by
    rintro _ ⟨w, hw, rfl⟩
    let TV : Over (Spec (CommRingCat.of k)) := Over.mk (V.ι ≫ W.hom)
    let a : TV ⟶ W := Over.homMk V.ι rfl
    have hrange : Set.range (a ≫ fst G.X E.X).left ⊆ Set.range m.left := by
      rintro _ ⟨v, rfl⟩
      exact v.2
    let l := FiniteEtaleImage.liftOver m (a ≫ fst G.X E.X) hrange
    have hl : l ≫ m = a ≫ fst G.X E.X := FiniteEtaleImage.liftOver_fac _ _ _
    let um : TV ⟶ G.X := l ≫ fst _ _ ≫ iU.hom.hom
    let p : TV ⟶ G.X := l ≫ snd _ _ ≫ iP.hom.hom
    have hgp : a ≫ fst G.X E.X = um * p := by
      rw [← hl, MonObj.comp_mul]
    have hum : um ∈ F.carrier TV := by
      apply hU'
      rw [← hUrep.2]
      exact ⟨l ≫ fst _ _, by
        change (l ≫ fst _ _) ≫ iU.hom.hom = l ≫ fst _ _ ≫ iU.hom.hom
        rw [Category.assoc]⟩
    have hp : p ∈ (parabolic χ).carrier TV := by
      rw [← hPrep.2]
      exact ⟨l ≫ snd _ _, by
        change (l ≫ snd _ _) ≫ iP.hom.hom = l ≫ snd _ _ ≫ iP.hom.hom
        rw [Category.assoc]⟩
    obtain ⟨z, hz⟩ := exists_hasLimit χ hp
    have hzc : z ∈ (centralizer χ).carrier TV := hz.mem_centralizer χ
    have hu : p * z⁻¹ ∈ (unipotent χ).carrier TV := by
      change HasLimit χ (p * z⁻¹) 1
      simpa only [mul_inv_cancel] using hz.mul χ ((hasLimit_of_mem_centralizer χ hzc).inv χ)
    have hx' : a ≫ snd G.X E.X ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier TV :=
      ⟨a ≫ snd G.X E.X, by
        change (a ≫ snd G.X E.X) ≫ i.hom.hom = a ≫ snd G.X E.X ≫ i.hom.hom
        rw [Category.assoc]⟩
    have hconj : a ≫ c ∈ F.carrier TV := by
      have hd : um * (p * z⁻¹) ∈ F.carrier TV := (F.carrier TV).mul_mem hum (hU _ hu)
      have heq : a ≫ c = (um * (p * z⁻¹)) * (z * (a ≫ snd G.X E.X ≫ i.hom.hom) * z⁻¹) *
          (um * (p * z⁻¹))⁻¹ := by
        simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hgp]
        group
      rw [heq]
      exact (F.carrier TV).mul_mem ((F.carrier TV).mul_mem hd (hZ _ _ _ hzc hx'))
        ((F.carrier TV).inv_mem hd)
    rw [← hj.2] at hconj
    obtain ⟨y, hy⟩ := hconj
    change y ≫ j.hom.hom = a ≫ c at hy
    refine ⟨y.left ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun q : TV ⟶ G.X => q.left ⟨w, hw⟩) hy
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [h]
    rfl
  have hΩ : Dense (Ω : Set G.X.left) := by
    have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (Affine.unipotentScheme χ').X ⊗ (Affine.parabolicScheme χ).X :=
      lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Affine.unipotentScheme χ').X)
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Affine.parabolicScheme χ).X)
    exact Ω.isOpen.dense ⟨_, ⟨e.left (IsLocalRing.closedPoint k), rfl⟩⟩
  have : Flat (fst G.X E.X).left := by
    change Flat (pullback.fst G.X.hom E.X.hom)
    infer_instance
  have : LocallyOfFinitePresentation (fst G.X E.X).left := by
    change LocallyOfFinitePresentation (pullback.fst G.X.hom E.X.hom)
    infer_instance
  have : UniversallyOpen (fst G.X E.X).left := UniversallyOpen.of_flat _
  have hVd : Dense (V : Set W.left) := hΩ.preimage (fst G.X E.X).left.isOpenMap
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hclosed : IsClosed (c.left ⁻¹' Set.range j.hom.hom.left) :=
    j.hom.hom.left.isClosedEmbedding.isClosed_range.preimage c.left.continuous
  have hall : Set.range c.left ⊆ Set.range j.hom.hom.left := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure (V : Set W.left) := by
      rw [hVd.closure_eq]
      exact Set.mem_univ w
    exact closure_minimal (fun v (hv : v ∈ (V : Set W.left)) =>
      (hV ⟨v, hv, rfl⟩ : c.left v ∈ Set.range j.hom.hom.left)) hclosed hw
  have : Smooth W.hom := by
    rw [← Over.w (fst G.X E.X)]
    have : Smooth (fst G.X E.X).left := by
      change Smooth (pullback.fst G.X.hom E.X.hom)
      infer_instance
    infer_instance
  have : IsReduced W.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k W.left W.hom
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset j.hom.hom.left c.left hall
  rw [← hj.2]
  refine ⟨Over.homMk l (by rw [← Over.w j.hom.hom, ← Category.assoc, hl, Over.w c]), ?_⟩
  exact Over.OverMorphism.ext hl

end Dynamic

end Langlands.GroupScheme
