import Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Derived.EpiProductDetection
import Langlands.GroupScheme.Derived.SmoothnessProof
import Langlands.GroupScheme.Derived.ConnectednessProof
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # The multiplication map of a central torus and the derived subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoverPreimage

section General

variable {S : Scheme.{u}} {G D : GroupScheme S} {Z : CommGroupScheme S}

/-- The multiplication homomorphism `Z × D ⟶ G` of a central homomorphism `i` and an arbitrary
homomorphism `d`. -/
def centralProduct (i : Z.toGrp ⟶ G) (d : D ⟶ G) (hic : IsCentral i) : Z.toGrp ⊗ D ⟶ G :=
  prodHom i d (hic.commute_values d)

theorem comp_centralProduct (i : Z.toGrp ⟶ G) (d : D ⟶ G) (hic : IsCentral i)
    {T : Over S} (x : T ⟶ (Z.toGrp ⊗ D).X) :
    x ≫ (centralProduct i d hic).hom.hom =
      (x ≫ fst Z.X D.X ≫ i.hom.hom) * (x ≫ snd Z.X D.X ≫ d.hom.hom) := by
  rw [centralProduct, comp_prodHom]
  simp only [productPointsEquiv_fst, productPointsEquiv_snd, Category.assoc]

theorem centralProduct_hom (i : Z.toGrp ⟶ G) (d : D ⟶ G) (hic : IsCentral i) :
    (centralProduct i d hic).hom.hom = subgroupProductMap i d := by
  have h := comp_centralProduct i d hic (𝟙 _)
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at h
  exact h

/-- Kernel points of the central product are central. -/
theorem centralProduct_kernel_central (i : Z.toGrp ⟶ G) (d : D ⟶ G) (hic : IsCentral i)
    [Mono d.hom.hom] {T : Over S} (x : T ⟶ (Z.toGrp ⊗ D).X)
    (hx : x ≫ (centralProduct i d hic).hom.hom = 1) :
    x ∈ (center (Z.toGrp ⊗ D)).carrier T := by
  rw [comp_centralProduct] at hx
  have hy : x ≫ snd Z.X D.X ≫ d.hom.hom = (x ≫ fst Z.X D.X ≫ i.hom.hom)⁻¹ :=
    eq_inv_of_mul_eq_one_right hx
  have hyc : (x ≫ snd Z.X D.X) ≫ d.hom.hom ∈ (center G).carrier T := by
    rw [Category.assoc, hy, ← Category.assoc]
    exact inv_mem (hic T (x ≫ fst Z.X D.X))
  intro T' a w
  apply (productPointsEquiv Z.toGrp D T').injective
  rw [map_mul, map_mul]
  apply Prod.ext
  · simp only [Prod.fst_mul, productPointsEquiv_fst]
    exact mul_comm _ _
  · simp only [Prod.snd_mul, productPointsEquiv_snd]
    apply (cancel_mono d.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    have hc := hyc T' a (w ≫ snd Z.X D.X ≫ d.hom.hom)
    simpa only [Category.assoc] using hc.eq

/-- Restriction of the central product to the inverse image of a subgroup containing the
central factor. -/
def restrictedProduct (d : D ⟶ G) {M : GroupScheme S} (j : M ⟶ G)
    (iM : Z.toGrp ⟶ M) (hic : IsCentral iM) :
    Z.toGrp ⊗ subgroupIntersection d j ⟶ M :=
  centralProduct iM (subgroupIntersectionSnd d j) hic

/-- A factorization of a central homomorphism through a monomorphism is central. -/
theorem isCentral_of_comp_mono {M : GroupScheme S} {i : Z.toGrp ⟶ G} (hic : IsCentral i)
    (j : M ⟶ G) [Mono j.hom.hom] (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i) : IsCentral iM := by
  intro T x T' a w
  change (a ≫ x ≫ iM.hom.hom) * w = w * (a ≫ x ≫ iM.hom.hom)
  apply (cancel_mono j.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hc := hic T x T' a (w ≫ j.hom.hom)
  rw [← hiM, Grp.comp_hom_hom] at hc
  simpa only [Category.assoc] using hc.eq

/-- The restricted product is the base change of the central product along `j`. -/
theorem isCentralFppfCover_restrictedProduct (i : Z.toGrp ⟶ G) (d : D ⟶ G) (hic : IsCentral i)
    [Mono d.hom.hom] (hm : IsCentralFppfCover (centralProduct i d hic))
    {M : GroupScheme S} (j : M ⟶ G) [Mono j.hom.hom] (iM : Z.toGrp ⟶ M) (hiM : iM ≫ j = i) :
    IsCentralFppfCover (restrictedProduct d j iM (isCentral_of_comp_mono hic j iM hiM)) := by
  let hicM := isCentral_of_comp_mono hic j iM hiM
  let MD := subgroupIntersection d j
  let f₁ := subgroupIntersectionFst d j
  let f₂ := subgroupIntersectionSnd d j
  have hcond : f₁.hom.hom ≫ d.hom.hom = f₂.hom.hom ≫ j.hom.hom :=
    congrArg (fun r => r.hom.hom) (subgroupIntersection_condition d j)
  let hpb := subgroupIntersection_isPullback d j
  have : Mono f₁.hom.hom := hpb.mono_fst_of_mono
  let i₀ : Z.toGrp ⊗ MD ⟶ Z.toGrp ⊗ D := Z.toGrp ◁ f₁
  have hi₀ : i₀.hom.hom = Z.X ◁ f₁.hom.hom := rfl
  have hi₀fst : ∀ {T : Over S} (x : T ⟶ (Z.toGrp ⊗ MD).X),
      x ≫ i₀.hom.hom ≫ fst Z.X D.X = x ≫ fst Z.X MD.X := by
    intro T x
    rw [hi₀, whiskerLeft_fst]
  have hi₀snd : ∀ {T : Over S} (x : T ⟶ (Z.toGrp ⊗ MD).X),
      x ≫ i₀.hom.hom ≫ snd Z.X D.X = x ≫ snd Z.X MD.X ≫ f₁.hom.hom := by
    intro T x
    rw [hi₀, whiskerLeft_snd]
  have hi₀fst' : i₀.hom.hom ≫ fst Z.X D.X = fst Z.X MD.X := by
    rw [hi₀, whiskerLeft_fst]
  have hi₀snd' : i₀.hom.hom ≫ snd Z.X D.X = snd Z.X MD.X ≫ f₁.hom.hom := by
    rw [hi₀, whiskerLeft_snd]
  have hsq : i₀ ≫ centralProduct i d hic = restrictedProduct d j iM hicM ≫ j := by
    apply Grp.hom_ext
    apply yoneda.map_injective
    ext T x
    change x ≫ i₀.hom.hom ≫ (centralProduct i d hic).hom.hom =
      (x ≫ (restrictedProduct d j iM hicM).hom.hom) ≫ j.hom.hom
    rw [← Category.assoc x i₀.hom.hom, comp_centralProduct, restrictedProduct,
      comp_centralProduct, MonObj.mul_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hi₀fst', reassoc_of% hi₀snd', ← hiM, Grp.comp_hom_hom]
    rw [show f₁.hom.hom ≫ d.hom.hom = f₂.hom.hom ≫ j.hom.hom from hcond]
  have hmono : Mono i₀.hom.hom := by
    constructor
    intro T x y hxy
    apply (productPointsEquiv Z.toGrp MD T).injective
    apply Prod.ext
    · have h := congrArg (fun r => r ≫ fst Z.X D.X) hxy
      simp only [Category.assoc] at h
      rw [hi₀fst, hi₀fst] at h
      simpa only [productPointsEquiv_fst] using h
    · have h := congrArg (fun r => r ≫ snd Z.X D.X) hxy
      simp only [Category.assoc] at h
      rw [hi₀snd, hi₀snd, ← Category.assoc, ← Category.assoc] at h
      simpa only [productPointsEquiv_snd] using (cancel_mono f₁.hom.hom).mp h
  have hrep : ((SubgroupFunctor.range j).comap (centralProduct i d hic)).IsRepresentedBy i₀ := by
    refine ⟨hmono, ?_⟩
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y ≫ (restrictedProduct d j iM hicM).hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, ← hsq, Grp.comp_hom_hom, Category.assoc]
    · rintro ⟨m, hm⟩
      rw [comp_centralProduct] at hm
      let z := x ≫ fst Z.X D.X
      have e1 : z ≫ iM.hom.hom ≫ j.hom.hom = z ≫ i.hom.hom := by
        rw [← Grp.comp_hom_hom, hiM]
      have hd : (x ≫ snd Z.X D.X) ≫ d.hom.hom = ((z ≫ iM.hom.hom)⁻¹ * m) ≫ j.hom.hom := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc z, e1, hm]
        simp only [z, Category.assoc, inv_mul_cancel_left]
      let y : T ⟶ MD.X := hpb.lift (x ≫ snd Z.X D.X) ((z ≫ iM.hom.hom)⁻¹ * m) hd
      have hz : (productPointsEquiv Z.toGrp MD T).symm (z, y) ≫ fst Z.X MD.X = z :=
        congrArg Prod.fst ((productPointsEquiv Z.toGrp MD T).apply_symm_apply (z, y))
      have hy' : (productPointsEquiv Z.toGrp MD T).symm (z, y) ≫ snd Z.X MD.X = y :=
        congrArg Prod.snd ((productPointsEquiv Z.toGrp MD T).apply_symm_apply (z, y))
      refine ⟨(productPointsEquiv Z.toGrp MD T).symm (z, y), ?_⟩
      apply (productPointsEquiv Z.toGrp D T).injective
      apply Prod.ext
      · simp only [productPointsEquiv_fst, Category.assoc]
        rw [hi₀fst, hz]
      · simp only [productPointsEquiv_snd, Category.assoc]
        rw [hi₀snd, ← Category.assoc, hy']
        exact hpb.lift_fst _ _ _
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hpb' := (SubgroupFunctor.IsRepresentedBy.isPullback_of_comap_eq hrep hjrep
    (centralProduct i d hic) (restrictedProduct d j iM hicM) hsq rfl).map (Over.forget S)
  exact hm.of_isPullback i₀ _ j hsq hpb'

end General

section Field

variable {k : Type u} [Field k] {G D : GroupScheme (Spec (CommRingCat.of k))}
  {Z : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Basic geometry of the derived subgroup of a connected reductive group. -/
theorem derivedSubgroup_smooth_connected_affine (hG : IsConnectedReductive G) {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) :
    Smooth D.X.hom ∧ ConnectedSpace D.X.left ∧ IsAffineHom D.X.hom := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  exact ⟨derivedSubgroupSmoothness k G D d hd hG.smooth,
    derivedSubgroupConnectedness k G D d hd hG.connectedSpace,
    IsClosedSubgroup.isAffineHom hd.1⟩

/-- The central product of a closed central torus with the derived subgroup is a central fppf
cover as soon as its multiplication morphism is an epimorphism of schemes. -/
theorem isCentralFppfCover_centralProduct (hG : IsConnectedReductive G) {d : D ⟶ G}
    (hd : IsDerivedSubgroup d) {i : Z.toGrp ⟶ G} (hZ : IsTorus Z.toGrp)
    (hic : IsCentral i) (hi : IsClosedSubgroup i) [Epi (subgroupProductMap i d)] :
    IsCentralFppfCover (centralProduct i d hic) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hDs, hDc, hDa⟩ := derivedSubgroup_smooth_connected_affine hG hd
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffine Z.X.left := SplittingAssembly.isAffine_of_isTorus Z.toGrp hZ
  have hZa : IsAffineHom Z.X.hom := inferInstance
  have hZs : Smooth Z.X.hom := hZ.smooth
  have hZc : ConnectedSpace Z.X.left := hZ.connectedSpace
  obtain ⟨hAff, _, _, hInt⟩ := smoothConnectedAffineGeometry.2 k Z.toGrp D
    hZs hZa hZc hDs hDa hDc
  have : IsAffineHom (Z.X ⊗ D.X).hom := hAff
  have : GeometricallyIntegral (Z.X ⊗ D.X).hom := hInt
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : IrreducibleSpace (Z.X ⊗ D.X).left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (Z.X ⊗ D.X).hom
  have : ConnectedSpace (Z.toGrp ⊗ D).X.left := by
    change ConnectedSpace (Z.X ⊗ D.X).left
    infer_instance
  have : Smooth (Z.toGrp ⊗ D).X.hom := smooth_tensor Z.X D.X hZs hDs
  have : IsAffineHom (Z.toGrp ⊗ D).X.hom := hAff
  let m := centralProduct i d hic
  obtain ⟨I, inc, fac, hinc, hfac, hf, hs, hq, hl, -, -, -⟩ := HomImage.exists_image m
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have hmfac : fac.hom.hom ≫ inc.hom.hom = subgroupProductMap i d := by
    rw [← centralProduct_hom i d hic]
    change fac.hom.hom ≫ inc.hom.hom = m.hom.hom
    rw [← hfac]
    rfl
  have : Epi inc.hom.hom := by
    have : Epi (fac.hom.hom ≫ inc.hom.hom) := by
      rw [hmfac]
      infer_instance
    exact epi_of_epi fac.hom.hom inc.hom.hom
  have : IsIso inc.hom.hom := isIso_of_isClosedImmersion_of_epi_over inc.hom.hom
  have : IsIso inc.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map inc.hom.hom))
  have hm : m.hom.hom.left = fac.hom.hom.left ≫ inc.hom.hom.left := by
    rw [← hfac]
    rfl
  have : Flat fac.hom.hom.left := hf
  have : Surjective fac.hom.hom.left := hs
  have : QuasiCompact fac.hom.hom.left := hq
  have : LocallyOfFinitePresentation fac.hom.hom.left := hl
  obtain ⟨C, c, hc, hcrange, hcfin⟩ := derivedCentralIntersectionFiniteness k G D d hG hd
  have : IsClosedImmersion c.hom.hom.left := hc
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have : IsFinite C.X.hom := hcfin
  have hcd : IsCentral (c ≫ d) := by
    intro T w
    have hw : w ≫ c.hom.hom ∈ (SubgroupFunctor.range c).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨w, rfl⟩
    rw [hcrange, SubgroupFunctor.mem_comap] at hw
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hw
  have : Mono (c ≫ d).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have : IsCommMonObj C.X := hcd.isCommMonObj
  obtain ⟨N, hNpos, hN⟩ := exists_pow_eq_one_of_isFinite C
  refine ⟨?_, ?_, ?_, ?_, fun T x hx => centralProduct_kernel_central i d hic x hx,
    ⟨N, hNpos, ?_⟩⟩
  · change QuasiCompact m.hom.hom.left
    rw [hm]
    infer_instance
  · change Flat m.hom.hom.left
    rw [hm]
    infer_instance
  · change Surjective m.hom.hom.left
    rw [hm]
    infer_instance
  · change LocallyOfFinitePresentation m.hom.hom.left
    rw [hm]
    infer_instance
  · intro T x hx
    rw [comp_centralProduct] at hx
    have hy : x ≫ snd Z.X D.X ≫ d.hom.hom = (x ≫ fst Z.X D.X ≫ i.hom.hom)⁻¹ :=
      eq_inv_of_mul_eq_one_right hx
    have hyc : (x ≫ snd Z.X D.X) ≫ d.hom.hom ∈ (center G).carrier T := by
      rw [Category.assoc, hy, ← Category.assoc]
      exact inv_mem (hic T (x ≫ fst Z.X D.X))
    have hyr : x ≫ snd Z.X D.X ∈ (SubgroupFunctor.range c).carrier T := by
      rw [hcrange, SubgroupFunctor.mem_comap]
      exact hyc
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hyr
    have hyN : (x ≫ snd Z.X D.X) ^ N = 1 := by
      rw [← hw, ← MonObj.pow_comp, hN T w, MonObj.one_comp]
    have hzN : (x ≫ fst Z.X D.X) ^ N = 1 := by
      apply (cancel_mono i.hom.hom).mp
      rw [MonObj.pow_comp, MonObj.one_comp, Category.assoc, ← inv_inv
        (x ≫ fst Z.X D.X ≫ i.hom.hom), ← hy, inv_pow, ← Category.assoc, ← MonObj.pow_comp,
        hyN, MonObj.one_comp, inv_one]
    apply (productPointsEquiv Z.toGrp D T).injective
    rw [map_pow, map_one]
    apply Prod.ext
    · simpa only [Prod.pow_fst, productPointsEquiv_fst, Prod.fst_one] using hzN
    · simpa only [Prod.pow_snd, productPointsEquiv_snd, Prod.snd_one] using hyN

end Field

end Langlands.GroupScheme.CoverPreimage
