import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.CocharacterTransport
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness

/-! # Translating a smooth chart over a strictly henselian DVR -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HenselianDvrSmoothTranslation

open Langlands.AlgebraicGeometry.PointTopology

/-- Ground-field translations of a nonempty open cover a smooth group over a separably
closed field, including points whose residue fields are inseparable extensions. -/
theorem exists_right_translate_mem {k : Type u} [Field k] [IsSepClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom]
    (U : G.X.left.Opens) (hU : (U : Set G.X.left).Nonempty) (x : G.X.left) :
    ∃ p : RationalPoint k G.X, (GrpObj.mulRight p).hom.left x ∈ U := by
  let K := G.X.left.residueField x
  let s := G.X.left.fromSpecResidueField x
  let : Algebra k K := (Spec.homEquiv (s ≫ G.X.hom)).hom.toAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : s ≫ G.X.hom = b := (Spec.homEquiv.symm_apply_apply _).symm
  let GK := (baseChange b).obj G
  let fst : GK.X.left ⟶ G.X.left := pullback.fst G.X.hom b
  let a₀ : Over.mk b ⟶ G.X := Over.homMk s hb
  let a : RationalPoint K GK.X := (baseChangeBasePointsEquiv b G).symm a₀
  let τ := FiniteIndexTransfer.leftMul GK a
  have : IsIso τ.left := inferInstanceAs (IsIso ((Over.forget _).map τ))
  let V : GK.X.left.Opens := τ.left ⁻¹ᵁ (fst ⁻¹ᵁ U)
  have hV : (V : Set GK.X.left).Nonempty := by
    obtain ⟨u, hu⟩ := hU
    have : Surjective b := ⟨fun z => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
    obtain ⟨z, hz⟩ := fst.surjective u
    obtain ⟨w, hw⟩ := τ.left.surjective z
    exact ⟨w, by change fst (τ.left w) ∈ U; rwa [hw, hz]⟩
  have hd : Dense (⋃ p : RationalPoint k G.X,
      Set.range ((geometricRationalPoint (K := K) G.X p).left)) :=
    hasDenseGeometricRationalPoints_of_hasDenseRationalPoints G.X
      (hasDenseRationalPoints_of_smooth_of_isSepClosed k G.X)
  obtain ⟨z, hz, hzV⟩ := hd.exists_mem_open V.isOpen hV
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨p, t, rfl⟩ := hz
  let pK : RationalPoint K GK.X := geometricRationalPoint (K := K) G.X p
  have hpK : (baseChangeBasePointsEquiv b G pK).left = b ≫ p.left := by
    rw [baseChangeBasePointsEquiv_left]
    simpa only [pK] using geometricRationalPoint_fst (K := K) G.X p
  have hmove : (pK ≫ τ).left ≫ fst = s ≫ (GrpObj.mulRight p).hom.left := by
    rw [← baseChangeBasePointsEquiv_left]
    have he : pK ≫ τ = a * pK := by
      rw [FiniteIndexTransfer.comp_leftMul]
      have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = 𝟙 _ := by
        apply Over.OverMorphism.ext
        rfl
      rw [hu, Category.id_comp]
    rw [he, map_mul, show baseChangeBasePointsEquiv b G a = a₀ from
      (baseChangeBasePointsEquiv b G).apply_symm_apply a₀]
    change (a₀ * baseChangeBasePointsEquiv b G pK).left =
      (a₀ ≫ (GrpObj.mulRight p).hom).left
    congr 1
    change a₀ * baseChangeBasePointsEquiv b G pK =
      a₀ ≫ ((𝟙 G.X) * (toUnit G.X ≫ p))
    rw [MonObj.comp_mul]
    simp only [Category.comp_id, comp_toUnit_assoc]
    congr 1
    apply Over.OverMorphism.ext
    exact hpK
  refine ⟨p, ?_⟩
  have he := congrArg (fun j : Spec (CommRingCat.of K) ⟶ G.X.left => j t) hmove
  have hst : s t = x := Scheme.fromSpecResidueField_apply _ _
  change fst (τ.left (pK.left t)) ∈ U at hzV
  change fst (τ.left (pK.left t)) = (GrpObj.mulRight p).hom.left (s t) at he
  rw [he, hst] at hzV
  exact hzV

/-- Over a henselian local ring with separably closed residue field, translations by
sections move every special-fibre point into an open meeting that fibre. -/
theorem exists_section_right_translate_mem {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom]
    (U : G.X.left.Opens)
    (hU : ∃ x ∈ U, G.X.hom x = IsLocalRing.closedPoint R)
    (x : G.X.left) (hx : G.X.hom x = IsLocalRing.closedPoint R) :
    ∃ σ : RationalPoint R G.X, (GrpObj.mulRight σ).hom.left x ∈ U := by
  let k := IsLocalRing.ResidueField R
  let b := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have hb : b (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    rw [show IsLocalRing.closedPoint k = (⟨⊥, inferInstance⟩ : PrimeSpectrum k) from
      Subsingleton.elim _ _]
    apply PrimeSpectrum.ext
    exact IsLocalRing.ker_residue (R := R)
  let GK := (baseChange b).obj G
  have : Smooth GK.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let fst : GK.X.left ⟶ G.X.left := pullback.fst G.X.hom b
  have hpoint : ∀ z : G.X.left, G.X.hom z = IsLocalRing.closedPoint R →
      ∃ w : GK.X.left, fst w = z := by
    intro z hz
    change z ∈ Set.range (pullback.fst G.X.hom b)
    rw [Scheme.Pullback.range_fst]
    exact ⟨IsLocalRing.closedPoint k, hb.trans hz.symm⟩
  let UK : GK.X.left.Opens := fst ⁻¹ᵁ U
  have hUK : (UK : Set GK.X.left).Nonempty := by
    obtain ⟨z, hzU, hzs⟩ := hU
    obtain ⟨w, hw⟩ := hpoint z hzs
    exact ⟨w, by change fst w ∈ U; rwa [hw]⟩
  obtain ⟨xK, hxK⟩ := hpoint x hx
  obtain ⟨p, hp⟩ := exists_right_translate_mem GK UK hUK xK
  let p₀ := baseChangeBasePointsEquiv b G p
  obtain ⟨s, hs, hbs⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      (IsLocalRing.residue_surjective (R := R)) G.X.hom p₀.left (Over.w p₀)
  let σ : RationalPoint R G.X := Over.homMk s hs
  let T := (Over.map b).obj GK.X
  let e := baseChangePointsEquiv b G GK.X
  let j : T ⟶ G.X := e (𝟙 GK.X)
  have hj : j.left = fst := by
    change 𝟙 _ ≫ fst = fst
    exact Category.id_comp _
  have hconst : e (toUnit GK.X ≫ p) = toUnit T ≫ σ := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left]
    change (GK.X.hom ≫ p.left) ≫ fst = (GK.X.hom ≫ b) ≫ s
    rw [Category.assoc, ← baseChangeBasePointsEquiv_left, ← hbs, Category.assoc]
  have he : e (GrpObj.mulRight p).hom = j ≫ (GrpObj.mulRight σ).hom := by
    change e ((𝟙 GK.X) * (toUnit GK.X ≫ p)) =
      j ≫ ((𝟙 G.X) * (toUnit G.X ≫ σ))
    rw [map_mul, hconst, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
  have hmove : (GrpObj.mulRight p).hom.left ≫ fst =
      fst ≫ (GrpObj.mulRight σ).hom.left := by
    rw [← baseChangePointsEquiv_left, he, Over.comp_left, hj]
  refine ⟨σ, ?_⟩
  have hh := congrArg (fun q : GK.X.left ⟶ G.X.left => q xK) hmove
  change fst ((GrpObj.mulRight p).hom.left xK) ∈ U at hp
  change fst ((GrpObj.mulRight p).hom.left xK) = (GrpObj.mulRight σ).hom.left (fst xK) at hh
  rw [hh, hxK] at hp
  exact hp

/-- Choose a section whose right translation moves a specified special-fibre point
into the supplied open. -/
def specialFibreTranslatingSection {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom]
    (U : G.X.left.Opens)
    (hU : ∃ x ∈ U, G.X.hom x = IsLocalRing.closedPoint R)
    (x : G.X.left) (hx : G.X.hom x = IsLocalRing.closedPoint R) :
    { σ : RationalPoint R G.X // (GrpObj.mulRight σ).hom.left x ∈ U } :=
  let H := exists_section_right_translate_mem G U hU x hx
  ⟨Classical.choose H, Classical.choose_spec H⟩

/-- A group homomorphism is smooth everywhere if it is smooth on its actual generic
base change and on an open chart meeting the special fibre of a smooth source. -/
theorem smooth_of_generic_and_chart {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))} [Smooth G.X.hom]
    (f : G ⟶ H)
    (hη : Smooth ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f).hom.hom.left)
    (U : G.X.left.Opens) (hU : ∃ x ∈ U, G.X.hom x = IsLocalRing.closedPoint R)
    (hchart : Smooth (U.ι ≫ f.hom.hom.left)) :
    Smooth f.hom.hom.left := by
  have := hchart
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let δ := pullback.fst G.X.hom b
  let δH := pullback.fst H.X.hom b
  let fK := ((baseChange b).map f).hom.hom.left
  have : Smooth fK := hη
  have : IsOpenImmersion b :=
    Langlands.AlgebraicGeometry.isOpenImmersion_spec_fractionRing_of_dvr R K
  have hgeneric : Smooth (δ ≫ f.hom.hom.left) := by
    have he : δ ≫ f.hom.hom.left = fK ≫ δH := by
      simp [δ, δH, fK, Over.pullback_map_left]
    rw [he]
    infer_instance
  have hgenopen : Smooth (δ.opensRange.ι ≫ f.hom.hom.left) := by
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac δ δ.opensRange.ι
      (by rw [Scheme.Opens.range_ι]; rfl), Category.assoc]
    infer_instance
  have htranslate (σ : RationalPoint R G.X) :
      Smooth (( (GrpObj.mulRight σ).hom.left ⁻¹ᵁ U).ι ≫ f.hom.hom.left) := by
    let tG := (GrpObj.mulRight σ).hom.left
    let tH := (GrpObj.mulRight (σ ≫ f.hom.hom)).hom.left
    have : IsIso tG := inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight σ).hom))
    have : IsIso tH :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight (σ ≫ f.hom.hom)).hom))
    have hcomm : tG ≫ f.hom.hom.left = f.hom.hom.left ≫ tH := by
      have he : (GrpObj.mulRight σ).hom ≫ f.hom.hom =
          f.hom.hom ≫ (GrpObj.mulRight (σ ≫ f.hom.hom)).hom := by
        change ((𝟙 G.X) * (toUnit G.X ≫ σ)) ≫ f.hom.hom =
          f.hom.hom ≫ ((𝟙 H.X) * (toUnit H.X ≫ (σ ≫ f.hom.hom)))
        rw [MonObj.mul_comp, MonObj.comp_mul]
        simp
      exact congrArg Over.Hom.left he
    have hs : Smooth ((((tG ⁻¹ᵁ U).ι ≫ f.hom.hom.left)) ≫ tH) := by
      rw [Category.assoc, ← hcomm, ← Category.assoc, ← morphismRestrict_ι,
        Category.assoc]
      infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Smooth) _ tH).mp hs
  have hlocal : ∀ x : G.X.left, ∃ V : G.X.left.Opens, x ∈ V ∧
      Smooth (V.ι ≫ f.hom.hom.left) := by
    intro x
    by_cases hx : G.X.hom x = IsLocalRing.closedPoint R
    · obtain ⟨σ, hσ⟩ := exists_section_right_translate_mem G U hU x hx
      exact ⟨(GrpObj.mulRight σ).hom.left ⁻¹ᵁ U, hσ, htranslate σ⟩
    · refine ⟨δ.opensRange, ?_, hgenopen⟩
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
      have := Langlands.AlgebraicGeometry.isLocalizationAway_fractionRing_of_dvr R K hπ
      change x ∈ Set.range (pullback.fst G.X.hom b)
      rw [Scheme.Pullback.range_fst]
      change G.X.hom x ∈ Set.range (PrimeSpectrum.comap (algebraMap R K))
      rw [PrimeSpectrum.localization_away_comap_range K π]
      have hxη := (Langlands.AlgebraicGeometry.FlatReducedDvrConnectedness.point_eq_generic_or_closed
        R (G.X.hom x)).resolve_right hx
      rw [hxη]
      change π ∉ (⊥ : Ideal R)
      simpa only [Ideal.mem_bot] using hπ.ne_zero
  let I := { V : G.X.left.Opens // Smooth (V.ι ≫ f.hom.hom.left) }
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun i : I => i.1)
  · apply eq_top_iff.mpr
    intro x _
    obtain ⟨V, hxV, hV⟩ := hlocal x
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
  · exact fun i => i.2

end Langlands.GroupScheme.HenselianDvrSmoothTranslation
