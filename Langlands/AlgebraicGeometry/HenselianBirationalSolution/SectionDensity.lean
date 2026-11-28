import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Density
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting
import Langlands.AlgebraicGeometry.SmoothDvrFibreGenericPoints
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Density of sections over a strictly henselian discrete valuation ring

Let `R` be a henselian discrete valuation ring with separably closed residue field and
`f : Y ⟶ Spec R` smooth and surjective. For every scheme `P` over `Spec R`, every open subset
`Z` of `Y ×_R P` which is dense in the fibres of the projection to `P`, and every point `p` of
`P`, some section `c` of `f` satisfies `(c, id)(p) ∈ Z`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

/-- A point of `Y ×_B P` whose first projection lies on a section `c` is the image of its second
projection under the base change of `c`. -/
theorem eq_lift_of_fst_mem_range {Y P B : Scheme.{u}} (f : Y ⟶ B) (g : P ⟶ B) (c : B ⟶ Y)
    (hc : c ≫ f = 𝟙 B) (z : ↥(pullback f g)) (hz : pullback.fst f g z ∈ Set.range c) :
    z = pullback.lift (g ≫ c) (𝟙 P) (by rw [Category.assoc, hc, Category.comp_id,
      Category.id_comp]) (pullback.snd f g z) := by
  obtain ⟨b, hb⟩ := hz
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := c)
    (g := pullback.fst f g) b z hb
  set σ := pullback.snd c (pullback.fst f g)
  set τ := σ ≫ pullback.snd f g
  have h1 : pullback.fst c (pullback.fst f g) = τ ≫ g := by
    calc pullback.fst c (pullback.fst f g) = pullback.fst c (pullback.fst f g) ≫ c ≫ f := by
          rw [hc, Category.comp_id]
      _ = σ ≫ pullback.fst f g ≫ f := by
          rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = τ ≫ g := by rw [pullback.condition, ← Category.assoc]
  have hlift : σ = τ ≫ pullback.lift (g ≫ c) (𝟙 P) (by rw [Category.assoc, hc,
      Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← pullback.condition, h1, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [← hw₂, hlift, Scheme.Hom.comp_apply]
  congr 1
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

/-- The image in `Y` of an open subset of the fibre of `Y ×_B P ⟶ P` over a point `p` is open in
the fibre of `Y ⟶ B` over the image of `p`. -/
theorem exists_isOpen_inter_preimage_eq_image {Y P B : Scheme.{u}} (f : Y ⟶ B) (g : P ⟶ B)
    (p : P) (Z : Set ↥(pullback f g)) (hZ : IsOpen Z) :
    ∃ O : Set Y, IsOpen O ∧
      O ∩ f ⁻¹' {g p} = pullback.fst f g '' (Z ∩ pullback.snd f g ⁻¹' {p}) := by
  have h := IsPullback.of_hasPullback f g
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h p
  have hφι0 : ∀ e₁ e₂, pullback.map (pullback.snd f g) (P.fromSpecResidueField p) f
      (B.fromSpecResidueField (g p)) (pullback.fst f g) (Spec.map (g.residueFieldMap p)) g
      e₁ e₂ ≫ f.fiberι (g p) = (pullback.snd f g).fiberι p ≫ pullback.fst f g :=
    fun _ _ => pullback.lift_fst _ _ _
  set φ : (pullback.snd f g).fiber p ⟶ f.fiber (g p) := pullback.map (pullback.snd f g)
      (P.fromSpecResidueField p) f (B.fromSpecResidueField (g p)) (pullback.fst f g)
      (Spec.map (g.residueFieldMap p)) g h.w.symm (by simp) with hφdef
  have hφι : φ ≫ f.fiberι (g p) = (pullback.snd f g).fiberι p ≫ pullback.fst f g :=
    hφι0 _ _
  have : UniversallyOpen φ := MorphismProperty.of_isPullback hpb.flip inferInstance
  set ι := (pullback.snd f g).fiberι p
  let ZE : Set ((pullback.snd f g).fiber p) := ι ⁻¹' Z
  have hZE : IsOpen ZE := hZ.preimage ι.continuous
  have hφZE : IsOpen (φ '' ZE) := φ.isOpenMap _ hZE
  obtain ⟨O, hO, hOeq⟩ := (f.fiberι (g p)).isEmbedding.isInducing.isOpen_iff.mp hφZE
  refine ⟨O, hO, ?_⟩
  ext y
  constructor
  · rintro ⟨hyO, hyf⟩
    rw [← Scheme.Hom.range_fiberι] at hyf
    obtain ⟨e, rfl⟩ := hyf
    have he : e ∈ φ '' ZE := by rw [← hOeq]; exact hyO
    obtain ⟨z, hz, rfl⟩ := he
    refine ⟨ι z, ⟨hz, ?_⟩, ?_⟩
    · have := ((pullback.snd f g).fiberHomeo p z).2
      exact this
    · rw [← Scheme.Hom.comp_apply, ← hφι, Scheme.Hom.comp_apply]
  · rintro ⟨z, ⟨hzZ, hzp⟩, rfl⟩
    have hzr : z ∈ Set.range ι := by rw [Scheme.Hom.range_fiberι]; exact hzp
    obtain ⟨e, rfl⟩ := hzr
    refine ⟨?_, ?_⟩
    · have : f.fiberι (g p) (φ e) ∈ O := by
        change φ e ∈ f.fiberι (g p) ⁻¹' O
        rw [hOeq]
        exact ⟨e, hzZ, rfl⟩
      rwa [← Scheme.Hom.comp_apply, hφι, Scheme.Hom.comp_apply] at this
    · change f (pullback.fst f g (ι e)) = g p
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact congrArg g hzp

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The generic point of the spectrum of a discrete valuation ring. -/
abbrev genericPt (R : Type u) [CommRing R] [IsDomain R] : Spec (CommRingCat.of R) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)

theorem genericPt_ne_closedPoint : genericPt R ≠ IsLocalRing.closedPoint R := by
  intro h
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal h).symm

theorem eq_genericPt_or_closedPoint (s : Spec (CommRingCat.of R)) :
    s = genericPt R ∨ s = IsLocalRing.closedPoint R :=
  SmoothDvrAffineOpenGeometry.point_eq_generic_or_closed R s

/-- The generic point specializes to every point. -/
theorem genericPt_specializes (s : Spec (CommRingCat.of R)) : genericPt R ⤳ s :=
  (PrimeSpectrum.le_iff_specializes (R := R) ⟨⊥, Ideal.isPrime_bot⟩ s).mp bot_le

/-- A point specializing to the generic point is the generic point. -/
theorem eq_genericPt_of_specializes {s : Spec (CommRingCat.of R)} (h : s ⤳ genericPt R) :
    s = genericPt R := by
  have h' := (PrimeSpectrum.le_iff_specializes (R := R) s ⟨⊥, Ideal.isPrime_bot⟩).mpr h
  exact PrimeSpectrum.ext (le_bot_iff.mp h')

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Every open subset meeting the special fibre of a smooth scheme over a henselian discrete
valuation ring with separably closed residue field contains the reduction of a section. -/
theorem exists_section_closedPoint_mem {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [Smooth f] (O : Set Y) (hO : IsOpen O) (hOs : ∃ y ∈ O, f y = IsLocalRing.closedPoint R) :
    ∃ c : Spec (CommRingCat.of R) ⟶ Y, c ≫ f = 𝟙 _ ∧ c (IsLocalRing.closedPoint R) ∈ O := by
  let k := IsLocalRing.ResidueField R
  let b := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have hb : ∀ t : Spec (CommRingCat.of k), b t = IsLocalRing.closedPoint R := by
    intro t
    rw [show t = (⟨⊥, inferInstance⟩ : PrimeSpectrum k) from Subsingleton.elim _ _]
    apply PrimeSpectrum.ext
    exact IsLocalRing.ker_residue (R := R)
  have : Smooth (pullback.snd f b) := inferInstance
  let X : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd f b)
  have : Smooth X.hom := inferInstanceAs (Smooth (pullback.snd f b))
  have hd := PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed k X
  let OF : Set X.left := pullback.fst f b ⁻¹' O
  have hOF : IsOpen OF := hO.preimage (pullback.fst f b).continuous
  have hOFne : OF.Nonempty := by
    obtain ⟨y, hyO, hys⟩ := hOs
    have hy : y ∈ Set.range (pullback.fst f b) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint k, (hb _).trans hys.symm⟩
    obtain ⟨w, rfl⟩ := hy
    exact ⟨w, hyO⟩
  obtain ⟨z, hzD, hzO⟩ := hd.exists_mem_open hOF hOFne
  simp only [Set.mem_iUnion, Set.mem_range] at hzD
  obtain ⟨q, t, rfl⟩ := hzD
  let q' : Spec (CommRingCat.of k) ⟶ Y := q.left ≫ pullback.fst f b
  have hq' : q' ≫ f = b ≫ 𝟙 _ := by
    have hw : q.left ≫ X.hom = 𝟙 _ := Over.w q
    change (q.left ≫ pullback.fst f b) ≫ f = b ≫ 𝟙 _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (q.left ≫ X.hom) ≫ b = b ≫ 𝟙 _
    rw [hw, Category.id_comp, Category.comp_id]
  obtain ⟨c, hc, hcq⟩ := PointTopology.exists_smooth_lift_of_residue_point
    (R := R) (K := k) IsLocalRing.residue_surjective f (𝟙 _) q' hq'
  refine ⟨c, hc, ?_⟩
  have : c (b t) = q' t := by rw [← Scheme.Hom.comp_apply, hcq]
  rw [← hb t, this]
  exact hzO

/-- The points of the generic fibre lying on sections. -/
def sectionGenericPoints {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) : Set Y :=
  {y | ∃ c : Spec (CommRingCat.of R) ⟶ Y, c ≫ f = 𝟙 _ ∧ c (genericPt R) = y}

/-- A generic point `ζ` of the special fibre of a smooth scheme over a henselian discrete
valuation ring with separably closed residue field has a generization `ξ` in the generic fibre;
`ξ` is a generic point of the scheme and lies in the closure of the generic points of the
sections. -/
theorem exists_generic_mem_closure_sectionGenericPoints {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (ζ : Y) (hζ : f ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Y, y ⤳ ζ → f y = IsLocalRing.closedPoint R → y = ζ) :
    ∃ ξ : Y, ξ ⤳ ζ ∧ f ξ = genericPt R ∧ (∀ y : Y, y ⤳ ξ → y = ξ) ∧
      ξ ∈ closure (sectionGenericPoints f) := by
  obtain ⟨hdom, hdvr⟩ := Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R f ζ hζ hgen
  set ξ₀ := Y.fromSpecStalk ζ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Y.presheaf.stalk ζ))
  have hgz : ∀ y, y ⤳ ζ → y = ζ ∨ y = ξ₀ := by
    intro y hy
    have hyr : y ∈ Set.range (Y.fromSpecStalk ζ) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    obtain ⟨q, rfl⟩ := hyr
    by_cases hq : q.asIdeal = ⊥
    · right
      congr 1
      exact PrimeSpectrum.ext hq
    · left
      have := q.isPrime
      have : q.asIdeal.IsMaximal := IsPrime.to_maximal_ideal hq
      have hq' : q = IsLocalRing.closedPoint _ :=
        PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal this)
      rw [hq']
      exact Scheme.fromSpecStalk_closedPoint
  have hflat : GeneralizingMap f := Flat.generalizingMap f
  obtain ⟨ξ, hξζ, hfξ⟩ := hflat (show genericPt R ⤳ f ζ from genericPt_specializes _)
  have hξne : ξ ≠ ζ := by
    intro h
    rw [h, hζ] at hfξ
    exact genericPt_ne_closedPoint hfξ.symm
  have hξ0 : ξ = ξ₀ := (hgz ξ hξζ).resolve_left hξne
  have hmax : ∀ y, y ⤳ ξ → y = ξ := by
    intro y hy
    rcases hgz y (hy.trans hξζ) with h | h
    · exfalso
      have hspec : f y ⤳ f ξ := hy.map f.continuous
      rw [h, hζ, hfξ] at hspec
      exact genericPt_ne_closedPoint (eq_genericPt_of_specializes hspec).symm
    · rw [h, hξ0]
  refine ⟨ξ, hξζ, hfξ, hmax, ?_⟩
  set A := sectionGenericPoints f with hA
  have hζcl : ζ ∈ closure A := by
    rw [mem_closure_iff]
    intro N hN hζN
    obtain ⟨c, hc, hcN⟩ := exists_section_closedPoint_mem f N hN ⟨ζ, hζN, hζ⟩
    refine ⟨c (genericPt R), ?_, c, hc, rfl⟩
    exact hN.stableUnderGeneralization ((genericPt_specializes _).map c.continuous) hcN
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨_, ⟨W, hW, rfl⟩, hζW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ζ) isOpen_univ
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
  have : QuasiSober W := W.isOpenEmbedding'.quasiSober
  have hcl := W.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val A
  let AW : Set W := Subtype.val ⁻¹' A
  obtain ⟨T, hTfin, hTcl, hTirr, hCeq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := AW))
  set T' := {t ∈ T | (t ∩ AW).Nonempty} with hT'
  have hAW : AW ⊆ ⋃₀ T' := by
    intro a ha
    have haC : a ∈ ⋃₀ T := hCeq ▸ subset_closure ha
    obtain ⟨t, htT, hat⟩ := Set.mem_sUnion.mp haC
    exact Set.mem_sUnion.mpr ⟨t, ⟨htT, a, hat, ha⟩, hat⟩
  have hT'closed : IsClosed (⋃₀ T') :=
    (hTfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hTcl t ht.1
  have hζC : (⟨ζ, hζW⟩ : W) ∈ closure AW := by
    change _ ∈ closure (Subtype.val ⁻¹' A)
    rw [← hcl]
    exact hζcl
  obtain ⟨t, ⟨htT, a, haT, haA⟩, hζt⟩ :=
    Set.mem_sUnion.mp (closure_minimal hAW hT'closed hζC)
  obtain ⟨v, hv⟩ := QuasiSober.sober (hTirr t htT) (hTcl t htT)
  have hvζ : v.1 ⤳ ζ := (hv.specializes hζt).map continuous_subtype_val
  have hva : v.1 ⤳ a.1 := (hv.specializes haT).map continuous_subtype_val
  have hfv : f v.1 = genericPt R := by
    obtain ⟨c, hc, hca⟩ := haA
    have hspec : f v.1 ⤳ f a.1 := hva.map f.continuous
    rw [← hca, ← Scheme.Hom.comp_apply, hc] at hspec
    exact eq_genericPt_of_specializes hspec
  have hvξ : v.1 = ξ := by
    rcases hgz v.1 hvζ with h | h
    · exfalso
      rw [h, hζ] at hfv
      exact genericPt_ne_closedPoint hfv.symm
    · rw [h, hξ0]
  have hvC : v ∈ closure AW := hCeq ▸ Set.mem_sUnion_of_mem hv.mem htT
  rw [← hvξ]
  have hv' : v ∈ Subtype.val ⁻¹' closure A := by
    rw [hcl]
    exact hvC
  exact hv'

/-- **Density of sections.** Let `R` be a henselian discrete valuation ring with separably
closed residue field and `f : Y ⟶ Spec R` smooth and surjective. If `Z` is an open subset of
`Y ×_R P` which is dense in the fibres of the projection to `P`, then for every point `p` of `P`
some section `c` of `f` maps `p` into `Z` under `(c, id) : P ⟶ Y ×_R P`. -/
theorem exists_section_lift_mem {Y P : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [Surjective f] (g : P ⟶ Spec (CommRingCat.of R)) (Z : Set ↥(pullback f g)) (hZo : IsOpen Z)
    (hZ : FibreGenerizationDense (pullback.snd f g) Z) (p : P) :
    ∃ c : Spec (CommRingCat.of R) ⟶ Y, ∃ hc : c ≫ f = 𝟙 _,
      pullback.lift (g ≫ c) (𝟙 P) (by rw [Category.assoc, hc, Category.comp_id,
        Category.id_comp]) p ∈ Z := by
  obtain ⟨O, hO, hOeq⟩ := exists_isOpen_inter_preimage_eq_image f g p Z hZo
  suffices h : ∃ c : Spec (CommRingCat.of R) ⟶ Y, c ≫ f = 𝟙 _ ∧ c (g p) ∈ O by
    obtain ⟨c, hc, hcO⟩ := h
    have hmem : c (g p) ∈ O ∩ f ⁻¹' {g p} := by
      refine ⟨hcO, ?_⟩
      change f (c (g p)) = g p
      rw [← Scheme.Hom.comp_apply, hc]
      rfl
    rw [hOeq] at hmem
    obtain ⟨z, ⟨hzZ, hzp⟩, hzc⟩ := hmem
    refine ⟨c, hc, ?_⟩
    have hz := eq_lift_of_fst_mem_range f g c hc z ⟨g p, hzc.symm⟩
    have hzp' : pullback.snd f g z = p := hzp
    rw [hzp'] at hz
    rw [← hz]
    exact hzZ
  have hfib : ∀ y : Y, f y = g p → ∃ y' ∈ O, y' ⤳ y ∧ f y' = g p := by
    intro y hy
    obtain ⟨z₀, hz₀1, hz₀2⟩ := Scheme.Pullback.exists_preimage_pullback y p hy
    obtain ⟨z, hzZ, hzq, hzz₀⟩ := hZ z₀
    have hzp : pullback.snd f g z = p := hzq.trans hz₀2
    refine ⟨pullback.fst f g z, ?_, ?_, ?_⟩
    · have hmem : pullback.fst f g z ∈ O ∩ f ⁻¹' {g p} := by
        rw [hOeq]
        exact ⟨z, ⟨hzZ, hzp⟩, rfl⟩
      exact hmem.1
    · rw [← hz₀1]
      exact hzz₀.map (pullback.fst f g).continuous
    · rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hzp]
  rcases eq_genericPt_or_closedPoint (g p) with hgp | hgp
  · obtain ⟨y0, hy0⟩ := f.surjective (IsLocalRing.closedPoint R)
    obtain ⟨ζ, hζmem, hζf, -⟩ := exists_fibreGenericPoint_specializes f y0
    have hζs : f ζ = IsLocalRing.closedPoint R := hζf.trans hy0
    have hgen : ∀ y : Y, y ⤳ ζ → f y = IsLocalRing.closedPoint R → y = ζ := by
      obtain ⟨s, z, hz, hzζ⟩ := Set.mem_iUnion.mp hζmem
      have hs : f ζ = s := by
        rw [← hzζ]
        exact (f.fiberHomeo s z).2
      intro y hy hfy
      rw [← hzζ] at hy ⊢
      exact SmoothDvrFibreGenericPoints.noProperGenerization_in_fibre f s z hz y hy
        (hfy.trans (hζs.symm.trans hs))
    obtain ⟨ξ, -, hfξ, hmax, hξcl⟩ :=
      exists_generic_mem_closure_sectionGenericPoints f ζ hζs hgen
    obtain ⟨y', hy'O, hy'ξ, -⟩ := hfib ξ (hfξ.trans hgp.symm)
    have hξO : ξ ∈ O := (hmax y' hy'ξ) ▸ hy'O
    obtain ⟨_, hcO, c, hc, rfl⟩ := mem_closure_iff.mp hξcl O hO hξO
    exact ⟨c, hc, by rw [hgp]; exact hcO⟩
  · obtain ⟨y0, hy0⟩ := f.surjective (g p)
    obtain ⟨y', hy'O, -, hy'f⟩ := hfib y0 hy0
    obtain ⟨c, hc, hcO⟩ := exists_section_closedPoint_mem f O hO ⟨y', hy'O, hy'f.trans hgp⟩
    exact ⟨c, hc, by rw [hgp]; exact hcO⟩

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
