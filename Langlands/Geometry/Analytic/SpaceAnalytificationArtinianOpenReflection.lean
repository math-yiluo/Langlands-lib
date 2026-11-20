import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPointsEquivalence
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteLocal
import Langlands.Geometry.Analytic.ArtinianOpenImmersionTests
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartNeighborhoods
import Langlands.Geometry.Analytic.SpaceAnalytificationClosedImmersionReflection
import Langlands.Geometry.Analytic.SpaceAnalytificationMonomorphismDetection

/-! # Open immersion reflection by finite Artinian tests -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open SaturatedAtlasPresentation AffineAnalytification
open ArtinianOpenImmersionTests

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X' X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y' Y : LocalizedCategory.{u, u, u} (K := K)}
  {p' : PointFamily K X' Y'} {p : PointFamily K X Y}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_affinoidPointHom_of_subsingleton
    (hp : IsAnalytification K X Y p) (hX : IsSeparated X) (hft : LocallyOfFiniteTypeOverBase X)
    (R : PresentedAffinoidAlgebra K) [Subsingleton (BanachSpectrum R)]
    (z : BanachSpectrum R) (g : localizedAffinoidSpectrum R ⟶ Y) :
    ∃ x : RingPoints K X R, affinoidPointHom hp hX hft R x = g := by
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  let e := (localizationFunctor.mapIso B.saturationIso).symm
  let hp₀ := hp.comp_iso e
  let t : localizedSpaceFunctor.obj (localizedAffinoidSpectrum R) :=
    SmallAffinoidSpectrum.spectrumHomeomorph R z
  let y : B.presentation.space := localizedSpaceFunctor.map (g ≫ e.hom) t
  obtain ⟨j, w, hw⟩ := B.presentation.atlas.saturatedAtlas.exists_mem_range_chart y
  obtain ⟨k, -, hkn, hk⟩ :=
    exists_affinoidPointHom_neighborhood B.presentation hp₀ hX hft j w
  have hkt : y ∈ range (B.presentation.atlas.saturatedAtlas.chart k) :=
    hw ▸ (show w ∈ B.presentation.atlas.saturatedAtlas.chart j ⁻¹'
      range (B.presentation.atlas.saturatedAtlas.chart k) from mem_of_mem_nhds hkn)
  obtain ⟨x, hx⟩ := hk R (g ≫ e.hom) (fun s => by
    have hs : s = t := (SmallAffinoidSpectrum.spectrumHomeomorph R).symm.injective
      (Subsingleton.elim _ _)
    rw [hs]
    exact hkt)
  obtain ⟨A, _, _, P, a, x₀, rfl⟩ := exists_polynomial_point_factorization hft x
  apply Exists.intro (RingPoints.changeRing a x₀)
  apply (cancel_mono e.hom).mp
  rw [affinoidPointHom_test hp₀ hX hft R P] at hx
  rw [affinoidPointHom_test hp hX hft R P, Category.assoc]
  exact hx

/-- A nonempty affinoid spectrum with one point tests ring-valued points of
an analytification by its analytic morphisms. -/
def subsingletonAffinoidPointEquiv (hp : IsAnalytification K X Y p) (hX : IsSeparated X)
    (hft : LocallyOfFiniteTypeOverBase X) (R : PresentedAffinoidAlgebra K)
    [Subsingleton (BanachSpectrum R)] (z : BanachSpectrum R) :
    RingPoints K X R ≃ (localizedAffinoidSpectrum R ⟶ Y) :=
  Equiv.ofBijective _ ⟨affinoidPointHom_injective hp hX hft R,
    exists_affinoidPointHom_of_subsingleton hp hX hft R z⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_ringPoint_of_finiteLocal_lift
    (f : X' ⟶ X) {F : Y' ⟶ Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    {D : Type u} [CommRing D] [Algebra K D] [Module.Finite K D] [IsLocalRing D]
    (P : FinitePolynomialPresentation K D) (x : RingPoints K X D)
    (l : localized K P ⟶ Y') (hl : l ≫ F = p D P x) :
    ∃ x' : RingPoints K X' D, RingPoints.map f x' = x := by
  obtain ⟨s⟩ := nonempty_space_of_isLocalRing K P
  obtain ⟨i, z, -⟩ := (presentation K P).atlas.exists_mem_range_chart s
  let R := (presentation K P).atlas.algebra i
  let : Subsingleton (Space K P) := subsingleton_space_of_finite_of_isLocalRing K P
  let : Subsingleton (BanachSpectrum R) := ⟨fun a b =>
    ((presentation K P).atlas.isEmbedding_chart i).injective
      (@Subsingleton.elim (Space K P) inferInstance
        ((presentation K P).atlas.chart i a) ((presentation K P).atlas.chart i b))⟩
  let α := finiteLocalChartEquiv K P i ⟨z⟩
  let c := localizedAffinoidHom K P R α.toAlgHom
  obtain ⟨y, hy⟩ := exists_affinoidPointHom_of_subsingleton hp' hX' hX'ft R z (c ≫ l)
  have hyx : RingPoints.map f y = RingPoints.changeRing α.toAlgHom x := by
    apply affinoidPointHom_injective hp hX hXft R
    rw [← affinoidPointHom_comp hp' hX' hX'ft hp hX hXft f F hF, hy,
      Category.assoc, hl, affinoidPointHom_test]
  refine ⟨(RingPoints.changeRingEquiv X' α).symm y, ?_⟩
  apply (RingPoints.changeRingEquiv X α).injective
  rw [RingPoints.changeRingEquiv_apply, RingPoints.changeRing_map]
  change RingPoints.map f ((RingPoints.changeRingEquiv X' α)
    ((RingPoints.changeRingEquiv X' α).symm y)) = _
  rw [Equiv.apply_symm_apply]
  exact hyx

set_option backward.isDefEq.respectTransparency false in
private theorem exists_lift_of_openImmersion_of_finiteLocal
    {F : Y' ⟶ Y} (ho : openImmersion F)
    {D : Type u} [CommRing D] [Algebra K D] [Module.Finite K D] [IsLocalRing D]
    (P : FinitePolynomialPresentation K D) (g : localized K P ⟶ Y)
    (s : Space K P) (hs : localizedSpaceFunctor.map g s ∈ range (localizedSpaceFunctor.map F)) :
    ∃ l : localized K P ⟶ Y', l ≫ F = g := by
  obtain ⟨U, hU, e, rfl⟩ := ho
  let E := (presentationOf Y).openDomain U hU
  let : Subsingleton (Space K P) := subsingleton_space_of_finite_of_isLocalRing K P
  have hg (t : localizedSpaceFunctor.obj (localized K P)) :
      localizedSpaceFunctor.map g t ∈ E.carrier := by
    have hts : t = s := @Subsingleton.elim (Space K P) inferInstance t s
    obtain ⟨v, hv⟩ := hs
    rw [hts, ← hv, Functor.map_comp, TopCat.comp_app, domainι_apply]
    exact (localizedSpaceFunctor.map e.hom v).property
  refine ⟨domainLift E g hg ≫ e.inv, ?_⟩
  rw [Category.assoc, Iso.inv_hom_id_assoc, domainLift_comp]

section AffineTest

variable (f : X' ⟶ X) {F : Y' ⟶ Y}
  (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
  (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
  (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
  (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
    p' A P x ≫ F = p A P (RingPoints.map f x))

include hp' hp hX' hX'ft hX hXft hF in
set_option backward.isDefEq.respectTransparency false in
private theorem injective_truncationMap_of_openImmersion (ho : openImmersion F)
    {A B : Type u} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (x : RingPoints K X A) {W : Over (Spec (CommRingCat.of K))}
    (b : (schemeYoneda _).obj W ⟶ X'.presheaf) (q : W ⟶ ringTest K A)
    (hAlg : IsPullback b ((schemeYoneda _).map q) (hom f) (pointHom K x))
    (j : ringTest K B ⟶ W) [IsOpenImmersion j.left] [Mono q.left]
    (g : A →ₐ[K] B) (hjg : j ≫ q = ringTestMap K g)
    (m : Ideal B) [m.IsMaximal] (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (truncationMap g ((m.comap g.toRingHom) ^ n)) := by
  let S := Spec (CommRingCat.of K)
  let J := schemeYoneda S
  let mA := m.comap g.toRingHom
  let : mA.IsMaximal := isMaximal_comap g m
  let I := mA ^ n
  let D := A ⧸ I
  let C := B ⧸ I.map g.toRingHom
  let d := Ideal.Quotient.mkₐ K I
  let c := Ideal.Quotient.mkₐ K (I.map g.toRingHom)
  let φ := truncationMap g I
  have hC : ringTestMap K φ ≫ ringTestMap K d = ringTestMap K c ≫ ringTestMap K g := by
    rw [← ringTestMap_comp, ← ringTestMap_comp]
    rfl
  let : Module.Finite K D := finite_maximalPowerQuotient mA hn
  let : IsLocalRing D := isLocalRing_maximalPowerQuotient mA hn
  let : IsArtinianRing D := IsArtinianRing.of_finite K D
  let : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (inferInstance : m.IsMaximal).ne_top
      (Ideal.map_le_iff_le_comap.mpr (Ideal.pow_le_self hn)))
  obtain ⟨mC, hmC⟩ := Ideal.exists_maximal C
  let P := FinitePolynomialPresentation.ofFiniteType K D
  let Q := FinitePolynomialPresentation.ofFiniteType K C
  let w := (maximalCenterLift K Q mC).val
  let xD := RingPoints.changeRing d x
  let y : RingPoints K X' C := uliftYonedaEquiv.{u + 1} (J.map (ringTestMap K c ≫ j) ≫ b)
  have hy : pointHom K y = J.map (ringTestMap K c ≫ j) ≫ b := Equiv.symm_apply_apply _ _
  have hxy : RingPoints.map f y = RingPoints.changeRing φ xD := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    change pointHom K (RingPoints.map f y) = pointHom K (RingPoints.changeRing φ xD)
    rw [pointHom_map, hy, Category.assoc, hAlg.w, ← Functor.map_comp_assoc, Category.assoc, hjg,
      ← hC, pointHom_changeRing, pointHom_changeRing, Functor.map_comp_assoc]
  let t := localizedSpaceFunctor.map (localizedHom K P Q φ) w
  have ht : localizedSpaceFunctor.map (p D P xD) t ∈ range (localizedSpaceFunctor.map F) := by
    refine ⟨localizedSpaceFunctor.map (p' C Q y) w, ?_⟩
    dsimp only [t]
    rw [← TopCat.comp_app, ← Functor.map_comp, hF, hxy, hp.naturality,
      Functor.map_comp, TopCat.comp_app]
  obtain ⟨l, hl⟩ := exists_lift_of_openImmersion_of_finiteLocal ho P (p D P xD) t ht
  obtain ⟨x', hx'⟩ := exists_ringPoint_of_finiteLocal_lift f hp' hp hX' hX'ft hX hXft
    hF P xD l hl
  have hxy' : pointHom K x' ≫ hom f = J.map (ringTestMap K d) ≫ pointHom K x := by
    rw [← pointHom_map, hx', pointHom_changeRing]
  let lift := hAlg.lift (pointHom K x') (J.map (ringTestMap K d)) hxy'
  let r := J.preimage lift
  have hr : r ≫ q = ringTestMap K d := by
    apply J.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hAlg.lift_snd _ _ _
  have hSpecD (v v' : Spec (CommRingCat.of D)) : v = v' := by
    apply PrimeSpectrum.ext
    let : v.asIdeal.IsPrime := v.isPrime
    let : v'.asIdeal.IsPrime := v'.isPrime
    exact (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)).trans
      (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)).symm
  have hRange : range r.left ⊆ range j.left := by
    rintro _ ⟨v, rfl⟩
    let z := center K Q w
    refine ⟨(ringTestMap K c).left z, q.left.injective ?_⟩
    have hv : (ringTestMap K φ).left z = v := hSpecD _ _
    have hw := congrArg (fun k : ringTest K C ⟶ ringTest K A => k.left z) hC
    rw [← hjg, ← hr, Over.comp_left, Over.comp_left,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv] at hw
    exact hw.symm
  let s := IsOpenImmersion.lift j.left r.left hRange
  have hs : s ≫ j.left = r.left := IsOpenImmersion.lift_fac _ _ _
  have hsq : (ringTestMap K d).left = s ≫ (ringTestMap K g).left := by
    rw [← hjg, ← hr, Over.comp_left, Over.comp_left, ← Category.assoc, hs]
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_map g.toRingHom I)
  let k := hpb.lift (𝟙 (Spec (CommRingCat.of D))) s (by
    rw [Category.id_comp]
    exact hsq)
  have hk : k ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) = 𝟙 _ := hpb.lift_fst _ _ _
  let ψ := Spec.preimage k
  have hφ : CommRingCat.ofHom φ.toRingHom ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, show Spec.map ψ = k from Spec.map_preimage k]
    exact hk
  exact Function.LeftInverse.injective (g := ψ) (fun a =>
    congrArg (fun k : CommRingCat.of D ⟶ CommRingCat.of D => k a) hφ)

include hp' hp hX' hX'ft hX hXft hF in
set_option backward.isDefEq.respectTransparency false in
private theorem isOpenImmersion_of_affine_test (ho : openImmersion F)
    {A : Type u} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (x : RingPoints K X A) {W : Over (Spec (CommRingCat.of K))}
    (b : (schemeYoneda _).obj W ⟶ X'.presheaf) (q : W ⟶ ringTest K A)
    (hAlg : IsPullback b ((schemeYoneda _).map q) (hom f) (pointHom K x))
    [LocallyOfFiniteType W.hom] [Mono q.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion q.left := by
  let C := W.left.affineCover
  let : Etale q.left := IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) C (fun i => by
    let U := SchemeOpenChart.obj C i
    let j := SchemeOpenChart.map C i
    let : IsAffine U.left := inferInstanceAs (IsAffine (C.X i))
    let : LocallyOfFiniteType U.hom := by
      rw [← Over.w j]
      infer_instance
    let B := AffineCoordinateRing K U
    let e := affineSchemeOverIso K U
    let a := e.inv ≫ j
    let : _root_.AlgebraicGeometry.IsOpenImmersion a.left := by
      change _root_.AlgebraicGeometry.IsOpenImmersion (e.inv.left ≫ j.left)
      infer_instance
    let g := affineRingPointEquiv K A B (a ≫ q)
    have hg : a ≫ q = ringTestMap K g := (ringTestMap_affineRingPointEquiv K (a ≫ q)).symm
    let : Mono (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
      change Mono (ringTestMap K g).left
      rw [← hg, Over.comp_left]
      infer_instance
    let : _root_.AlgebraicGeometry.IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
      isOpenImmersion_of_injective_truncations g
        (injective_truncationMap_of_openImmersion f hp' hp hX' hX'ft hX hXft hF ho x b q hAlg a
          g hg)
    let : Etale (a ≫ q).left := by
      rw [hg, ringTestMap_left]
      infer_instance
    change Etale (j.left ≫ q.left)
    have he : e.hom.left ≫ (a ≫ q).left = j.left ≫ q.left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simpa only [a, Category.assoc] using
        congrArg (fun r => r.left) (e.hom_inv_id_assoc (j ≫ q))
    rw [← he]
    infer_instance)
  exact _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono q.left

end AffineTest

set_option backward.isDefEq.respectTransparency false in
/-- A compatible analytic open immersion reflects to an algebraic open immersion
of separated algebraic spaces locally of finite type over the base field. -/
theorem isOpenImmersion_of_openImmersion
    (f : X' ⟶ X) {F : Y' ⟶ Y}
    (hp' : IsAnalytification K X' Y' p') (hp : IsAnalytification K X Y p)
    (hX' : IsSeparated X') (hX'ft : LocallyOfFiniteTypeOverBase X')
    (hX : IsSeparated X) (hXft : LocallyOfFiniteTypeOverBase X)
    (hF : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (P : FinitePolynomialPresentation K A) (x : RingPoints K X' A),
      p' A P x ≫ F = p A P (RingPoints.map f x))
    (ho : openImmersion F) : AlgebraicSpace.IsOpenImmersion (hom f) := by
  let : Mono F := by
    obtain ⟨U, hU, e, rfl⟩ := ho
    infer_instance
  let : Mono (hom f) := mono_of_mono_analytification_of_isSeparated f hp' hp hF hX' hX hX'ft
  let hr := isRepresentableMorphism_of_mono_of_finiteType_source f hX'ft hX
  obtain ⟨T, a, ha, hs, hT⟩ := hXft.exists_atlas
  let : LocallyOfFiniteType T.hom := hT
  let S := Spec (CommRingCat.of K)
  let J := schemeYoneda S
  let q := hr.snd a
  apply relativeProperty_of_etale_atlas @_root_.AlgebraicGeometry.IsOpenImmersion hr a ha hs
  change _root_.AlgebraicGeometry.IsOpenImmersion q.left
  let C := T.left.affineCover
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @_root_.AlgebraicGeometry.IsOpenImmersion) C]
  intro i
  let U := SchemeOpenChart.obj C i
  let j := SchemeOpenChart.map C i
  let : IsAffine U.left := inferInstanceAs (IsAffine (C.X i))
  let : LocallyOfFiniteType U.hom := by
    rw [← Over.w j]
    infer_instance
  let A := AffineCoordinateRing K U
  let e := affineSchemeOverIso K U
  let c := e.inv ≫ j
  let x : RingPoints K X A := uliftYonedaEquiv.{u + 1} (J.map c ≫ a)
  have hx : pointHom K x = J.map c ≫ a := Equiv.symm_apply_apply _ _
  have he : AlgebraicSpace.IsEtale (pointHom K x) := by
    rw [hx]
    apply AlgebraicSpace.IsEtale.comp _ ha
    apply isEtale_map
    change Etale (e.inv.left ≫ j.left)
    infer_instance
  let W := pullback q c
  let b := J.map (pullback.fst q c) ≫ hr.fst a
  let r := pullback.snd q c
  have hAlg : IsPullback b (J.map r) (hom f) (pointHom K x) := by
    rw [hx]
    exact ((IsPullback.of_hasPullback q c).map J).paste_horiz (hr.isPullback a)
  let := MorphismProperty.relative_isStableUnderBaseChange (F := J)
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S))
  have hb : AlgebraicSpace.IsEtale b := MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative J) hAlg.flip he
  let : LocallyOfFiniteType W.hom := locallyOfFiniteType_of_isEtale hX'ft b hb
  let : Mono (J.map r) := hAlg.mono_snd_of_mono
  let : Mono r := J.mono_of_mono_map inferInstance
  let : Mono r.left := Over.mono_left_of_mono r
  have hrOpen := isOpenImmersion_of_affine_test f hp' hp hX' hX'ft hX hXft hF ho x b r hAlg
  have hU : IsPullback (pullback.fst q c) (r ≫ e.inv) q j := by
    apply (IsPullback.of_hasPullback q c).of_iso
      (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    · simp
    · simp [r]
    · simp
    · simp [c]
  have hscheme := hU.map (Over.forget S)
  let : _root_.AlgebraicGeometry.IsOpenImmersion r.left := hrOpen
  have hImm : _root_.AlgebraicGeometry.IsOpenImmersion
      (hscheme.isoPullback.inv ≫ (r ≫ e.inv).left) := by
    rw [Over.comp_left]
    infer_instance
  change _root_.AlgebraicGeometry.IsOpenImmersion (pullback.snd q.left j.left)
  exact hscheme.isoPullback_inv_snd ▸ hImm

end Langlands.Analytic.SpaceAnalytification
