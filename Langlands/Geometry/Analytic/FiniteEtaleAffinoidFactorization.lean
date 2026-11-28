import Langlands.Geometry.Analytic.ClopenAffinoidImage
import Langlands.Geometry.Analytic.CompactEtaleKernelPair
import Langlands.Geometry.Analytic.EtaleQuotientComparison
import Langlands.Geometry.Analytic.FiniteEtaleKernelPairQuotient
import Langlands.Geometry.Analytic.SmallAffinoidRingPushout

/-! # Affinoid models of intermediate finite étale maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open PresentedAffinoidAlgebra SaturatedAtlasPresentation
open PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private abbrev localizedSpectrum (A : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)] :
    LocalizedCategory.{u, v, v} (K := K) :=
  localizationFunctor.obj (saturated.{u, v} A)

private abbrev spectrumMap {A B : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B) :
    localizedSpectrum.{u, v} B ⟶ localizedSpectrum.{u, v} A :=
  localizedMapEquiv.{u, v} A B f

private theorem compact_localizedSpectrum (A : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum A)] : IsCompactSpace (localizedSpectrum.{u, v} A) :=
  ⟨(spectrumHomeomorph.{u, v} A).compactSpace, (spectrumHomeomorph.{u, v} A).t2Space⟩

private theorem surjective_spectrumMap {A B : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    (f : BoundedAlgHom K A B)
    (hf : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    Function.Surjective (localizedSpaceFunctor.map (spectrumMap.{u, v} f)) := by
  intro x
  obtain ⟨a, rfl⟩ := (spectrumHomeomorph.{u, v} A).surjective x
  obtain ⟨b, hb⟩ := hf a
  exact ⟨spectrumHomeomorph.{u, v} B b,
    (map_spectrumHomeomorph f b).trans (congrArg (spectrumHomeomorph.{u, v} A) hb)⟩

private theorem finiteEtale_selfPushout {A B : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale) :
    ((leftMap f f).IsFiniteBanach ∧ (leftMap f f).AlgebraicallyFiniteEtale) ∧
      ((rightMap f f).IsFiniteBanach ∧ (rightMap f f).AlgebraicallyFiniteEtale) := by
  let L := leftMap f f
  let R := rightMap f f
  let C := algebra f f
  have hRfin : R.IsFiniteBanach := rightMap_isFiniteBanach f f hf
  have hRe : R.AlgebraicallyFiniteEtale :=
    BoundedAlgHom.algebraicallyFiniteEtale_of_isEtaleAtPoint _ hRfin.finite
      (fun x => rightMap_isEtaleAtPoint_of_tensorComparison f f (tensorComparison_bijective f f hf)
        hf.finite.finiteType x (he.isEtaleAtPoint _))
  let a := lift f f C R L (condition f f).symm
  have hL : a.comp L = R := lift_comp_leftMap f f C R L (condition f f).symm
  have hR : a.comp R = L := lift_comp_rightMap f f C R L (condition f f).symm
  have hInv : a.comp a = BoundedAlgHom.id K C := by
    apply AffinoidPushout.hom_ext f f C
    · rw [BoundedAlgHom.comp_assoc, hL, hR, BoundedAlgHom.id_comp]
    · rw [BoundedAlgHom.comp_assoc, hR, hL, BoundedAlgHom.id_comp]
  have hinv : Function.Involutive a :=
    fun x => congrArg (fun b : BoundedAlgHom K C C => b x) hInv
  obtain ⟨M, hM, hb⟩ := a.bounded
  have hafin := BoundedAlgHom.isFiniteBanach_of_lift a hM (fun x => ⟨a x, hinv x, hb x⟩)
  have hae := BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective a hinv.bijective
  change (L.IsFiniteBanach ∧ L.AlgebraicallyFiniteEtale) ∧
    (R.IsFiniteBanach ∧ R.AlgebraicallyFiniteEtale)
  rw [← hR]
  exact ⟨⟨hafin.comp hRfin, hae.comp hRe⟩, ⟨hRfin, hRe⟩⟩

section Model

variable {A B : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum A)]
  [Small.{v} (BanachSpectrum B)] {H : LocalizedCategory.{u, v, v} (K := K)}

/-- An actual affinoid model for an intermediate map, with its finite Banach
and algebraic finite étale witnesses over the original base. -/
structure FiniteEtaleAffinoidModel (g : H ⟶ localizedSpectrum.{u, v} A) where
  algebra : PresentedAffinoidAlgebra K
  small : Small.{v} (BanachSpectrum algebra)
  baseMap : BoundedAlgHom K A algebra
  finiteBanach : baseMap.IsFiniteBanach
  finiteEtale : baseMap.AlgebraicallyFiniteEtale
  iso : H ≅ @localizedSpectrum.{u, v} K _ _ _ algebra small
  iso_hom_comp : iso.hom ≫ @spectrumMap.{u, v} K _ _ _ A algebra _ small baseMap = g

set_option backward.isDefEq.respectTransparency false in
/-- An étale surjection from a small affinoid onto a Hausdorff intermediate
space of a finite étale affinoid map gives a finite étale affinoid model of
the intermediate space, assuming étale Hom descent. -/
def finiteEtaleAffinoidModelOfEtaleFactorization
    (hSheaf : EtaleHomSheafStatement.{u, v})
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (q : localizedSpectrum.{u, v} B ⟶ H) (hq : etale q)
    (hqs : Function.Surjective (localizedSpaceFunctor.map q))
    (hH : T2Space (localizedSpaceFunctor.obj H))
    (g : H ⟶ localizedSpectrum.{u, v} A) (hg : q ≫ g = spectrumMap.{u, v} f) :
    FiniteEtaleAffinoidModel g := by
  let P := localizedSpectrum.{u, v} B
  have hP : IsCompactSpace P := compact_localizedSpectrum B
  let r := compactLocalizedEtalePullback q q hq hP hP hH
  have hr : IsPullback r.cone.fst r.cone.snd q q := IsPullback.of_isLimit r.isLimit
  let C := algebra f f
  let : Small.{v} (BanachSpectrum C) :=
    small_spectrum_of_finiteBanachPushout f f finiteBanachPushout hf
  have hS : IsPullback (spectrumMap.{u, v} (leftMap f f))
      (spectrumMap.{u, v} (rightMap f f)) (q ≫ g) (q ≫ g) := by
    rw [hg]
    exact pushout_localized_isPullback.{u, v} f f
  have hcom : etale (q ≫ g) := hg.symm ▸ map_etale_of_finite_pointwiseEtale f
    finiteBanachPushout finiteTensorComparison hf he.isEtaleAtPoint
  let j := kernelPairComparison hr hS
  let : Mono j := mono_kernelPairComparison hr hS
  have hj : etale j := etale_kernelPairComparison hr hS hq hcom
  let U : Set (saturated.{u, v} C).presentation.space := range (localizedSpaceFunctor.map j)
  have hU : IsClopen U :=
    isClopen_range_kernelPairComparison hr hS hq hcom hP hH (compact_localizedSpectrum C).2
  let d := clopenDomainChart C U hU
  let : Small.{v} (BanachSpectrum d.algebra) := small_clopenDomainChart C U hU
  let e := etaleMonoClopenImageIso C U hU j hj rfl
  have heq : e.hom ≫ spectrumMap.{u, v} d.baseMap = j :=
    etaleMonoClopenImageIso_hom_comp_map C U hU j hj rfl
  let s := d.baseMap.comp (leftMap f f)
  let t := d.baseMap.comp (rightMap f f)
  have hs : e.hom ≫ spectrumMap.{u, v} s = r.cone.fst := by
    change e.hom ≫ localizedMapEquiv.{u, v} B d.algebra s = _
    rw [localizedMapEquiv_comp, ← Category.assoc, heq]
    exact kernelPairComparison_fst hr hS
  have ht : e.hom ≫ spectrumMap.{u, v} t = r.cone.snd := by
    change e.hom ≫ localizedMapEquiv.{u, v} B d.algebra t = _
    rw [localizedMapEquiv_comp, ← Category.assoc, heq]
    exact kernelPairComparison_snd hr hS
  have hr' : IsPullback (spectrumMap.{u, v} s) (spectrumMap.{u, v} t) q q :=
    hr.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hs.symm)
      (by simpa only [Iso.refl_hom, Category.comp_id] using ht.symm) (by simp) (by simp)
  have hd : d.baseMap.AlgebraicallyFiniteEtale := algebraicallyFiniteEtale_clopenRationalChart _
  have hdb : d.baseMap.IsFiniteBanach := isFiniteBanach_clopenRationalChart _
  have hdf : Function.Surjective d.baseMap := surjective_clopenRationalChart _
  obtain ⟨hLeft, hRight⟩ := finiteEtale_selfPushout f hf he
  let Q := finiteEtaleAffinoidQuotientOfLocalizedKernelPair hr' f hf he
    (hd.comp hLeft.2) (hd.comp hRight.2) (hdb.comp hRight.1)
    g hg (range_sup_of_quotient_pushout f f hf d.baseMap hdf)
  have hQs := Q.val.coverMap_spectrum_surjective_of_isFiniteBanach Q.property.2
  let hSmall : Small.{v} (BanachSpectrum Q.val.algebra) := small_of_surjective hQs
  letI := hSmall
  let p := spectrumMap.{u, v} Q.val.coverMap
  have hp : etale p := map_etale_of_finite_pointwiseEtale Q.val.coverMap
    finiteBanachPushout finiteTensorComparison Q.property.2 Q.val.coverMap_finiteEtale.isEtaleAtPoint
  have hpull : IsPullback (spectrumMap.{u, v} s) (spectrumMap.{u, v} t) p p :=
    localized_isPullback_of_ring_isPushout Q.val.relation_isPushout (hdb.comp hLeft.1)
  let α := etaleQuotientIsoOfCommonKernelPair hSheaf q p hq hp hqs
    (surjective_spectrumMap Q.val.coverMap hQs) hr' hpull
  refine ⟨Q.val.algebra, hSmall, Q.val.baseMap, Q.property.1, Q.val.baseMap_finiteEtale, α.val, ?_⟩
  apply hom_ext_of_etale_cover (hSheaf K H (localizedSpectrum.{u, v} A))
    (fun _ : Unit => P) (fun _ => q) (fun _ => hq) (fun x => ⟨(), hqs x⟩)
  intro k
  change q ≫ α.val.hom ≫ spectrumMap.{u, v} Q.val.baseMap = q ≫ g
  rw [← Category.assoc, α.property]
  change localizedMapEquiv.{u, v} _ _ Q.val.coverMap ≫
    localizedMapEquiv.{u, v} _ _ Q.val.baseMap = q ≫ g
  rw [← localizedMapEquiv_comp, Q.val.coverMap_comp]
  exact hg.symm

end Model

end Langlands.Analytic.SmallAffinoidSpectrum
