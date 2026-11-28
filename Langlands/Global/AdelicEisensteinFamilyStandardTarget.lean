import Langlands.Global.AdelicEisensteinFamilyStandardSource
import Langlands.Global.AdelicEisensteinFamilyTargetRange
import Langlands.Global.AdelicEisensteinFamilyConjugateTarget
import Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # The target parabolic in standard position -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine Q.X.left] [IsAffine V.X.left]

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine Q.X.left] [IsAffine V.X.left] in
private theorem mono_grp_of_closed' {H : GroupScheme (Spec (CommRingCat.of F))} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) : Mono j := by
  let := hj.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact (Grp.forget _).mono_of_mono_map (f := j) this

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine Q.X.left] [IsAffine V.X.left] in
private theorem isClosedImmersion_comp_innerIso {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    IsClosedImmersion (j ≫ (G.innerIso s).hom).hom.hom.left := by
  let : IsIso (G.innerIso s).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso s))).hom)
  change IsClosedImmersion (j.hom.hom.left ≫ (G.innerIso s).hom.hom.hom.left)
  infer_instance

/-- **The target parabolic in standard position.** Let `fam` be a standard family with a
standard index `I`, and `(w, c)` a Weyl conjugation from `P_I` to a parabolic `q` with root
presentation `r'`. There are a standard index `J`, a rational point `s`, a Levi conjugation
`c₃` and a Levi projection `proj` of `P_J` such that `(s w, c₃)` is a Weyl conjugation from
`P_I` to `P_J`, and the family comparison for `(P_I, P_J, s w)` with the standard presentations
implies the family comparison for `(P_I, q, w)`. Regularity for `r'` is compared with that of
the standard presentation of `P_J` by `RootPresentationRegularityComparisonStatement`. -/
theorem FamilyRegularComparison.exists_standardTarget
    (hcmp : RootPresentationRegularityComparisonStatement.{u})
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) {π' : Q ⟶ M'}
    (hπ' : l' ≫ π' = 𝟙 M') (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ fam.M I}
    (hw : IsWeylConjugation (fam.p I) (fam.l I) q l' w c)
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKQ : IsIwasawaCompact q K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    ∃ J : StandardIndex F G fam.i fam.ν,
      haveI : IsClosedImmersion (fam.p J).hom.hom.left :=
        (fam.isCompatible J).parabolic.isClosedSubgroup
      haveI := (⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
        ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J)).mono_groupHom_f
      ∃ (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c₃ : fam.M J ⟶ fam.M I)
        (proj : fam.P J ⟶ fam.M J) (hKJ : IsIwasawaCompact (fam.p J) K),
        fam.l J ≫ proj = 𝟙 (fam.M J) ∧
        IsWeylConjugation (fam.p I) (fam.l I) (fam.p J) (fam.l J) (s * w) c₃ ∧
        (FamilyRegularComparison.{u, v, w} (fam.iU I) (fam.l I)
            (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩ :
              ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
            (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
            fam.maximalSplit.isSplitSubtorus.1 (fam.iU J) (fam.l J)
            (⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
              ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
            (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
            fam.maximalSplit.isSplitSubtorus.1 proj (s * w) c₃ hKI hKJ rho hsmooth hcalc →
          FamilyRegularComparison.{u, v, w} (fam.iU I) (fam.l I)
            (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩ :
              ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
            (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
            fam.maximalSplit.isSplitSubtorus.1 iV l' r' hA' hT' π' w c hKI hKQ rho hsmooth
            hcalc) := by
  classical
  have hG := fam.connectedReductive
  obtain ⟨ζ, -, hPζ, hMζ⟩ := r'.isCompatible.realization
  have hroot := relativeRootSystem F G hG fam.T fam.i fam.maximalSplit
  obtain ⟨g, J, ζ₁, hζ₁, hPg, hMg, hPd, hMd⟩ :=
    exists_simultaneousStandardConjugate_of_dynamicRealization smoothMaximalSplitTorusConjugacy hG
      fam.maximalSplit hroot fam.generic q l' (CommGroupScheme.groupHom ζ ≫ r'.data.i) hPζ hMζ
  let Jq : StandardIndex F G fam.i fam.ν := ⟨J, hζ₁.1⟩
  refine ⟨Jq, ?_⟩
  let stdJ : ParabolicRootPresentation (fam.p Jq) (fam.l Jq) (fam.a Jq) :=
    ⟨⟨fam.T, fam.i, fam.ν, Jq.val, fam.f Jq⟩, fam.isCompatible Jq⟩
  have hPJc : IsClosedSubgroup (fam.p Jq) := (fam.isCompatible Jq).parabolic.isClosedSubgroup
  have : IsClosedImmersion (fam.p Jq).hom.hom.left := hPJc
  have := stdJ.mono_groupHom_f
  -- the conjugated target
  have hq'C : IsClosedSubgroup (q ≫ (G.innerIso g).hom) := isClosedImmersion_comp_innerIso q g
  have : IsClosedImmersion (q ≫ (G.innerIso g).hom).hom.hom.left := hq'C
  have : IsClosedImmersion (iV ≫ q ≫ (G.innerIso g).hom).hom.hom.left := by
    have := isClosedImmersion_comp_innerIso (iV ≫ q) g
    simpa only [Category.assoc] using this
  have : Mono (r'.compAmbientIso (G.innerIso g)).data.i.hom.hom.left := by
    let : IsIso (G.innerIso g).hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso g))).hom)
    change Mono (r'.data.i.hom.hom.left ≫ (G.innerIso g).hom.hom.hom.left)
    infer_instance
  let : Fintype (relativeWeylGroup (r'.compAmbientIso (G.innerIso g)).data.i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup _
      (r'.compAmbientIso (G.innerIso g)).isCompatible.maximalSplit)
  have : Mono (CommGroupScheme.groupHom (r'.compAmbientIso (G.innerIso g)).data.f).hom.hom.left :=
    inferInstanceAs (Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left)
  obtain ⟨hKQ', -⟩ := eisensteinConjugateParabolicHeight F G Q q g K hKQ
  have hrangeJ : SubgroupFunctor.range (q ≫ (G.innerIso g).hom) = SubgroupFunctor.range (fam.p Jq) :=
    hPg.trans (fam.isCompatible Jq).parabolic_eq.symm
  have hKJ : IsIwasawaCompact (fam.p Jq) K := hKQ'.of_range_eq hrangeJ
  let eQ : fam.P Jq ≅ Q := hPJc.sourceIsoOfRangeEq hq'C hrangeJ.symm
  have heQ : eQ.hom ≫ q ≫ (G.innerIso g).hom = fam.p Jq :=
    hPJc.sourceIsoOfRangeEq_hom_comp hq'C hrangeJ.symm
  have hLJc : IsClosedSubgroup (fam.l Jq ≫ fam.p Jq) :=
    (fam.isCompatible Jq).levi.isClosedSubgroup.comp hPJc
  have hL'c : IsClosedSubgroup (l' ≫ q ≫ (G.innerIso g).hom) :=
    r'.isCompatible.levi.isClosedSubgroup.comp hq'C
  have hMr : SubgroupFunctor.range (l' ≫ q ≫ (G.innerIso g).hom) =
      SubgroupFunctor.range (fam.l Jq ≫ fam.p Jq) :=
    hMg.trans (fam.isCompatible Jq).levi_eq.symm
  let eMQ : M' ≅ fam.M Jq := hL'c.sourceIsoOfRangeEq hLJc hMr
  have heMQ : eMQ.hom ≫ fam.l Jq ≫ fam.p Jq = l' ≫ q ≫ (G.innerIso g).hom :=
    hL'c.sourceIsoOfRangeEq_hom_comp hLJc hMr
  have hVr : SubgroupFunctor.range (iV ≫ q ≫ (G.innerIso g).hom) =
      SubgroupFunctor.range (fam.iU Jq ≫ fam.p Jq) := by
    let := hG.smooth
    let := hq'C.mono
    let := hL'c.mono
    have h := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
      (CommGroupScheme.groupHom ζ₁ ≫ fam.i) (p := q ≫ (G.innerIso g).hom)
      (z := l' ≫ q ≫ (G.innerIso g).hom) ⟨Over.mono_of_mono_left _, hPd⟩
      ⟨Over.mono_of_mono_left _, hMd⟩ r'.isCompatible.levi.isConnectedReductive hV
    have hstd := (standardCocharacter F G hG fam.T fam.i fam.maximalSplit fam.ν fam.generic J
      hζ₁.1).2 ζ₁ hζ₁
    rw [fam.range_radical_eq_standardUnipotent Jq]
    exact h.trans hstd.2.2.symm
  have hw' : IsWeylConjugation (fam.p I) (fam.l I) (q ≫ (G.innerIso g).hom) l' (g * w) c :=
    ⟨hw.isIso, by
      simpa only [Category.assoc, innerIso_mul_inv, Iso.hom_inv_id_assoc] using hw.comp_eq⟩
  let c₃ : fam.M Jq ⟶ fam.M I := eMQ.inv ≫ c
  let proj : fam.P Jq ⟶ fam.M Jq := eQ.hom ≫ π' ≫ eMQ.hom
  have hmonoq' : Mono (q ≫ (G.innerIso g).hom) := mono_grp_of_closed' hq'C
  have hkeyQ : fam.l Jq ≫ eQ.hom = eMQ.inv ≫ l' := by
    rw [← cancel_mono (q ≫ (G.innerIso g).hom)]
    simp only [Category.assoc]
    rw [heQ, ← heMQ, Iso.inv_hom_id_assoc]
  have hproj : fam.l Jq ≫ proj = 𝟙 (fam.M Jq) := by
    change fam.l Jq ≫ eQ.hom ≫ π' ≫ eMQ.hom = _
    rw [← Category.assoc, hkeyQ, Category.assoc, reassoc_of% hπ', Iso.inv_hom_id]
  have hw₃ : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Jq) (fam.l Jq) (g * w) c₃ := by
    have := hw.isIso
    refine ⟨inferInstanceAs (IsIso (eMQ.inv ≫ c)), ?_⟩
    change (eMQ.inv ≫ c) ≫ fam.l I ≫ fam.p I = fam.l Jq ≫ fam.p Jq ≫ (G.innerIso (g * w)).inv
    rw [Category.assoc, hw'.comp_eq]
    simp only [Category.assoc]
    rw [← reassoc_of% heMQ, Iso.inv_hom_id_assoc]
  have hW : ∀ lam, weylParameter (fam.l I) c₃ proj lam =
      parameterRestrict eQ.hom (weylParameter (fam.l I) c π' lam) := by
    intro lam
    change parameterRestrict (proj ≫ c₃ ≫ fam.l I) lam =
      parameterRestrict eQ.hom (parameterRestrict (π' ≫ c ≫ fam.l I) lam)
    rw [show proj ≫ c₃ ≫ fam.l I = eQ.hom ≫ π' ≫ c ≫ fam.l I by
      simp only [proj, c₃, Category.assoc, Iso.hom_inv_id_assoc], parameterRestrict_comp,
      LinearMap.comp_apply]
  have hcomp := hcmp F G Q M' (fam.P Jq) (fam.M Jq) A' (fam.A Jq) (q ≫ (G.innerIso g).hom) l' a'
    (r'.compAmbientIso (G.innerIso g)) (fam.p Jq) (fam.l Jq) (fam.a Jq) stdJ hA' hT'
    (fam.isCompatible Jq).splitComponent.isCentralSplitTorus.1.1 fam.maximalSplit.isSplitSubtorus.1
    hG eQ.hom heQ hrangeJ hMr
  refine ⟨g, c₃, proj, hKJ, hproj, hw₃, fun h => ?_⟩
  refine FamilyRegularComparison.of_conjugateTarget g (fam.isUnipotentRadical I) hV
    r'.isCompatible.levi hw hKI hKQ hKQ' ?_
  exact FamilyRegularComparison.of_targetRange (r'.compAmbientIso (G.innerIso g)) stdJ hA' hT'
    (fam.isCompatible Jq).splitComponent.isCentralSplitTorus.1.1 fam.maximalSplit.isSplitSubtorus.1
    eQ heQ hrangeJ hVr hMr hW hcomp hKI hKQ' hKJ h

end Langlands.Global
