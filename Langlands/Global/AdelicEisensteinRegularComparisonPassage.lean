import Langlands.Global.AdelicEisensteinRegularComparisonPassageStatement
import Langlands.Global.AdelicEisensteinFamilyCompacts
import Langlands.Global.AdelicEisensteinFamilyCompactChange
import Langlands.Global.AdelicEisensteinFamilyStandardCase
import Langlands.Global.AdelicEisensteinFamilyStandardSource
import Langlands.Global.AdelicEisensteinFamilyStandardTarget
import Langlands.Global.AdelicEisensteinFamilyNormalizerRepresentative
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Global.AdelicEisensteinConjugateParabolicHeight
import Langlands.Global.AdelicGoodPositionIwasawaCompactProof
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Rational.ParabolicRootRadicals

/-! # The regular-patch comparison from the standard family comparison -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Iwasawa

variable {F : Type u} [Field F] [NumberField F]
  {G H H' : GroupScheme (Spec (CommRingCat.of F))} {K : Subgroup (AdelicGroupPoints F G)}

/-- Iwasawa coverage for a rational conjugate `p ≫ Int(s)` gives Iwasawa coverage for `p`. -/
theorem AdelicGroupPoints.IsIwasawaCompact.of_comp_innerIso {p : H ⟶ G}
    (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hK : IsIwasawaCompact (p ≫ (G.innerIso s).hom) K) : IsIwasawaCompact p K := by
  refine hK.of_conjugate_map (t := (innerAdelicPoint F G s)⁻¹) fun a => ?_
  have h : map F H G (p ≫ (G.innerIso s).hom) a =
      innerAdelicPoint F G s * map F H G p a * (innerAdelicPoint F G s)⁻¹ := by
    rw [map_comp_apply_of_hom]
    exact affinePointsTarget_innerIso_hom F G s _
  rw [h]
  group

end Iwasawa

section Presentation

variable {F : Type u} [Field F] [NumberField F]
  {G Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A subgroup with Iwasawa coverage for the minimal standard parabolic of a family has Iwasawa
coverage for every parabolic with a root presentation: such a parabolic is rationally conjugate
to a standard one, which contains the minimal standard parabolic. -/
theorem StandardParabolicFamily.isIwasawaCompact_of_presentation
    (fam : StandardParabolicFamily F G) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    {q : Q ⟶ G} {l' : M' ⟶ Q} {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a') :
    IsIwasawaCompact q K := by
  have hG := fam.connectedReductive
  obtain ⟨ζ, -, hPζ, hMζ⟩ := r'.isCompatible.realization
  have hroot := relativeRootSystem F G hG fam.T fam.i fam.maximalSplit
  obtain ⟨g, J, ζ₁, hζ₁, hPg, -, -, -⟩ :=
    exists_simultaneousStandardConjugate_of_dynamicRealization smoothMaximalSplitTorusConjugacy hG
      fam.maximalSplit hroot fam.generic q l' (CommGroupScheme.groupHom ζ ≫ r'.data.i) hPζ hMζ
  let Jq : StandardIndex F G fam.i fam.ν := ⟨J, hζ₁.1⟩
  have hle : (⟨∅, Set.empty_subset _⟩ : StandardIndex F G fam.i fam.ν) ≤ Jq :=
    Set.empty_subset _
  have hKJ : IsIwasawaCompact (fam.p Jq) K :=
    hK.of_range_le ((fam.le_iff_range_le _ _).mp hle)
  have hrangeJ : SubgroupFunctor.range (q ≫ (G.innerIso g).hom) =
      SubgroupFunctor.range (fam.p Jq) :=
    hPg.trans (fam.isCompatible Jq).parabolic_eq.symm
  exact (hKJ.of_range_eq hrangeJ.symm).of_comp_innerIso g

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- For a parabolic with a root presentation and a geometric unipotent radical, the Levi-first
multiplication `M × V → Q` is an isomorphism. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.isIso_subgroupMultiplication
    (hG : IsConnectedReductive G) {q : Q ⟶ G} {l' : M' ⟶ Q} {a' : A'.toGrp ⟶ M'}
    (r' : ParabolicRootPresentation q l' a') {iV : V ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left] (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) :
    IsIso (subgroupMultiplication l' iV) := by
  obtain ⟨ζ, -, hPζ, hMζ⟩ := r'.isCompatible.realization
  have hPc : IsClosedSubgroup q := r'.isCompatible.parabolic.isClosedSubgroup
  have hLc : IsClosedSubgroup (l' ≫ q) := r'.isCompatible.levi.isClosedSubgroup.comp hPc
  have hVc : IsClosedSubgroup (iV ≫ q) := ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
  let := hG.smooth
  let := hPc.mono
  let := hLc.mono
  let := hVc.mono
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ r'.data.i)).IsRepresentedBy q :=
    ⟨Over.mono_of_mono_left _, hPζ⟩
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ r'.data.i)).IsRepresentedBy
      (l' ≫ q) :=
    ⟨Over.mono_of_mono_left _, hMζ⟩
  have hVr := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    (CommGroupScheme.groupHom ζ ≫ r'.data.i) (p := q) (z := l' ≫ q) hP hZ
    r'.isCompatible.levi.isConnectedReductive hV
  have hU : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ r'.data.i)).IsRepresentedBy
      (iV ≫ q) :=
    ⟨Over.mono_of_mono_left _, hVr⟩
  exact Dynamic.isIso_subgroupMultiplication hP hZ hU l' iV rfl rfl

end Presentation

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

/-- **The family comparison for arbitrary data.** Granting Bruhat–Tits availability, the
comparison for finite families in standard position and the comparison of regularity across
root presentations, the family comparison holds for arbitrary parabolics `P`, `Q` with root
presentations, a Weyl conjugation `(w, c)`, a Levi projection of `Q` and a maximal compact
subgroup `K` with Iwasawa coverage for `P` and `Q`. -/
theorem FamilyRegularComparison.of_standardFamily
    (hBT : Langlands.Geometry.Building.BruhatTitsAvailabilityStatement.{u})
    (hfam : StandardEisensteinFamilyComparisonStatement.{u})
    (hcmp : RootPresentationRegularityComparisonStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) {π' : Q ⟶ M'}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hπ' : l' ≫ π' = 𝟙 M')
    (hw : IsWeylConjugation p l q l' w c)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact q K) (hKmax : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hK hK' rho
      hsmooth hcalc := by
  classical
  obtain ⟨K₀, hK₀max, hK₀e, hK₀levi⟩ := (r.standardFamily hG).exists_goodCompact hBT
  obtain ⟨s, hCmax, hinf⟩ := exists_archimedeanConjugate_infinite_eq hG hKmax hK₀max
  have hK₀I : IsIwasawaCompact ((r.standardFamily hG).p (r.standardIndex hG)) K₀ :=
    hK₀e.of_range_le (((r.standardFamily hG).le_iff_range_le _ _).mp (Set.empty_subset _))
  have hK₀p : IsIwasawaCompact p K₀ :=
    hK₀I.of_range_eq (((r.standardFamily hG).isCompatible (r.standardIndex hG)).parabolic_eq.trans
      r.isCompatible.parabolic_eq.symm)
  have hK₀q : IsIwasawaCompact q K₀ :=
    (r.standardFamily hG).isIwasawaCompact_of_presentation hK₀e r'
  have hCp := hK₀p.conjInv (ofInfinite F G s)
  have hCq := hK₀q.conjInv (ofInfinite F G s)
  obtain ⟨c₂, hKI, hw₂, himp₁⟩ :=
    FamilyRegularComparison.exists_standardSource (iV := iV) (r' := r') (hA' := hA') (hT' := hT') (π' := π')
      hG r hA hT hU hw hK₀p hK₀q rho hsmooth hcalc
  let : Fintype (relativeWeylGroup (r.standardFamily hG).i) :=
    inferInstanceAs (Fintype (relativeWeylGroup r.data.i))
  have : IsClosedImmersion ((r.standardFamily hG).p (r.standardIndex hG)).hom.hom.left :=
    ((r.standardFamily hG).isCompatible (r.standardIndex hG)).parabolic.isClosedSubgroup
  have := (⟨⟨(r.standardFamily hG).T, (r.standardFamily hG).i, (r.standardFamily hG).ν,
      (r.standardIndex hG).val, (r.standardFamily hG).f (r.standardIndex hG)⟩,
    (r.standardFamily hG).isCompatible (r.standardIndex hG)⟩ :
      ParabolicRootPresentation ((r.standardFamily hG).p (r.standardIndex hG))
        ((r.standardFamily hG).l (r.standardIndex hG))
        ((r.standardFamily hG).a (r.standardIndex hG))).mono_groupHom_f
  obtain ⟨J, s', c₃, proj, hKJ, hproj, hw₃, himp₂⟩ :=
    FamilyRegularComparison.exists_standardTarget hcmp (r.standardFamily hG) (r.standardIndex hG)
      r' hA' hT' hπ' hV hw₂ hKI hK₀q rho hsmooth hcalc
  have : IsClosedImmersion ((r.standardFamily hG).p J).hom.hom.left :=
    ((r.standardFamily hG).isCompatible J).parabolic.isClosedSubgroup
  have := (⟨⟨(r.standardFamily hG).T, (r.standardFamily hG).i, (r.standardFamily hG).ν, J.val,
      (r.standardFamily hG).f J⟩, (r.standardFamily hG).isCompatible J⟩ :
      ParabolicRootPresentation ((r.standardFamily hG).p J) ((r.standardFamily hG).l J)
        ((r.standardFamily hG).a J)).mono_groupHom_f
  obtain ⟨n, c', hn, hIJ, hJI, himp₃⟩ :=
    FamilyRegularComparison.exists_normalizerRepresentative (r.standardFamily hG)
      (r.standardIndex hG) J hw₃ hproj hKI hKJ rho hsmooth hcalc
  -- Trailing arguments are left to `apply`, since the elaborator would otherwise unfold
  -- `FamilyRegularComparison` to instantiate its leading implicit binders.
  apply FamilyRegularComparison.of_finiteCompactChange hG hU r'.isCompatible.parabolic hV
    r'.isCompatible.levi (r'.isIso_subgroupMultiplication hG hV) hw hK hK' hCp hCq hKmax hCmax
    hinf hrho
  apply FamilyRegularComparison.of_conjugateCompact hK₀p hK₀q s hCp hCq
  apply himp₁
  apply himp₂
  apply himp₃
  apply FamilyRegularComparison.of_standard hfam (r.standardFamily hG) (r.standardIndex hG) J n c'
    proj hproj hn hIJ hJI hKI hKJ hK₀max hK₀e hK₀levi rho hrho hsmooth

/-- **The regular-patch comparison from the standard family comparison.** -/
theorem eisensteinRegularComparisonPassage : EisensteinRegularComparisonPassageStatement.{u} := by
  intro hBT hfam hcmp F _ _ G P M U Q M' V A A' _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _
    a' r' _ _ _ hA' hT' π' w c hG hU hV hπ' hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
    EP DP hEP hEPser k ψ coeff D hψ hcoeff hint R
  exact FamilyRegularComparison.single
    (FamilyRegularComparison.of_standardFamily.{u, 0, 0} hBT hfam hcmp hG r hA hT r' hA' hT'
      hU hV hπ' hw hK hK' hKmax rho hrho hsmooth hcalc) φ hφ EP DP hEP hEPser k ψ coeff D
    hψ hcoeff hint R

end Langlands.Global
