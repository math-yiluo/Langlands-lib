import Langlands.Global.AdelicEisensteinFamilySourceRange
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # The standard family attached to the presentation of the inducing parabolic -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Every geometric unipotent radical of a presented parabolic has the standard unipotent image
of the presentation. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.range_radical_eq_standardUnipotent'
    (hG : IsConnectedReductive G) {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    SubgroupFunctor.range (iU ≫ p) = standardUnipotent r.data.i r.data.ν r.data.J := by
  let := hG.smooth
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := (r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup).mono
  obtain ⟨z, hz, hP, hM⟩ := r.isCompatible.realization
  have h := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    (CommGroupScheme.groupHom z ≫ r.data.i) (p := p) (z := l ≫ p)
    ⟨Over.mono_of_mono_left _, hP⟩ ⟨Over.mono_of_mono_left _, hM⟩
    r.isCompatible.levi.isConnectedReductive hU
  have hstd := (standardCocharacter F G hG r.data.T r.data.i r.isCompatible.maximalSplit r.data.ν
    r.isCompatible.generic r.data.J r.isCompatible.subset_simpleRoots).2 z hz
  exact h.trans hstd.2.2.symm

/-- The standard family of the maximal split torus and chamber of a presentation. -/
abbrev _root_.Langlands.GroupScheme.ParabolicRootPresentation.standardFamily (hG : IsConnectedReductive G) {p : P ⟶ G}
    {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a) :
    StandardParabolicFamily F G :=
  StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit r.data.ν
    r.isCompatible.generic

/-- The standard index of a presentation in its standard family. -/
abbrev _root_.Langlands.GroupScheme.ParabolicRootPresentation.standardIndex (hG : IsConnectedReductive G) {p : P ⟶ G}
    {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a) :
    StandardIndex F G (r.standardFamily hG).i (r.standardFamily hG).ν :=
  ⟨r.data.J, r.isCompatible.subset_simpleRoots⟩

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The split component of a presentation maps monomorphically into its maximal split torus. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.mono_groupHom_f {p : P ⟶ G}
    {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a) :
    Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left := by
  let := r.isCompatible.splitComponent.1.isSplitSubtorus.mono
  let := r.isCompatible.levi.isClosedSubgroup.mono
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  have : Mono (a ≫ l ≫ p).hom.hom.left := by
    change Mono (a.hom.hom.left ≫ l.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r.isCompatible.factor_comp)

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem mono_grp_of_closed {H : GroupScheme (Spec (CommRingCat.of F))} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) : Mono j := by
  let := hj.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact (Grp.forget _).mono_of_mono_map (f := j) this

variable [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]

/-- **The inducing parabolic in its standard family.** Let `r` present `P`, and let `fam` and
`I` be the standard family and index of `r`. There are a Levi conjugation `c₂` into the
standard Levi `M_I` and an Iwasawa witness for `P_I` such that `(w, c₂)` is a Weyl conjugation
from `P_I` to `Q` and the family comparison for `P_I` implies the family comparison for `P`. -/
theorem FamilyRegularComparison.exists_standardSource (hG : IsConnectedReductive G)
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {iV : V ⟶ Q} {l' : M' ⟶ Q}
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation q l' a'}
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : Q ⟶ M'}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : IsWeylConjugation p l q l' w c)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact q K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    haveI : IsClosedImmersion ((r.standardFamily hG).p (r.standardIndex hG)).hom.hom.left :=
      ((r.standardFamily hG).isCompatible (r.standardIndex hG)).parabolic.isClosedSubgroup
    haveI := (⟨⟨r.data.T, r.data.i, r.data.ν, r.data.J,
        (r.standardFamily hG).f (r.standardIndex hG)⟩,
      (r.standardFamily hG).isCompatible (r.standardIndex hG)⟩ :
        ParabolicRootPresentation ((r.standardFamily hG).p (r.standardIndex hG))
          ((r.standardFamily hG).l (r.standardIndex hG))
          ((r.standardFamily hG).a (r.standardIndex hG))).mono_groupHom_f
    ∃ (c₂ : M' ⟶ (r.standardFamily hG).M (r.standardIndex hG))
      (hKI : IsIwasawaCompact ((r.standardFamily hG).p (r.standardIndex hG)) K),
      IsWeylConjugation ((r.standardFamily hG).p (r.standardIndex hG))
        ((r.standardFamily hG).l (r.standardIndex hG)) q l' w c₂ ∧
      (FamilyRegularComparison.{u, v, w} ((r.standardFamily hG).iU (r.standardIndex hG))
          ((r.standardFamily hG).l (r.standardIndex hG))
          (⟨⟨r.data.T, r.data.i, r.data.ν, r.data.J, (r.standardFamily hG).f (r.standardIndex hG)⟩,
            (r.standardFamily hG).isCompatible (r.standardIndex hG)⟩ :
            ParabolicRootPresentation ((r.standardFamily hG).p (r.standardIndex hG))
              ((r.standardFamily hG).l (r.standardIndex hG))
              ((r.standardFamily hG).a (r.standardIndex hG)))
          ((r.standardFamily hG).isCompatible (r.standardIndex hG)).splitComponent.isCentralSplitTorus.1.1
          hT iV l' r' hA' hT' π' w c₂ hKI hK' rho hsmooth hcalc →
        FamilyRegularComparison.{u, v, w} iU l r hA hT iV l' r' hA' hT' π' w c hK hK' rho
          hsmooth hcalc) := by
  set fam := r.standardFamily hG
  set I := r.standardIndex hG
  have hPI : IsClosedSubgroup (fam.p I) := (fam.isCompatible I).parabolic.isClosedSubgroup
  have hPp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have hrange : SubgroupFunctor.range (fam.p I) = SubgroupFunctor.range p :=
    (fam.isCompatible I).parabolic_eq.trans r.isCompatible.parabolic_eq.symm
  let e : fam.P I ≅ P := hPI.sourceIsoOfRangeEq hPp hrange
  have he : e.hom ≫ p = fam.p I := hPI.sourceIsoOfRangeEq_hom_comp hPp hrange
  have hLI : IsClosedSubgroup (fam.l I ≫ fam.p I) :=
    (fam.isCompatible I).levi.isClosedSubgroup.comp hPI
  have hLp : IsClosedSubgroup (l ≫ p) := r.isCompatible.levi.isClosedSubgroup.comp hPp
  have hMr : SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (fam.l I ≫ fam.p I) :=
    r.isCompatible.levi_eq.trans (fam.isCompatible I).levi_eq.symm
  let eM : M ≅ fam.M I := hLp.sourceIsoOfRangeEq hLI hMr
  have heM : eM.hom ≫ fam.l I ≫ fam.p I = l ≫ p := hLp.sourceIsoOfRangeEq_hom_comp hLI hMr
  have hmono : Mono p := mono_grp_of_closed hPp
  have hkey : eM.hom ≫ fam.l I ≫ e.hom = l := by
    rw [← cancel_mono p]
    simp only [Category.assoc, he]
    exact heM
  have hUr : SubgroupFunctor.range (iU ≫ p) = SubgroupFunctor.range (fam.iU I ≫ fam.p I) :=
    (r.range_radical_eq_standardUnipotent' hG hU).trans (fam.range_radical_eq_standardUnipotent I).symm
  let c₂ : M' ⟶ fam.M I := c ≫ eM.hom
  have hw₂ : IsWeylConjugation (fam.p I) (fam.l I) q l' w c₂ := by
    have := hw.isIso
    refine ⟨inferInstanceAs (IsIso (c ≫ eM.hom)), ?_⟩
    change (c ≫ eM.hom) ≫ fam.l I ≫ fam.p I = _
    rw [Category.assoc, heM]
    exact hw.comp_eq
  have : IsClosedImmersion (fam.p I).hom.hom.left := hPI
  have := (⟨⟨r.data.T, r.data.i, r.data.ν, r.data.J, fam.f I⟩, fam.isCompatible I⟩ :
    ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I)).mono_groupHom_f
  refine ⟨c₂, hK.of_range_eq hrange.symm, hw₂, fun h => ?_⟩
  refine FamilyRegularComparison.of_sourceRange hG r.isCompatible (fam.isCompatible I) hA
    (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1 hT e he hrange.symm hUr hMr
    (fun lam => ?_) hK (hK.of_range_eq hrange.symm) hK' h
  change parameterRestrict (π' ≫ c₂ ≫ fam.l I) (parameterRestrict e.hom lam) =
    parameterRestrict (π' ≫ c ≫ l) lam
  rw [← LinearMap.comp_apply, ← parameterRestrict_comp,
    show (π' ≫ c₂ ≫ fam.l I) ≫ e.hom = π' ≫ c ≫ l by simp only [c₂, Category.assoc, hkey]]

end Langlands.Global
