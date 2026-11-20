import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteGermAssembly

/-! # Flatness and unramifiedness on finite pieces extend to all pieces

The Library has two finite-piece formulations of pointwise conditions on a strong map:
`HasFinitePiecesAt` (open finite neighborhoods and one finite family of recognized affinoid
target pieces) and `HasAllPiecesAt` (all recognized affinoid target pieces). For flatness at
a point these are the recognized-piece forms of Berkovich (1993), Proposition 3.2.3(a) and
(b), applied on open neighborhoods as in Definition 3.2.5. The Library proves (a) ⇒ (b) for
the joint condition `IsEtaleAtPoint` (`finitePiecesEtaleAllPieces`).

This module proves (a) ⇒ (b) separately for pointwise flatness, the recognized-piece version
of Proposition 3.2.3(a) ⇒ (b), and for pointwise unramifiedness. The unramified case is a
derived analogue, not a statement of Berkovich: it is proved from preservation and
reflection of unramifiedness across nested recognized pieces, by base change of
differentials and faithful flatness. Both cases instantiate a general finite-to-all lemma
that is conditional on invariance across nested recognized pieces. Consequently the Library's
finite-piece formulation `StrongHom.IsEtale` of the unramified-and-flat condition
(Definition 3.3.4, with the pointwise support description of Proposition 3.3.7(b)) implies
`StrongHom.IsEtaleAllPieces`, and the two agree.
-/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace PresentedAffinoidAlgebra.AffinoidPushout

open TensorProduct
open scoped TensorProduct

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

omit [CompleteSpace K] in
/-- Pointwise flatness reflects from the second leg of the actual affinoid pushout when
both domain structural maps are algebraically flat. -/
theorem isFlatAtPoint_of_rightMap
    (hg : g.toAlgHom.toRingHom.Flat)
    (hl : (leftMap f g).toAlgHom.toRingHom.Flat)
    (x : BanachSpectrum (algebra f g))
    (hx : (rightMap f g).IsFlatAtPoint x) :
    f.IsFlatAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra B (algebra f g) := (leftMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra A (algebra f g) :=
    ((rightMap f g).comp g).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A C (algebra f g) := .of_algebraMap_eq' rfl
  have : IsScalarTower A B (algebra f g) := .of_algebraMap_eq fun a =>
    congrArg (fun q : BoundedAlgHom K A (algebra f g) => q a) (condition f g).symm
  have : Module.Flat A C := hg
  have : Module.Flat B (algebra f g) := hl
  have hflat : Module.Flat C (Localization.AtPrime x.kernel) :=
    ((rightMap f g).isFlatAtPoint_iff_flat_atPrime x).1 hx
  exact (f.isFlatAtPoint_iff_flat_atPrime _).2
    (TensorStalkBaseChange.flat_atPrime_reflect (R := A) (S := B) (T := C) x.kernel hflat)

omit [CompleteSpace K] in
/-- Pointwise unramifiedness reflects from the second leg of the actual affinoid pushout
when the ordinary tensor comparison is bijective and the first leg is algebraically flat. -/
theorem isUnramifiedAtPoint_of_rightMap_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (hf : f.toAlgHom.toRingHom.FiniteType)
    (hl : (leftMap f g).toAlgHom.toRingHom.Flat)
    (x : BanachSpectrum (algebra f g))
    (hx : (rightMap f g).IsUnramifiedAtPoint x) :
    f.IsUnramifiedAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra B (algebra f g) := (leftMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let : Algebra A (algebra f g) :=
    ((rightMap f g).comp g).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A C (algebra f g) := .of_algebraMap_eq' rfl
  have : IsScalarTower A B (algebra f g) := .of_algebraMap_eq fun a =>
    congrArg (fun q : BoundedAlgHom K A (algebra f g) => q a) (condition f g).symm
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Algebra.IsPushout A C B (algebra f g) := by
    constructor
    change Function.Bijective _
    convert e.bijective using 1
    rfl
  have : Module.Flat B (algebra f g) := hl
  have : Algebra.FiniteType A B := hf
  have hr : (rightMap f g).toAlgHom.toRingHom.FiniteType :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  have hunr : Algebra.FormallyUnramified C (Localization.AtPrime x.kernel) :=
    ((rightMap f g).isUnramifiedAtPoint_iff_isUnramifiedAt hr x).1 hx
  exact (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf _).2
    (TensorStalkBaseChange.formallyUnramified_atPrime_reflect (R := A) (S := B) (T := C)
      x.kernel hunr)

omit [CompleteSpace K] in
/-- Pointwise flatness is preserved by the actual affinoid pushout when its ordinary
tensor comparison is bijective. -/
theorem rightMap_isFlatAtPoint_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (x : BanachSpectrum (algebra f g))
    (hx : f.IsFlatAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x)) :
    (rightMap f g).IsFlatAtPoint x := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  let q := (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x).kernel
  have hq : (x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom = q := by
    ext b
    change tensorComparison f g (tensorRight f g b) ∈ x.kernel ↔ leftMap f g b ∈ x.kernel
    rw [tensorComparison_tensorRight]
  have hqp : (⟨(x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom,
      inferInstance⟩ : PrimeSpectrum B) = ⟨q, inferInstance⟩ := PrimeSpectrum.ext hq
  have hflat : Module.Flat A (Localization.AtPrime q) :=
    (f.isFlatAtPoint_iff_flat_atPrime _).1 hx
  apply ((rightMap f g).isFlatAtPoint_iff_flat_atPrime x).2
  apply TensorStalkBaseChange.flat_atPrime_of_equiv e x.kernel
  exact (congrArg (fun p : PrimeSpectrum B =>
    Module.Flat A (Localization.AtPrime p.asIdeal)) hqp).mpr hflat

omit [CompleteSpace K] in
/-- Pointwise unramifiedness is preserved by the actual affinoid pushout of a finite type
map when its ordinary tensor comparison is bijective. -/
theorem rightMap_isUnramifiedAtPoint_of_tensorComparison
    (h : Function.Bijective (tensorComparison f g))
    (hf : f.toAlgHom.toRingHom.FiniteType)
    (x : BanachSpectrum (algebra f g))
    (hx : f.IsUnramifiedAtPoint (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x)) :
    (rightMap f g).IsUnramifiedAtPoint x := by
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra C (algebra f g) := (rightMap f g).toAlgHom.toRingHom.toAlgebra
  let e : C ⊗[A] B ≃ₐ[C] algebra f g :=
    { tensorComparisonEquiv f g h with
      commutes' := tensorComparison_tensorLeft f g }
  have : Algebra.FiniteType A B := hf
  have : Algebra.FiniteType C (C ⊗[A] B) := inferInstance
  have hr : (rightMap f g).toAlgHom.toRingHom.FiniteType :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  let q := (BanachSpectrum.comap (leftMap f g).toBoundedRingHom x).kernel
  have hq : (x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom = q := by
    ext b
    change tensorComparison f g (tensorRight f g b) ∈ x.kernel ↔ leftMap f g b ∈ x.kernel
    rw [tensorComparison_tensorRight]
  have hqp : (⟨(x.kernel.comap e.toRingHom).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom,
      inferInstance⟩ : PrimeSpectrum B) = ⟨q, inferInstance⟩ := PrimeSpectrum.ext hq
  have hunr : Algebra.FormallyUnramified A (Localization.AtPrime q) :=
    (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf _).1 hx
  apply ((rightMap f g).isUnramifiedAtPoint_iff_isUnramifiedAt hr x).2
  apply TensorStalkBaseChange.formallyUnramified_atPrime_of_equiv e x.kernel
  exact (congrArg (fun p : PrimeSpectrum B =>
    Algebra.FormallyUnramified A (Localization.AtPrime p.asIdeal)) hqp).mpr hunr

end PresentedAffinoidAlgebra.AffinoidPushout

namespace BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- A bounded change of target algebra preserves and reflects pointwise flatness at the
corresponding spectrum point. -/
theorem isFlatAtPoint_comp_boundedEquiv_iff
    (f : BoundedAlgHom K R S) (e : BoundedAlgEquiv K S T) (y : BanachSpectrum T) :
    (e.toBoundedAlgHom.comp f).IsFlatAtPoint y ↔
      f.IsFlatAtPoint (e.spectrumHomeomorph y) := by
  have he : e.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.bijective
  have hi : e.symm.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.symm.bijective
  constructor
  · intro hx
    have hp : BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
        (e.spectrumHomeomorph y) = y :=
      e.spectrumHomeomorph.symm_apply_apply y
    have hx' : (e.toBoundedAlgHom.comp f).IsFlatAtPoint
        (BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
          (e.spectrumHomeomorph y)) := hp.symm ▸ hx
    have hc := (hi.isEtaleAtPoint (e.spectrumHomeomorph y)).1.comp hx'
    have hcancel : e.symm.toBoundedAlgHom.comp (e.toBoundedAlgHom.comp f) = f := by
      apply BoundedAlgHom.ext
      intro r
      exact e.symm_apply_apply (f r)
    rw [hcancel] at hc
    exact hc
  · intro hx
    exact (he.isEtaleAtPoint y).1.comp hx

/-- A bounded change of target algebra preserves and reflects pointwise unramifiedness at
the corresponding spectrum point, for maps of finite type. -/
theorem isUnramifiedAtPoint_comp_boundedEquiv_iff
    (f : BoundedAlgHom K R S) (e : BoundedAlgEquiv K S T)
    (hf : f.toAlgHom.toRingHom.FiniteType) (y : BanachSpectrum T) :
    (e.toBoundedAlgHom.comp f).IsUnramifiedAtPoint y ↔
      f.IsUnramifiedAtPoint (e.spectrumHomeomorph y) := by
  have he : e.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.bijective
  have hi : e.symm.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    AlgebraicallyFiniteEtale.of_bijective _ e.symm.bijective
  have het := (algebraicallyFiniteEtale_iff _).1 he
  have hit := (algebraicallyFiniteEtale_iff _).1 hi
  constructor
  · intro hx
    have hp : BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
        (e.spectrumHomeomorph y) = y :=
      e.spectrumHomeomorph.symm_apply_apply y
    have hx' : (e.toBoundedAlgHom.comp f).IsUnramifiedAtPoint
        (BanachSpectrum.comap e.symm.toBoundedAlgHom.toBoundedRingHom
          (e.spectrumHomeomorph y)) := hp.symm ▸ hx
    have hc := IsUnramifiedAtPoint.comp hit.1.finiteType (het.1.finiteType.comp hf)
      (hi.isEtaleAtPoint (e.spectrumHomeomorph y)).2 hx'
    have hcancel : e.symm.toBoundedAlgHom.comp (e.toBoundedAlgHom.comp f) = f := by
      apply BoundedAlgHom.ext
      intro r
      exact e.symm_apply_apply (f r)
    rw [hcancel] at hc
    exact hc
  · intro hx
    exact IsUnramifiedAtPoint.comp het.1.finiteType hf (he.isEtaleAtPoint y).2 hx

end BoundedAlgHom

namespace AffinoidAtlasPresentation.StrongHom

open Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- Pointwise flatness across nested recognized inverse-image squares, with the domain
flatness and finite tensor comparison inputs stated explicitly. -/
theorem recognizedNested_isFlatAtPoint_iff
    (hflat : Domain.FlatnessStatement.{u})
    (hcomp : AffinoidPushout.FiniteTensorComparisonStatement K)
    (P₀ P : A.atlas.saturatedAtlas.RecognizedSubset)
    (W₀ W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h₀ : g.baseMap '' range P₀.chart ⊆ range W₀.chart)
    (h : g.baseMap '' range P.chart ⊆ range W.chart)
    (hW : W.locus ⊆ W₀.locus) (hP : P.locus ⊆ P₀.locus)
    (hpre : P.locus = P₀.locus ∩ g.baseMap ⁻¹' W.locus)
    (hf : (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsFiniteBanach)
    (t : BanachSpectrum P.algebra) :
    (g.fullRecognitionPairs.pullback P W h).IsFlatAtPoint t ↔
      (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsFlatAtPoint
        (BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t) := by
  let f := g.fullRecognitionPairs.pullback P₀ W₀ h₀
  let r := W.restriction W₀ hW
  let e := g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre
  let x := e.spectrumHomeomorph t
  have hc : Function.Bijective (AffinoidPushout.tensorComparison f r) :=
    hcomp W₀.algebra P₀.algebra W.algebra f r hf
  have ht := BoundedAlgHom.isFlatAtPoint_comp_boundedEquiv_iff
    (AffinoidPushout.rightMap f r) e t
  rw [← g.fullRecognitionPairs_nestedPullback_eq_pushout P₀ P W₀ W h₀ hW hP hpre h] at ht
  have hp : BanachSpectrum.comap (AffinoidPushout.leftMap f r).toBoundedRingHom x =
      BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t := by
    change BanachSpectrum.comap
      (e.toBoundedAlgHom.comp (AffinoidPushout.leftMap f r)).toBoundedRingHom t = _
    rw [g.recognizedNestedPullbackEquiv_comp_leftMap P₀ P W₀ W h₀ hW hP hpre]
    rfl
  constructor
  · intro he
    have hx := ht.mp he
    have hF := AffinoidPushout.isFlatAtPoint_of_rightMap f r
      (hflat K W₀.algebra (W.inclusionDomain W₀ hW))
      (hflat K P₀.algebra (Domain.pullback f (W.inclusionDomain W₀ hW))) x hx
    rw [hp] at hF
    exact hF
  · intro he
    apply ht.mpr
    apply AffinoidPushout.rightMap_isFlatAtPoint_of_tensorComparison f r hc x
    rw [hp]
    exact he

/-- Pointwise unramifiedness across nested recognized inverse-image squares, with the
domain flatness and finite tensor comparison inputs stated explicitly. -/
theorem recognizedNested_isUnramifiedAtPoint_iff
    (hflat : Domain.FlatnessStatement.{u})
    (hcomp : AffinoidPushout.FiniteTensorComparisonStatement K)
    (P₀ P : A.atlas.saturatedAtlas.RecognizedSubset)
    (W₀ W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h₀ : g.baseMap '' range P₀.chart ⊆ range W₀.chart)
    (h : g.baseMap '' range P.chart ⊆ range W.chart)
    (hW : W.locus ⊆ W₀.locus) (hP : P.locus ⊆ P₀.locus)
    (hpre : P.locus = P₀.locus ∩ g.baseMap ⁻¹' W.locus)
    (hf : (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsFiniteBanach)
    (t : BanachSpectrum P.algebra) :
    (g.fullRecognitionPairs.pullback P W h).IsUnramifiedAtPoint t ↔
      (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsUnramifiedAtPoint
        (BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t) := by
  let f := g.fullRecognitionPairs.pullback P₀ W₀ h₀
  let r := W.restriction W₀ hW
  let e := g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre
  let x := e.spectrumHomeomorph t
  have hc : Function.Bijective (AffinoidPushout.tensorComparison f r) :=
    hcomp W₀.algebra P₀.algebra W.algebra f r hf
  have hft : f.toAlgHom.toRingHom.FiniteType := hf.finite.finiteType
  have hrt := AffinoidPushout.rightMap_finiteType_of_tensorComparison f r hc hft
  have ht := BoundedAlgHom.isUnramifiedAtPoint_comp_boundedEquiv_iff
    (AffinoidPushout.rightMap f r) e hrt t
  rw [← g.fullRecognitionPairs_nestedPullback_eq_pushout P₀ P W₀ W h₀ hW hP hpre h] at ht
  have hp : BanachSpectrum.comap (AffinoidPushout.leftMap f r).toBoundedRingHom x =
      BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t := by
    change BanachSpectrum.comap
      (e.toBoundedAlgHom.comp (AffinoidPushout.leftMap f r)).toBoundedRingHom t = _
    rw [g.recognizedNestedPullbackEquiv_comp_leftMap P₀ P W₀ W h₀ hW hP hpre]
    rfl
  constructor
  · intro he
    have hx := ht.mp he
    have hF := AffinoidPushout.isUnramifiedAtPoint_of_rightMap_of_tensorComparison f r hc
      hft (hflat K P₀.algebra (Domain.pullback f (W.inclusionDomain W₀ hW))) x hx
    rw [hp] at hF
    exact hF
  · intro he
    apply ht.mpr
    apply AffinoidPushout.rightMap_isUnramifiedAtPoint_of_tensorComparison f r hc hft x
    rw [hp]
    exact he

/-- Finite-to-all transport for any pointwise property of finite affinoid maps that is
invariant across nested recognized inverse-image squares. -/
theorem hasAllPiecesAt_of_hasFinitePiecesAt_of_nested
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hQ : ∀ (P₀ P : A.atlas.saturatedAtlas.RecognizedSubset)
      (W₀ W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h₀ : g.baseMap '' range P₀.chart ⊆ range W₀.chart)
      (h : g.baseMap '' range P.chart ⊆ range W.chart)
      (_ : W.locus ⊆ W₀.locus) (hP : P.locus ⊆ P₀.locus),
      P.locus = P₀.locus ∩ g.baseMap ⁻¹' W.locus →
      (g.fullRecognitionPairs.pullback P₀ W₀ h₀).IsFiniteBanach →
      ∀ t : BanachSpectrum P.algebra,
        Q (g.fullRecognitionPairs.pullback P W h) t ↔
          Q (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
            (BanachSpectrum.comap (P.restriction P₀ hP).toBoundedRingHom t))
    {y : A.space} (hg : g.HasFinitePiecesAt Q y) : g.HasAllPiecesAt Q y := by
  obtain ⟨V, U, hV, hU, hy, hfin, I, hIfin, hIU, hIN, hIQ⟩ := hg
  obtain ⟨W₀, hW₀I, hxW₀⟩ := Set.mem_iUnion₂.mp (mem_of_mem_nhds hIN)
  obtain ⟨P₀, h₀, hP₀, hf₀⟩ := hfin.2 W₀ (hIU W₀ hW₀I).1
  refine ⟨V, U, hV, hU, hy, hfin, ?_⟩
  intro W hWU hxW P h hP s hs
  obtain ⟨P', h', hP', hf'⟩ := hfin.2 W hWU
  have hPP' : P = P' := Subtype.ext (Subtype.ext (hP.trans hP'.symm))
  have hf : (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach := by
    subst hPP'
    exact hf'
  have hxW₀' : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart W₀) :=
    W₀.range_chart.symm ▸ hxW₀
  have hxW' : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart W) :=
    W.range_chart.symm ▸ hxW
  obtain ⟨Z, hZsub, hxZ⟩ :=
    IndexedAffinoidAtlas.exists_chart_inter
      (a := B.atlas.fullRecognitionAtlas) hxW₀' hxW'
  change B.atlas.saturatedAtlas.RecognizedSubset at Z
  change range Z.chart ⊆ range W₀.chart ∩ range W.chart at hZsub
  change g.baseMap y ∈ range Z.chart at hxZ
  rw [Z.range_chart, W₀.range_chart, W.range_chart] at hZsub
  rw [Z.range_chart] at hxZ
  have hZW₀ : Z.locus ⊆ W₀.locus := hZsub.trans inter_subset_left
  have hZW : Z.locus ⊆ W.locus := hZsub.trans inter_subset_right
  obtain ⟨R, hR, hRpre, -⟩ := hfin.2 Z (hZW.trans hWU)
  have hRP₀ : R.locus ⊆ P₀.locus := by
    rw [hRpre, hP₀]
    exact fun _ hz => ⟨hz.1, hZW₀ hz.2⟩
  have hRP : R.locus ⊆ P.locus := by
    rw [hRpre, hP]
    exact fun _ hz => ⟨hz.1, hZW hz.2⟩
  have hR₀ : R.locus = P₀.locus ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hRpre, hP₀]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1, hZW₀ hz.2⟩, hz.2⟩,
      fun hz => ⟨hz.1.1, hz.2⟩⟩
  have hRP' : R.locus = P.locus ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hRpre, hP]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1, hZW hz.2⟩, hz.2⟩,
      fun hz => ⟨hz.1.1, hz.2⟩⟩
  have hyR : y ∈ range R.chart := by
    rw [R.range_chart, hRpre]
    exact ⟨hy, hxZ⟩
  obtain ⟨t, ht⟩ := hyR
  have ht₀ : P₀.chart
      (BanachSpectrum.comap (R.restriction P₀ hRP₀).toBoundedRingHom t) = y :=
    (R.chart_restriction P₀ hRP₀ t).trans ht
  have hQ₀ := hIQ W₀ hW₀I P₀ h₀ hP₀ _ ht₀
  have hQR := (hQ P₀ R W₀ Z h₀ hR hZW₀ hRP₀ hR₀ hf₀ t).mpr hQ₀
  have hQP := (hQ P R W Z h hR hZW hRP hRP' hf t).mp hQR
  have hts : BanachSpectrum.comap (R.restriction P hRP).toBoundedRingHom t = s := by
    apply P.isEmbedding_chart.injective
    exact (R.chart_restriction P hRP t).trans (ht.trans hs.symm)
  exact (congrArg (fun z : BanachSpectrum P.algebra =>
    Q (g.fullRecognitionPairs.pullback P W h) z) hts).mp hQP

/-- The recognized-piece version of Berkovich (1993), Proposition 3.2.3, (a) ⇒ (b), used in
Definition 3.2.5: flatness at a point on one finite family of pieces over open finite
neighborhoods gives flatness at that point on all recognized pieces. -/
theorem IsFlatAt.isFlatAtAllPieces {y : A.space} (hg : g.IsFlatAt y) :
    g.IsFlatAtAllPieces y :=
  g.hasAllPiecesAt_of_hasFinitePiecesAt_of_nested
    (fun P₀ P W₀ W h₀ h hW hP hpre hf t =>
      g.recognizedNested_isFlatAtPoint_iff PresentedAffinoidAlgebra.Domain.flatness
        (AffinoidPushout.finiteTensorComparison (K := K)) P₀ P W₀ W h₀ h hW hP hpre hf t) hg

/-- The finite-to-all upgrade for pointwise unramifiedness. This is a derived analogue of
the flat case, obtained from `hasAllPiecesAt_of_hasFinitePiecesAt_of_nested` and the nested
invariance of unramifiedness (base change of differentials and faithful flatness). -/
theorem IsUnramifiedAt.isUnramifiedAtAllPieces {y : A.space} (hg : g.IsUnramifiedAt y) :
    g.IsUnramifiedAtAllPieces y :=
  g.hasAllPiecesAt_of_hasFinitePiecesAt_of_nested
    (fun P₀ P W₀ W h₀ h hW hP hpre hf t =>
      g.recognizedNested_isUnramifiedAtPoint_iff PresentedAffinoidAlgebra.Domain.flatness
        (AffinoidPushout.finiteTensorComparison (K := K)) P₀ P W₀ W h₀ h hW hP hpre hf t) hg

/-- A strong map satisfying the Library's finite-piece formulation `IsEtale` of the
unramified-and-flat condition of Berkovich's Definition 3.3.4 is étale over all recognized
affinoid pieces. -/
theorem IsEtale.isEtaleAllPieces {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsEtale) : g.IsEtaleAllPieces :=
  fun _ => ⟨univ, isOpen_univ, mem_univ _, fun y' _ =>
    ⟨IsUnramifiedAt.isUnramifiedAtAllPieces g (hg.1 y'),
      IsFlatAt.isFlatAtAllPieces g (hg.2 y')⟩⟩

/-- The finite-pieces and all-pieces notions of étale strong maps agree. -/
theorem isEtale_iff_isEtaleAllPieces : g.IsEtale ↔ g.IsEtaleAllPieces :=
  ⟨IsEtale.isEtaleAllPieces, IsEtaleAllPieces.isEtale⟩

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
