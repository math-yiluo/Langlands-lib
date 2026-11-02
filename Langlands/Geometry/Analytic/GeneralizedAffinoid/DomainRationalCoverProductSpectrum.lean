import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProduct
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-! # The actual spectrum pullback of a mixed finite-cover product -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A}

private theorem rationalInter_spectrum_exists (V : Domain K A) (d : RationalChart K A)
    (x : BanachSpectrum V.algebra) (y : BanachSpectrum d.algebra)
    (hxy : V.spectrumMap x = d.spectrumMap y) :
    ∃ z : BanachSpectrum (V.rationalInter d).algebra,
      (V.rationalInterLeft d).spectrumMap z = x ∧
        (V.rationalInterRight d).spectrumMap z = y := by
  have hx : x ∈ (RationalChart.pullback V.baseMap d).locus := by
    rw [RationalChart.pullback_locus]
    change V.spectrumMap x ∈ d.locus
    rw [hxy]
    exact (d.locusHomeomorph y).property
  let z := (RationalChart.pullback V.baseMap d).locusHomeomorph.symm ⟨x, hx⟩
  have hz : (V.rationalInterLeft d).spectrumMap z = x :=
    congrArg Subtype.val
      ((RationalChart.pullback V.baseMap d).locusHomeomorph.apply_symm_apply ⟨x, hx⟩)
  refine ⟨z, hz, ?_⟩
  apply d.locusHomeomorph.injective
  apply Subtype.ext
  change d.spectrumMap ((V.rationalInterRight d).spectrumMap z) = d.spectrumMap y
  calc
    _ = (V.rationalInter d).spectrumMap z :=
      (V.rationalInterRight d).spectrumMap_over_base z
    _ = V.spectrumMap ((V.rationalInterLeft d).spectrumMap z) :=
      ((V.rationalInterLeft d).spectrumMap_over_base z).symm
    _ = V.spectrumMap x := congrArg V.spectrumMap hz
    _ = d.spectrumMap y := hxy

namespace FiniteCover

/-- The finite disjoint union of the actual representing spectra. -/
abbrev TotalSpectrum (c : FiniteCover U) :=
  Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra

/-- Compatible pairs of actual total spectrum points over the original target
locus, with the subspace topology from the product of the two disjoint unions. -/
abbrev RationalProductSpectrumFiber (c : FiniteCover U) (r : FiniteRationalCover U) :=
  {p : c.TotalSpectrum × r.toFiniteCover.TotalSpectrum //
    c.totalMap p.1 = r.toFiniteCover.totalMap p.2}

private theorem rationalProductSpectrum_compatible (c : FiniteCover U)
    (r : FiniteRationalCover U) (x : (c.rationalProduct r).TotalSpectrum) :
    c.totalMap ((c.rationalProductFst r).spectrumMap x) =
      r.toFiniteCover.totalMap ((c.rationalProductSnd r).spectrumMap x) :=
  (ContinuousMap.congr_fun (c.rationalProduct_totalMap_fst r) x).trans
    (ContinuousMap.congr_fun (c.rationalProduct_totalMap_snd r) x).symm

/-- The actual bounded projection maps define the comparison with the concrete
topological fiber product of the original spectrum-cover maps. -/
def rationalProductSpectrumComparison (c : FiniteCover U) (r : FiniteRationalCover U) :
    C((c.rationalProduct r).TotalSpectrum, c.RationalProductSpectrumFiber r) :=
  ⟨fun x => ⟨⟨(c.rationalProductFst r).spectrumMap x,
      (c.rationalProductSnd r).spectrumMap x⟩,
    rationalProductSpectrum_compatible c r x⟩,
    ((c.rationalProductFst r).spectrumMap.continuous.prodMk
      (c.rationalProductSnd r).spectrumMap.continuous).subtype_mk _⟩

theorem rationalProductSpectrumComparison_injective (c : FiniteCover U)
    (r : FiniteRationalCover U) :
    Function.Injective (c.rationalProductSpectrumComparison r) := by
  rintro ⟨k, x⟩ ⟨l, y⟩ h
  have hf := congrArg (fun z : c.RationalProductSpectrumFiber r => z.val.1) h
  have hs := congrArg (fun z : c.RationalProductSpectrumFiber r => z.val.2) h
  have hkl : k = l := by
    apply (c.rationalProductIndexEquiv r).injective
    apply Prod.ext
    · exact congrArg Sigma.fst hf
    · exact congrArg Sigma.fst hs
  subst l
  have hxy : ((c.rationalProductFst r).map k).spectrumMap x =
      ((c.rationalProductFst r).map k).spectrumMap y :=
    eq_of_heq (Sigma.mk.inj hf).2
  have heq : x = y := by
    apply (RationalChart.pullback
      (c.obj (c.rationalProductIndexEquiv r k).1).baseMap
      (r.chart (c.rationalProductIndexEquiv r k).2)).locusHomeomorph.injective
    exact Subtype.ext hxy
  cases heq
  rfl

theorem rationalProductSpectrumComparison_surjective (c : FiniteCover U)
    (r : FiniteRationalCover U) :
    Function.Surjective (c.rationalProductSpectrumComparison r) := by
  rintro ⟨⟨⟨i, x⟩, ⟨j, y⟩⟩, h⟩
  let k := c.rationalProductIndex r i j
  have hk := c.rationalProductIndexEquiv_index r i j
  have hxy : (c.obj i).spectrumMap x = (r.chart j).spectrumMap y :=
    congrArg Subtype.val h
  have hex : ∃ z : BanachSpectrum ((c.rationalProduct r).obj k).algebra,
      (c.rationalProductFst r).spectrumMap ⟨k, z⟩ = ⟨i, x⟩ ∧
        (c.rationalProductSnd r).spectrumMap ⟨k, z⟩ = ⟨j, y⟩ := by
    change ∃ z : BanachSpectrum
        ((c.obj (c.rationalProductIndexEquiv r k).1).rationalInter
          (r.chart (c.rationalProductIndexEquiv r k).2)).algebra,
      (⟨(c.rationalProductIndexEquiv r k).1,
        ((c.obj (c.rationalProductIndexEquiv r k).1).rationalInterLeft
          (r.chart (c.rationalProductIndexEquiv r k).2)).spectrumMap z⟩ :
        c.TotalSpectrum) = ⟨i, x⟩ ∧
      (⟨(c.rationalProductIndexEquiv r k).2,
        ((c.obj (c.rationalProductIndexEquiv r k).1).rationalInterRight
          (r.chart (c.rationalProductIndexEquiv r k).2)).spectrumMap z⟩ :
        r.toFiniteCover.TotalSpectrum) = ⟨j, y⟩
    rw [show c.rationalProductIndexEquiv r k = (i, j) from hk]
    obtain ⟨z, hz, hz'⟩ := rationalInter_spectrum_exists (c.obj i) (r.chart j) x y hxy
    exact ⟨z, congrArg (Sigma.mk i) hz, congrArg (Sigma.mk j) hz'⟩
  obtain ⟨z, hz, hz'⟩ := hex
  refine ⟨⟨k, z⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hz hz'

/-- The comparison is a homeomorphism: its source is a finite sum of compact
actual spectra, and its target is a subspace of a Hausdorff product. -/
def rationalProductSpectrumHomeomorph (c : FiniteCover U) (r : FiniteRationalCover U) :
    (c.rationalProduct r).TotalSpectrum ≃ₜ c.RationalProductSpectrumFiber r :=
  (Equiv.ofBijective (c.rationalProductSpectrumComparison r)
    ⟨c.rationalProductSpectrumComparison_injective r,
      c.rationalProductSpectrumComparison_surjective r⟩).toHomeomorphOfContinuousClosed
    (c.rationalProductSpectrumComparison r).continuous
    (c.rationalProductSpectrumComparison r).continuous.isClosedMap

@[simp] theorem rationalProductSpectrumHomeomorph_fst (c : FiniteCover U)
    (r : FiniteRationalCover U) (x : (c.rationalProduct r).TotalSpectrum) :
    (c.rationalProductSpectrumHomeomorph r x).val.1 =
      (c.rationalProductFst r).spectrumMap x := rfl

@[simp] theorem rationalProductSpectrumHomeomorph_snd (c : FiniteCover U)
    (r : FiniteRationalCover U) (x : (c.rationalProduct r).TotalSpectrum) :
    (c.rationalProductSpectrumHomeomorph r x).val.2 =
      (c.rationalProductSnd r).spectrumMap x := rfl

@[simp] theorem rationalProductSpectrumHomeomorph_symm_fst (c : FiniteCover U)
    (r : FiniteRationalCover U) (p : c.RationalProductSpectrumFiber r) :
    (c.rationalProductFst r).spectrumMap ((c.rationalProductSpectrumHomeomorph r).symm p) =
      p.val.1 :=
  congrArg (fun q : c.RationalProductSpectrumFiber r => q.val.1)
    ((c.rationalProductSpectrumHomeomorph r).apply_symm_apply p)

@[simp] theorem rationalProductSpectrumHomeomorph_symm_snd (c : FiniteCover U)
    (r : FiniteRationalCover U) (p : c.RationalProductSpectrumFiber r) :
    (c.rationalProductSnd r).spectrumMap ((c.rationalProductSpectrumHomeomorph r).symm p) =
      p.val.2 :=
  congrArg (fun q : c.RationalProductSpectrumFiber r => q.val.2)
    ((c.rationalProductSpectrumHomeomorph r).apply_symm_apply p)

/-- Compatible continuous maps lift into the actual mixed-cover spectrum. -/
def rationalProductSpectrumLift {X : Type v} [TopologicalSpace X]
    (c : FiniteCover U) (r : FiniteRationalCover U)
    (f : C(X, c.TotalSpectrum)) (g : C(X, r.toFiniteCover.TotalSpectrum))
    (h : ∀ x, c.totalMap (f x) = r.toFiniteCover.totalMap (g x)) :
    C(X, (c.rationalProduct r).TotalSpectrum) :=
  (⟨(c.rationalProductSpectrumHomeomorph r).symm,
    (c.rationalProductSpectrumHomeomorph r).symm.continuous⟩ :
    C(c.RationalProductSpectrumFiber r, (c.rationalProduct r).TotalSpectrum)).comp
    ⟨fun x => ⟨(f x, g x), h x⟩,
      (f.continuous.prodMk g.continuous).subtype_mk _⟩

@[simp] theorem rationalProductSpectrumLift_fst {X : Type v} [TopologicalSpace X]
    (c : FiniteCover U) (r : FiniteRationalCover U)
    (f : C(X, c.TotalSpectrum)) (g : C(X, r.toFiniteCover.TotalSpectrum))
    (h : ∀ x, c.totalMap (f x) = r.toFiniteCover.totalMap (g x)) :
    (c.rationalProductFst r).spectrumMap.comp (c.rationalProductSpectrumLift r f g h) = f := by
  apply ContinuousMap.ext
  intro x
  exact c.rationalProductSpectrumHomeomorph_symm_fst r ⟨(f x, g x), h x⟩

@[simp] theorem rationalProductSpectrumLift_snd {X : Type v} [TopologicalSpace X]
    (c : FiniteCover U) (r : FiniteRationalCover U)
    (f : C(X, c.TotalSpectrum)) (g : C(X, r.toFiniteCover.TotalSpectrum))
    (h : ∀ x, c.totalMap (f x) = r.toFiniteCover.totalMap (g x)) :
    (c.rationalProductSnd r).spectrumMap.comp (c.rationalProductSpectrumLift r f g h) = g := by
  apply ContinuousMap.ext
  intro x
  exact c.rationalProductSpectrumHomeomorph_symm_snd r ⟨(f x, g x), h x⟩

/-- The vertex is the finite sum of actual pulled rational quotient spectra;
the legs are induced by the actual bounded projection restrictions. -/
def rationalProductSpectrumCone (c : FiniteCover U) (r : FiniteRationalCover U) :
    PullbackCone (TopCat.ofHom c.totalMap) (TopCat.ofHom r.toFiniteCover.totalMap) :=
  PullbackCone.mk (TopCat.ofHom (c.rationalProductFst r).spectrumMap)
    (TopCat.ofHom (c.rationalProductSnd r).spectrumMap) (by
      apply TopCat.ext
      exact rationalProductSpectrum_compatible c r)

@[simp] theorem rationalProductSpectrumCone_pt (c : FiniteCover U)
    (r : FiniteRationalCover U) :
    (c.rationalProductSpectrumCone r).pt =
      TopCat.of (c.rationalProduct r).TotalSpectrum := rfl

@[simp] theorem rationalProductSpectrumCone_fst (c : FiniteCover U)
    (r : FiniteRationalCover U) :
    (c.rationalProductSpectrumCone r).fst =
      TopCat.ofHom (c.rationalProductFst r).spectrumMap := rfl

@[simp] theorem rationalProductSpectrumCone_snd (c : FiniteCover U)
    (r : FiniteRationalCover U) :
    (c.rationalProductSpectrumCone r).snd =
      TopCat.ofHom (c.rationalProductSnd r).spectrumMap := rfl

/-- The actual spectrum square is a pullback in the category of topological
spaces, including when either finite cover is empty. -/
def rationalProductSpectrumConeIsLimit (c : FiniteCover U) (r : FiniteRationalCover U) :
    IsLimit (c.rationalProductSpectrumCone r) := by
  apply PullbackCone.isLimitAux'
  intro s
  let h : ∀ x : s.pt, c.totalMap (s.fst x) = r.toFiniteCover.totalMap (s.snd x) :=
    fun x => ConcreteCategory.congr_hom s.condition x
  let l := c.rationalProductSpectrumLift r s.fst.hom s.snd.hom h
  refine ⟨TopCat.ofHom l, ?_, ?_, ?_⟩
  · apply TopCat.ext
    intro x
    exact ContinuousMap.congr_fun (c.rationalProductSpectrumLift_fst r s.fst.hom s.snd.hom h) x
  · apply TopCat.ext
    intro x
    exact ContinuousMap.congr_fun (c.rationalProductSpectrumLift_snd r s.fst.hom s.snd.hom h) x
  · intro m hm₁ hm₂
    apply TopCat.ext
    intro x
    apply c.rationalProductSpectrumComparison_injective r
    apply Subtype.ext
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom hm₁ x).trans
        (ContinuousMap.congr_fun
          (c.rationalProductSpectrumLift_fst r s.fst.hom s.snd.hom h) x).symm
    · exact (ConcreteCategory.congr_hom hm₂ x).trans
        (ContinuousMap.congr_fun
          (c.rationalProductSpectrumLift_snd r s.fst.hom s.snd.hom h) x).symm

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
