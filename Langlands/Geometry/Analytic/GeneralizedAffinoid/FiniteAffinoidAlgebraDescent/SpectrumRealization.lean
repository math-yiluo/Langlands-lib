import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.EffectiveData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange

/-! # Spectral effectiveness from the original bounded base-change comparisons -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  {t : PairTransitions F}

namespace MatchingPresentation

variable (P : MatchingPresentation t)

/-- The original comparison source is the actual inverse-image full domain,
retaining the stored cover restriction. -/
def originalDomain (i : Fin c.size) : Domain K P.algebra where
  algebra := P.originalBaseChange i
  baseMap := AffinoidPushout.leftMap P.baseMap (c.map i).restriction
  locus := P.preimageLocus i
  represents := by
    have hi : (c.map i).restriction = (c.obj i).baseMap := (c.map i).comp_baseMap
    change Represents K (AffinoidPushout.leftMap P.baseMap (c.map i).restriction)
      (P.preimageLocus i)
    rw [hi]
    exact Domain.represents_pullback P.baseMap (c.obj i)

/-- A canonical original comparison equivalence identifies the local spectrum
with the entire inverse image of its original base-domain locus. -/
def localSpectrumEquivOfComparison (i : Fin c.size)
    (e : BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i)) :
    BanachSpectrum (F.algebra i) ≃ₜ P.preimageLocus i :=
  e.spectrumHomeomorph.trans (P.originalDomain i).locusHomeomorph

theorem localSpectrumEquivOfComparison_eq (i : Fin c.size)
    (e : BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
    (he : e.toBoundedAlgHom = P.comparison i) (x : BanachSpectrum (F.algebra i)) :
    P.localSpectrumEquivOfComparison i e x = P.localSpectrumMap i x := by
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  change x (e (AffinoidPushout.leftMap P.baseMap (c.map i).restriction a)) =
    x (P.localMap i a)
  exact congrArg (fun f : BoundedAlgHom K P.algebra (F.algebra i) => x (f a))
    ((congrArg (fun f => f.comp
      (AffinoidPushout.leftMap P.baseMap (c.map i).restriction)) he).trans
        (P.comparison_left i))

theorem localMap_overlap (i j : Fin c.size) :
    (t.leftRestriction i j).comp (P.localMap i) =
      (t.rightRestriction i j).comp (P.localMap j) := by
  apply BoundedAlgHom.ext
  intro a
  exact congrArg (fun f : BoundedAlgHom K t.MatchingAlgebra
    (F.baseChange j (F.overlap i j) (F.overlapRight i j)) => f (P.equiv a))
      (t.projection_overlap i j)

/-- The whole-map overlap compatibility already follows from the defining
matching equations, independently of any effectiveness theorem. -/
theorem overlapCompatible : P.OverlapCompatible := by
  intro i j
  apply AffinoidPushout.hom_ext P.baseMap (F.overlap i j).baseMap
  · rw [BoundedAlgHom.comp_assoc, P.restrictedComparison_left,
      P.restrictedComparison_left, ← BoundedAlgHom.comp_assoc]
    exact P.localMap_overlap i j
  · rw [BoundedAlgHom.comp_assoc, P.restrictedComparison_right,
      P.restrictedComparison_right, t.over_base]

/-- The canonical local maps are injective once the original base changes
are known to be effective; no finite-map spectral injectivity is assumed. -/
theorem localSpectrumMap_injective_of_comparison (i : Fin c.size)
    (e : BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
    (he : e.toBoundedAlgHom = P.comparison i) :
    Function.Injective (P.localSpectrumMap i) := by
  have hmap : (P.localSpectrumEquivOfComparison i e :
      BanachSpectrum (F.algebra i) → P.preimageLocus i) = P.localSpectrumMap i :=
    funext (P.localSpectrumEquivOfComparison_eq i e he)
  rw [← hmap]
  exact (P.localSpectrumEquivOfComparison i e).injective

theorem localSpectrumMap_surjective_of_comparison (i : Fin c.size)
    (e : BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
    (he : e.toBoundedAlgHom = P.comparison i) :
    Function.Surjective (P.localSpectrumMap i) := by
  have hmap : (P.localSpectrumEquivOfComparison i e :
      BanachSpectrum (F.algebra i) → P.preimageLocus i) = P.localSpectrumMap i :=
    funext (P.localSpectrumEquivOfComparison_eq i e he)
  rw [← hmap]
  exact (P.localSpectrumEquivOfComparison i e).surjective

/-- The canonical local spectral map retains the original coefficient square. -/
theorem localSpectrumMap_over_base (i : Fin c.size)
    (x : BanachSpectrum (F.algebra i)) :
    BanachSpectrum.comap P.baseMap.toBoundedRingHom
        (BanachSpectrum.comap (P.localMap i).toBoundedRingHom x) =
      (c.obj i).spectrumMap (BanachSpectrum.comap (F.map i).toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro r
  exact congrArg (fun f : BoundedAlgHom K R (F.algebra i) => x (f r))
    ((P.localMap_baseMap i).trans (F.structuralMap_eq i))

variable
  (e : ∀ i, BoundedAlgEquiv K (P.originalBaseChange i) (F.algebra i))
  (he : ∀ i, (e i).toBoundedAlgHom = P.comparison i)

include e he

/-- The original finite base-domain cover gives surjectivity onto the entire
presented spectrum once its canonical local base changes are effective. -/
theorem spectrumMap_surjective_of_comparison : Function.Surjective P.spectrumMap := by
  intro x
  obtain ⟨i, hi⟩ := c.covers (BanachSpectrum.comap P.baseMap.toBoundedRingHom x)
    (Set.mem_univ _)
  obtain ⟨y, hy⟩ := P.localSpectrumMap_surjective_of_comparison i (e i) (he i) ⟨x, hi⟩
  refine ⟨t.glue i y, (P.spectrumMap_glue i y).trans ?_⟩
  exact congrArg Subtype.val hy

/-- Two local points with the same global image are related by an actual
original overlap point. This uses local full-domain injectivity, never
injectivity of a finite map to its base. -/
theorem overlapRelation_of_spectrum_eq (i j : Fin c.size)
    (x : BanachSpectrum (F.algebra i)) (y : BanachSpectrum (F.algebra j))
    (hxy : BanachSpectrum.comap (P.localMap i).toBoundedRingHom x =
      BanachSpectrum.comap (P.localMap j).toBoundedRingHom y) :
    t.OverlapRelation ⟨i, x⟩ ⟨j, y⟩ := by
  let s := BanachSpectrum.comap P.baseMap.toBoundedRingHom
    (BanachSpectrum.comap (P.localMap j).toBoundedRingHom y)
  have hsi : s ∈ (c.obj i).locus := by
    have hx := P.localSpectrumMap_mem i x
    change BanachSpectrum.comap P.baseMap.toBoundedRingHom
      (BanachSpectrum.comap (P.localMap i).toBoundedRingHom x) ∈ (c.obj i).locus at hx
    rwa [hxy] at hx
  have hsj : s ∈ (c.obj j).locus := P.localSpectrumMap_mem j y
  obtain ⟨w, hw⟩ := (F.overlap i j).spectrumToLocus_surjective ⟨s, hsi, hsj⟩
  have hws : (F.overlap i j).spectrumMap w = s := congrArg Subtype.val hw
  have hwy : BanachSpectrum.comap (restriction (F.overlapRight i j)).toBoundedRingHom w =
      BanachSpectrum.comap (F.map j).toBoundedRingHom y := by
    apply (c.obj j).spectrumMap_injective
    calc
      _ = (F.overlap i j).spectrumMap w := by
        apply BanachSpectrum.ext
        intro r
        exact congrArg (fun f : BoundedAlgHom K R (F.overlap i j).algebra => w (f r))
          (restriction_baseMap (F.overlapRight i j))
      _ = s := hws
      _ = _ := P.localSpectrumMap_over_base j y
  obtain ⟨z, hzy, _⟩ := AffinoidPushout.exists_point (F.map j)
    (restriction (F.overlapRight i j)) y w hwy.symm
  change BanachSpectrum.comap (t.rightRestriction i j).toBoundedRingHom z = y at hzy
  have hzglobal : BanachSpectrum.comap (P.localMap i).toBoundedRingHom
        (BanachSpectrum.comap (t.leftRestriction i j).toBoundedRingHom z) =
      BanachSpectrum.comap (P.localMap j).toBoundedRingHom
        (BanachSpectrum.comap (t.rightRestriction i j).toBoundedRingHom z) := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun f : BoundedAlgHom K P.algebra
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) => z (f a))
        (P.localMap_overlap i j)
  have hzx : BanachSpectrum.comap (t.leftRestriction i j).toBoundedRingHom z = x := by
    apply P.localSpectrumMap_injective_of_comparison i (e i) (he i)
    apply Subtype.ext
    change BanachSpectrum.comap (P.localMap i).toBoundedRingHom
      (BanachSpectrum.comap (t.leftRestriction i j).toBoundedRingHom z) =
        BanachSpectrum.comap (P.localMap i).toBoundedRingHom x
    rw [hzglobal, hzy]
    exact hxy.symm
  exact ⟨i, j, z, congrArg (Sigma.mk i) hzx.symm, congrArg (Sigma.mk j) hzy.symm⟩

theorem spectrumMap_injective_of_comparison : Function.Injective P.spectrumMap := by
  intro a b
  induction a using Quot.inductionOn with
  | h a =>
    induction b using Quot.inductionOn with
    | h b =>
      obtain ⟨i, x⟩ := a
      obtain ⟨j, y⟩ := b
      intro hxy
      apply Quot.sound
      apply P.overlapRelation_of_spectrum_eq e he i j x y
      exact hxy

/-- The canonical map from the entire original quotient gluing is a
homeomorphism as soon as the original bounded comparisons are effective. -/
def spectrumEquivOfComparison :
    t.GluedSpectrum ≃ₜ BanachSpectrum P.algebra :=
  (Equiv.ofBijective P.spectrumMap
    ⟨P.spectrumMap_injective_of_comparison e he,
      P.spectrumMap_surjective_of_comparison e he⟩).toHomeomorphOfContinuousClosed
        P.spectrumMap.continuous P.spectrumMap.continuous.isClosedMap

@[simp] theorem spectrumEquivOfComparison_eq (x : t.GluedSpectrum) :
    P.spectrumEquivOfComparison e he x = P.spectrumMap x := rfl

end MatchingPresentation

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent
