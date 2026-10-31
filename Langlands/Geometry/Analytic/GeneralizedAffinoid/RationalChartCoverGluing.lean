import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainCoverLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverDescent

/-! # Continuous finite-cover gluing inside actual rational charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
variable {Y : Type v} [TopologicalSpace Y]

/-- The inverse locus comparison lifts each actual ambient spectrum point. -/
theorem extendDomainLocusHomeomorph_symm_spectrumMap (d : RationalChart K A)
    (U : Domain K d.algebra) (x : (d.extendDomain U).locus) :
    d.spectrumMap ((d.extendDomainLocusHomeomorph U).symm x) = x :=
  congrArg (fun z : (d.extendDomain U).locus => (z : BanachSpectrum A))
    ((d.extendDomainLocusHomeomorph U).apply_symm_apply x)

/-- The component comparisons commute with actual extended inclusions. -/
theorem extendDomainLocusHomeomorph_naturality (d : RationalChart K A)
    {U V : Domain K d.algebra} (f : U ⟶ V) (x : U.locus) :
    d.extendDomainLocusHomeomorph V (f.locusMap x) =
      (d.extendDomainFunctor.map f).locusMap (d.extendDomainLocusHomeomorph U x) :=
  Subtype.ext rfl

theorem extendDomainLocusHomeomorph_symm_naturality (d : RationalChart K A)
    {U V : Domain K d.algebra} (f : U ⟶ V) (x : (d.extendDomain U).locus) :
    (d.extendDomainLocusHomeomorph V).symm
        ((d.extendDomainFunctor.map f).locusMap x) =
      f.locusMap ((d.extendDomainLocusHomeomorph U).symm x) := by
  apply Subtype.ext
  apply d.spectrumMap_injective
  exact (d.extendDomainLocusHomeomorph_symm_spectrumMap V
    ((d.extendDomainFunctor.map f).locusMap x)).trans
      (d.extendDomainLocusHomeomorph_symm_spectrumMap U x).symm

/-- Transport inner continuous maps by the inverse component homeomorphisms. -/
def extendCoverFamily (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    ∀ i : Fin (d.extendFiniteCover c).size,
      C(((d.extendFiniteCover c).obj i).locus, Y) :=
  fun i => (g i).comp ((d.extendDomainLocusHomeomorph (c.obj i)).symm :
    C((d.extendDomain (c.obj i)).locus, (c.obj i).locus))

/-- The inverse family uses the forward actual spectrum comparisons. -/
def extendCoverFamilyInverse (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (d.extendFiniteCover c).size,
      C(((d.extendFiniteCover c).obj i).locus, Y)) :
    ∀ i : Fin c.size, C((c.obj i).locus, Y) :=
  fun i => (g i).comp (d.extendDomainLocusHomeomorph (c.obj i) :
    C((c.obj i).locus, (d.extendDomain (c.obj i)).locus))

theorem compatible_extendCoverFamily (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (d.extendFiniteCover c).Compatible (d.extendCoverFamily c g) := by
  intro i j x y h
  apply hg i j
  apply d.spectrumMap_injective
  exact (d.extendDomainLocusHomeomorph_symm_spectrumMap (c.obj i) x).trans
    (h.trans (d.extendDomainLocusHomeomorph_symm_spectrumMap (c.obj j) y).symm)

theorem compatible_extendCoverFamilyInverse (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (d.extendFiniteCover c).size,
      C(((d.extendFiniteCover c).obj i).locus, Y))
    (hg : (d.extendFiniteCover c).Compatible g) :
    c.Compatible (d.extendCoverFamilyInverse c g) := by
  intro i j x y h
  exact hg i j _ _ (congrArg d.spectrumMap h)

@[simp] theorem extendCoverFamilyInverse_extendCoverFamily (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.extendCoverFamilyInverse c (d.extendCoverFamily c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i) ((d.extendDomainLocusHomeomorph (c.obj i)).symm_apply_apply x)

@[simp] theorem extendCoverFamily_extendCoverFamilyInverse (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (d.extendFiniteCover c).size,
      C(((d.extendFiniteCover c).obj i).locus, Y)) :
    d.extendCoverFamily c (d.extendCoverFamilyInverse c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i) ((d.extendDomainLocusHomeomorph (c.obj i)).apply_symm_apply x)

/-- Actual extension gives a constructed equivalence of compatible families. -/
def extendCoverFamilyEquiv (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    CompatibleFamily c Y ≃ CompatibleFamily (d.extendFiniteCover c) Y where
  toFun g := ⟨d.extendCoverFamily c g.val, d.compatible_extendCoverFamily c g.val g.property⟩
  invFun g := ⟨d.extendCoverFamilyInverse c g.val,
    d.compatible_extendCoverFamilyInverse c g.val g.property⟩
  left_inv g := Subtype.ext (d.extendCoverFamilyInverse_extendCoverFamily c g.val)
  right_inv g := Subtype.ext (d.extendCoverFamily_extendCoverFamilyInverse c g.val)

/-- Extension of a global map restricts to extension of its local restrictions. -/
theorem extendCoverFamily_restrict (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (f : C(U.locus, Y)) :
    d.extendCoverFamily c (c.restrict f) =
      (d.extendFiniteCover c).restrict
        (f.comp ((d.extendDomainLocusHomeomorph U).symm :
          C((d.extendDomain U).locus, U.locus))) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg f (d.extendDomainLocusHomeomorph_symm_naturality (c.map i) x).symm

/-- The compatible-family comparison commutes with the concrete gluing equivalences. -/
theorem extendCoverFamilyEquiv_gluingEquiv (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (f : C(U.locus, Y)) :
    d.extendCoverFamilyEquiv c (c.gluingEquiv f) =
      (d.extendFiniteCover c).gluingEquiv
        (f.comp ((d.extendDomainLocusHomeomorph U).symm :
          C((d.extendDomain U).locus, U.locus))) := by
  apply Subtype.ext
  exact d.extendCoverFamily_restrict c f

/-- Gluing after actual extension is gluing before it, composed with the
constructed inverse target locus comparison. -/
theorem glue_extendCoverFamily (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (d.extendFiniteCover c).glue (d.extendCoverFamily c g)
        (d.compatible_extendCoverFamily c g hg) =
      (c.glue g hg).comp ((d.extendDomainLocusHomeomorph U).symm :
        C((d.extendDomain U).locus, U.locus)) := by
  apply ((d.extendFiniteCover c).glue_unique _ _ _ ?_).symm
  intro i
  rw [← d.extendCoverFamily_restrict c (c.glue g hg)]
  change (c.restrict (c.glue g hg) i).comp _ = (g i).comp _
  exact congrArg (fun f : C((c.obj i).locus, Y) =>
    f.comp ((d.extendDomainLocusHomeomorph (c.obj i)).symm :
      C((d.extendDomain (c.obj i)).locus, (c.obj i).locus)))
    (c.restrict_glue g hg i)

/-- Assembly on the retained actual component spectra is unchanged. -/
theorem extendCoverFamily_spectrumFamilyMap (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (d.extendFiniteCover c).spectrumFamilyMap (d.extendCoverFamily c g) =
      c.spectrumFamilyMap g := by
  apply ContinuousMap.ext
  intro x
  apply congrArg (g x.1)
  apply (d.extendDomainLocusHomeomorph (c.obj x.1)).injective
  refine ((d.extendDomainLocusHomeomorph (c.obj x.1)).apply_symm_apply _).trans ?_
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Restriction's inverse comparison lifts the original ambient locus point. -/
theorem restrictDomainLocusHomeomorph_symm_spectrumMap (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) (x : V.locus) :
    d.spectrumMap ((d.restrictDomainLocusHomeomorph V f).symm x) = x :=
  congrArg (fun z : V.locus => (z : BanachSpectrum A))
    ((d.restrictDomainLocusHomeomorph V f).apply_symm_apply x)

/-- Restriction's component comparisons commute with actual target inclusions. -/
theorem restrictFiniteCover_locusMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (i : Fin c.size) (x : ((d.restrictFiniteCover f c).obj i).locus) :
    d.restrictDomainLocusHomeomorph V f
        (((d.restrictFiniteCover f c).map i).locusMap x) =
      (c.map i).locusMap
        (d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f) x) :=
  Subtype.ext rfl

/-- Restrict local continuous maps using the actual forward component comparisons. -/
def restrictCoverFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    ∀ i : Fin (d.restrictFiniteCover f c).size,
      C(((d.restrictFiniteCover f c).obj i).locus, Y) :=
  fun i => (g i).comp (d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f) :
    C((d.restrictDomain (c.obj i) (c.map i ≫ f)).locus, (c.obj i).locus))

/-- The inverse operation uses the inverse actual component comparisons. -/
def restrictCoverFamilyInverse (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin (d.restrictFiniteCover f c).size,
      C(((d.restrictFiniteCover f c).obj i).locus, Y)) :
    ∀ i : Fin c.size, C((c.obj i).locus, Y) :=
  fun i => (g i).comp ((d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f)).symm :
    C((c.obj i).locus, (d.restrictDomain (c.obj i) (c.map i ≫ f)).locus))

theorem compatible_restrictCoverFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (d.restrictFiniteCover f c).Compatible (d.restrictCoverFamily f c g) := by
  intro i j x y h
  exact hg i j _ _ (congrArg d.spectrumMap h)

theorem compatible_restrictCoverFamilyInverse (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin (d.restrictFiniteCover f c).size,
      C(((d.restrictFiniteCover f c).obj i).locus, Y))
    (hg : (d.restrictFiniteCover f c).Compatible g) :
    c.Compatible (d.restrictCoverFamilyInverse f c g) := by
  intro i j x y h
  apply hg i j
  apply d.spectrumMap_injective
  exact (d.restrictDomainLocusHomeomorph_symm_spectrumMap (c.obj i) (c.map i ≫ f) x).trans
    (h.trans
      (d.restrictDomainLocusHomeomorph_symm_spectrumMap (c.obj j) (c.map j ≫ f) y).symm)

@[simp] theorem restrictCoverFamilyInverse_restrictCoverFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.restrictCoverFamilyInverse f c (d.restrictCoverFamily f c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i)
    ((d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f)).apply_symm_apply x)

@[simp] theorem restrictCoverFamily_restrictCoverFamilyInverse (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin (d.restrictFiniteCover f c).size,
      C(((d.restrictFiniteCover f c).obj i).locus, Y)) :
    d.restrictCoverFamily f c (d.restrictCoverFamilyInverse f c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i)
    ((d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f)).symm_apply_apply x)

/-- Actual restriction gives an equivalence of compatible continuous families. -/
def restrictCoverFamilyEquiv (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) :
    CompatibleFamily c Y ≃ CompatibleFamily (d.restrictFiniteCover f c) Y where
  toFun g := ⟨d.restrictCoverFamily f c g.val,
    d.compatible_restrictCoverFamily f c g.val g.property⟩
  invFun g := ⟨d.restrictCoverFamilyInverse f c g.val,
    d.compatible_restrictCoverFamilyInverse f c g.val g.property⟩
  left_inv g := Subtype.ext (d.restrictCoverFamilyInverse_restrictCoverFamily f c g.val)
  right_inv g := Subtype.ext (d.restrictCoverFamily_restrictCoverFamilyInverse f c g.val)

/-- Restriction of global maps agrees with componentwise chart restriction. -/
theorem restrictCoverFamily_restrict (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : C(V.locus, Y)) :
    d.restrictCoverFamily f c (c.restrict g) =
      (d.restrictFiniteCover f c).restrict
        (g.comp (d.restrictDomainLocusHomeomorph V f :
          C((d.restrictDomain V f).locus, V.locus))) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg g (d.restrictFiniteCover_locusMap f c i x).symm

theorem restrictCoverFamilyEquiv_gluingEquiv (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : C(V.locus, Y)) :
    d.restrictCoverFamilyEquiv f c (c.gluingEquiv g) =
      (d.restrictFiniteCover f c).gluingEquiv
        (g.comp (d.restrictDomainLocusHomeomorph V f :
          C((d.restrictDomain V f).locus, V.locus))) := by
  apply Subtype.ext
  exact d.restrictCoverFamily_restrict f c g

/-- Restriction and quotient-topology gluing commute over the actual target comparison. -/
theorem glue_restrictCoverFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    (d.restrictFiniteCover f c).glue (d.restrictCoverFamily f c g)
        (d.compatible_restrictCoverFamily f c g hg) =
      (c.glue g hg).comp (d.restrictDomainLocusHomeomorph V f :
        C((d.restrictDomain V f).locus, V.locus)) := by
  apply ((d.restrictFiniteCover f c).glue_unique _ _ _ ?_).symm
  intro i
  rw [← d.restrictCoverFamily_restrict f c (c.glue g hg)]
  change (c.restrict (c.glue g hg) i).comp _ = (g i).comp _
  exact congrArg (fun h : C((c.obj i).locus, Y) =>
    h.comp (d.restrictDomainLocusHomeomorph (c.obj i) (c.map i ≫ f) :
      C((d.restrictDomain (c.obj i) (c.map i ≫ f)).locus, (c.obj i).locus)))
    (c.restrict_glue g hg i)

/-- Restriction retains assembly on the actual disjoint union of quotient spectra. -/
theorem restrictCoverFamily_spectrumFamilyMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (d.restrictFiniteCover f c).spectrumFamilyMap (d.restrictCoverFamily f c g) =
      c.spectrumFamilyMap g := by
  apply ContinuousMap.ext
  intro x
  exact congrArg (g x.1) (Subtype.ext ((c.map x.1 ≫ f).spectrumMap_over_base x.2))

variable {Z : Type w} [TopologicalSpace Z]

theorem extendCoverFamily_postcomp (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (p : C(Y, Z)) :
    d.extendCoverFamily c (fun i => p.comp (g i)) =
      fun i => p.comp (d.extendCoverFamily c g i) := by
  funext i
  apply ContinuousMap.ext
  intro x
  rfl

theorem restrictCoverFamily_postcomp (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (p : C(Y, Z)) :
    d.restrictCoverFamily f c (fun i => p.comp (g i)) =
      fun i => p.comp (d.restrictCoverFamily f c g i) := by
  funext i
  apply ContinuousMap.ext
  intro x
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
