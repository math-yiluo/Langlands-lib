import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Mathlib.Topology.ContinuousMap.Basic

/-! # Gluing continuous maps along actual finite full-domain covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K} {V : Domain K A}
variable (c : FiniteCover V)
variable {Y : Type v} [TopologicalSpace Y]

/-- Agreement at equal underlying base-spectrum points, including all overlaps. -/
def Compatible (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) : Prop :=
  ∀ (i j : Fin c.size) (x : (c.obj i).locus) (y : (c.obj j).locus),
    (x : BanachSpectrum A) = (y : BanachSpectrum A) → g i x = g j y

/-- Restriction of a continuous map along the actual domain locus inclusions. -/
def restrict (f : C(V.locus, Y)) (i : Fin c.size) : C((c.obj i).locus, Y) :=
  f.comp (c.map i).locusMap

theorem compatible_restrict (f : C(V.locus, Y)) : c.Compatible (c.restrict f) := by
  intro i j x y h
  exact congrArg f (Subtype.ext h)

/-- Maps from the target are determined by their restrictions to the cover. -/
theorem ext_of_restrict_eq {f h : C(V.locus, Y)}
    (heq : ∀ i, c.restrict f i = c.restrict h i) : f = h := by
  ext x
  obtain ⟨⟨i, z⟩, rfl⟩ := c.totalMap_surjective x
  exact DFunLike.congr_fun (heq i) ((c.obj i).spectrumToLocus z)

/-- Assemble the given locus maps on the disjoint union of actual spectra. -/
def spectrumFamilyMap (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    C((Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra), Y) where
  toFun x := g x.1 ((c.obj x.1).spectrumToLocus x.2)
  continuous_toFun := continuous_sigma fun i =>
    (g i).continuous.comp (c.obj i).spectrumToLocus.continuous

/-- Overlap agreement makes the assembled map constant on the quotient fibers. -/
theorem spectrumFamilyMap_factorsThrough
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    Function.FactorsThrough (c.spectrumFamilyMap g) c.totalMap := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  exact hg i j _ _ (congrArg (fun z : V.locus => (z : BanachSpectrum A)) h)

/-- Descend compatible continuous maps through the actual spectrum-cover quotient. -/
def glue (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g) :
    C(V.locus, Y) :=
  c.totalMap_isQuotientMap.lift (c.spectrumFamilyMap g)
    (c.spectrumFamilyMap_factorsThrough g hg)

theorem glue_apply_spectrum
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    c.glue g hg (c.componentMap i x) = g i ((c.obj i).spectrumToLocus x) :=
  DFunLike.congr_fun
    (c.totalMap_isQuotientMap.lift_comp (c.spectrumFamilyMap g)
      (c.spectrumFamilyMap_factorsThrough g hg)) ⟨i, x⟩

@[simp] theorem restrict_glue
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g)
    (i : Fin c.size) : c.restrict (c.glue g hg) i = g i := by
  ext x
  obtain ⟨y, rfl⟩ := (c.obj i).spectrumToLocus_surjective x
  exact c.glue_apply_spectrum g hg i y

@[simp] theorem glue_restrict (f : C(V.locus, Y)) :
    c.glue (c.restrict f) (c.compatible_restrict f) = f := by
  apply c.ext_of_restrict_eq
  intro i
  exact c.restrict_glue _ _ i

/-- The glued continuous map is the unique one with the given restrictions. -/
theorem glue_unique
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g)
    (f : C(V.locus, Y)) (hf : ∀ i, c.restrict f i = g i) :
    f = c.glue g hg := by
  apply c.ext_of_restrict_eq
  intro i
  rw [hf i, c.restrict_glue g hg i]

/-- Continuous maps on the target are exactly compatible continuous locus maps. -/
def gluingEquiv :
    C(V.locus, Y) ≃
      {g : ∀ i : Fin c.size, C((c.obj i).locus, Y) // c.Compatible g} where
  toFun f := ⟨c.restrict f, c.compatible_restrict f⟩
  invFun g := c.glue g.val g.property
  left_inv f := c.glue_restrict f
  right_inv g := by
    apply Subtype.ext
    funext i
    exact c.restrict_glue g.val g.property i

variable {Z : Type w} [TopologicalSpace Z]

theorem compatible_postcomp
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g)
    (p : C(Y, Z)) : c.Compatible (fun i => p.comp (g i)) := by
  intro i j x y h
  exact congrArg p (hg i j x y h)

/-- Gluing commutes with every continuous map of target spaces. -/
theorem glue_postcomp
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) (hg : c.Compatible g)
    (p : C(Y, Z)) :
    p.comp (c.glue g hg) =
      c.glue (fun i => p.comp (g i)) (c.compatible_postcomp g hg p) := by
  apply c.glue_unique
  intro i
  change p.comp (c.restrict (c.glue g hg) i) = p.comp (g i)
  rw [c.restrict_glue]

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
