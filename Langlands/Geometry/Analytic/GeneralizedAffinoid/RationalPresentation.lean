import Langlands.Geometry.Analytic.GeneralizedAffinoid.Adjoin
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Weighted rational and Weierstrass quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- The actual denominator and numerator classes generate the unit ideal. -/
def GeneratesUnitIdeal : Prop :=
  Ideal.span (insert (presentationMap K A g)
    (Set.range fun j => presentationMap K A (f j))) = ⊤

/-- The actual weighted rational equations `g * Y_j - f_j`. -/
def equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K) :=
  Set.range fun j => appendLeft A.polyradius s K g *
    X (A.polyradius.append s) K (Fin.natAdd A.arity j) -
      appendLeft A.polyradius s K (f j)

/-- The closed quotient of the enlarged series algebra by the old ideal and
rational equations. No unit-ideal assumption is needed to form the quotient. -/
def algebra : PresentedAffinoidAlgebra K :=
  Adjoin.algebra K A s (equations K A s g f)

/-- The constructed bounded map from the original quotient. -/
def baseMap : BoundedAlgHom K A (algebra K A s g f) :=
  Adjoin.baseMap K A s (equations K A s g f)

@[simp] theorem baseMap_presentationMap (h : GeneralizedTateAlgebra A.polyradius K) :
    baseMap K A s g f (presentationMap K A h) =
      presentationMap K (algebra K A s g f) (appendLeft A.polyradius s K h) := rfl

theorem norm_baseMap_le (a : A) : ‖baseMap K A s g f a‖ ≤ ‖a‖ :=
  Adjoin.norm_baseMap_le K A s (equations K A s g f) a

theorem baseMap_coordinate (i : Fin A.arity) :
    baseMap K A s g f (coordinate K A i) =
      coordinate K (algebra K A s g f) (Fin.castAdd m i) :=
  Adjoin.baseMap_coordinate K A s (equations K A s g f) i

/-- The new coordinate, satisfying the fraction equation even before imposing
any unit-ideal hypothesis. -/
def fraction (j : Fin m) : algebra K A s g f :=
  Adjoin.newCoordinate K A s (equations K A s g f) j

theorem norm_fraction_le (j : Fin m) : ‖fraction K A s g f j‖ ≤ s j :=
  Adjoin.norm_newCoordinate_le K A s (equations K A s g f) j

theorem fraction_equation (j : Fin m) :
    baseMap K A s g f (presentationMap K A g) * fraction K A s g f j =
      baseMap K A s g f (presentationMap K A (f j)) := by
  have h := Adjoin.presentationMap_equation K A s (equations K A s g f)
    (Set.mem_range_self j)
  change (Ideal.Quotient.mk
    (Ideal.span (Adjoin.relations K A s (equations K A s g f))).closure)
    (appendLeft A.polyradius s K g *
      X (A.polyradius.append s) K (Fin.natAdd A.arity j) -
      appendLeft A.polyradius s K (f j)) = 0 at h
  rw [map_sub, map_mul, sub_eq_zero] at h
  exact h

/-- The expected weighted rational inequalities in the original spectrum. -/
def locus : Set (BanachSpectrum A) :=
  {x | ∀ j, x (presentationMap K A (f j)) ≤ s j * x (presentationMap K A g)}

theorem isClosed_locus : IsClosed (locus K A s g f) := by
  simp only [locus, Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le
    (BanachSpectrum.evaluation (presentationMap K A (f j))).continuous
    (continuous_const.mul (BanachSpectrum.evaluation (presentationMap K A g)).continuous)

theorem isCompact_locus : IsCompact (locus K A s g f) :=
  (isClosed_locus K A s g f).isCompact

/-- The continuous spectrum map of the constructed bounded base map. -/
def spectrumMap : C(BanachSpectrum (algebra K A s g f), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (baseMap K A s g f).toBoundedRingHom

/-- Every quotient point satisfies the indicated weighted rational inequalities. -/
theorem spectrumMap_mem_locus (x : BanachSpectrum (algebra K A s g f)) :
    spectrumMap K A s g f x ∈ locus K A s g f := by
  intro j
  change x (baseMap K A s g f (presentationMap K A (f j))) ≤
    s j * x (baseMap K A s g f (presentationMap K A g))
  rw [← fraction_equation]
  rw [map_mul, mul_comm (s j)]
  exact mul_le_mul_of_nonneg_left
    ((x.le_norm _).trans (norm_fraction_le K A s g f j))
    (apply_nonneg x.toMulRingSeminorm _)

/-- The denominator-one specialization is the weighted Weierstrass presentation. -/
abbrev weierstrassAlgebra : PresentedAffinoidAlgebra K := algebra K A s 1 f

/-- The structural map of the denominator-one presentation. -/
abbrev weierstrassMap : BoundedAlgHom K A (weierstrassAlgebra K A s f) :=
  baseMap K A s 1 f

theorem weierstrass_fraction (j : Fin m) :
    fraction K A s 1 f j = weierstrassMap K A s f (presentationMap K A (f j)) := by
  have h := fraction_equation K A s 1 f j
  simpa only [map_one, one_mul] using h

/-- The Weierstrass inequalities use the same specified positive radii. -/
def weierstrassLocus : Set (BanachSpectrum A) :=
  {x | ∀ j, x (presentationMap K A (f j)) ≤ s j}

theorem locus_one : locus K A s 1 f = weierstrassLocus K A s f := by
  ext x
  simp only [locus, weierstrassLocus, Set.mem_ofPred_eq, map_one, mul_one]

theorem spectrumMap_mem_weierstrassLocus (x : BanachSpectrum (weierstrassAlgebra K A s f)) :
    spectrumMap K A s 1 f x ∈ weierstrassLocus K A s f := by
  rw [← locus_one]
  exact spectrumMap_mem_locus K A s 1 f x

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
