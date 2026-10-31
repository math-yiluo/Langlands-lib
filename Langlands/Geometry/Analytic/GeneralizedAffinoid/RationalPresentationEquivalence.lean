import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalEquivalence
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentatives

/-! # Weighted rational quotients under coefficient presentation equivalences -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

section DataEquality

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g g' : A) (f f' : Fin m → A) (hg : g = g') (hf : f = f')

/-- Equality of actual rational data identifies the two intrinsic quotients. -/
def dataEquiv :
    BoundedAlgEquiv K (RelativeRationalPresentation.Algebra K A s g f)
      (RelativeRationalPresentation.Algebra K A s g' f') := by
  cases hg
  cases hf
  exact BoundedAlgEquiv.refl K _

theorem dataEquiv_baseMap (a : A) :
    dataEquiv K A s g g' f f' hg hf
      (RelativeRationalPresentation.baseMap K A s g f a) =
        RelativeRationalPresentation.baseMap K A s g' f' a := by
  cases hg
  cases hf
  rfl

theorem dataEquiv_fraction (j : Fin m) :
    dataEquiv K A s g g' f f' hg hf
      (RelativeRationalPresentation.fraction K A s g f j) =
        RelativeRationalPresentation.fraction K A s g' f' j := by
  cases hg
  cases hf
  rfl

private theorem dataEquiv_quotientMap (h : GeneralizedTateAlgebra s A) :
    dataEquiv K A s g g' f f' hg hf
      (RelativeRationalPresentation.quotientMap K A s g f h) =
        RelativeRationalPresentation.quotientMap K A s g' f' h := by
  cases hg
  cases hf
  rfl

private theorem norm_dataEquiv (a : RelativeRationalPresentation.Algebra K A s g f) :
    ‖dataEquiv K A s g g' f f' hg hf a‖ = ‖a‖ := by
  cases hg
  cases hf
  rfl

private theorem norm_dataEquiv_symm
    (a : RelativeRationalPresentation.Algebra K A s g' f') :
    ‖(dataEquiv K A s g g' f f' hg hf).symm a‖ = ‖a‖ := by
  cases hg
  cases hf
  rfl

end DataEquality

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {m : ℕ}
  (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (g' : GeneralizedTateAlgebra B.polyradius K)
  (f' : Fin m → GeneralizedTateAlgebra B.polyradius K)
  (e : BoundedAlgEquiv K A B)
  (hg : e (presentationMap K A g) = presentationMap K B g')
  (hf : ∀ j, e (presentationMap K A (f j)) = presentationMap K B (f' j))

/-- Compare the actual scalar rational quotients across a supplied bounded
coefficient equivalence and matching classes of the supplied representatives. -/
def presentationEquiv :
    BoundedAlgEquiv K (algebra K A s g f) (algebra K B s g' f') :=
  (((relativeEquiv K A s g f).trans
    (RelativeRationalPresentation.coefficientEquiv K s (presentationMap K A g)
      (fun j => presentationMap K A (f j)) e)).trans
    (dataEquiv K B s (e (presentationMap K A g)) (presentationMap K B g')
      (fun j => e (presentationMap K A (f j)))
      (fun j => presentationMap K B (f' j)) hg (funext hf))).trans
    (relativeEquiv K B s g' f').symm

/-- The comparison is precisely intrinsic coefficient transport between the two
scalar-to-relative identifications, with the supplied data equalities. -/
theorem relativeEquiv_presentationEquiv (a : algebra K A s g f) :
    relativeEquiv K B s g' f' (presentationEquiv K s g f g' f' e hg hf a) =
      dataEquiv K B s (e (presentationMap K A g)) (presentationMap K B g')
        (fun j => e (presentationMap K A (f j)))
        (fun j => presentationMap K B (f' j)) hg (funext hf)
        (RelativeRationalPresentation.coefficientEquiv K s (presentationMap K A g)
          (fun j => presentationMap K A (f j)) e (relativeEquiv K A s g f a)) := by
  change relativeEquiv K B s g' f' ((relativeEquiv K B s g' f').symm _) = _
  exact BoundedAlgEquiv.apply_symm_apply _ _

@[simp] theorem presentationEquiv_baseMap (a : A) :
    presentationEquiv K s g f g' f' e hg hf (baseMap K A s g f a) =
      baseMap K B s g' f' (e a) := by
  apply (relativeEquiv K B s g' f').toAlgEquiv.injective
  rw [relativeEquiv_presentationEquiv, relativeEquiv_baseMap,
    RelativeRationalPresentation.coefficientEquiv_baseMap, dataEquiv_baseMap,
    relativeEquiv_baseMap]

@[simp] theorem presentationEquiv_fraction (j : Fin m) :
    presentationEquiv K s g f g' f' e hg hf (fraction K A s g f j) =
      fraction K B s g' f' j := by
  apply (relativeEquiv K B s g' f').toAlgEquiv.injective
  rw [relativeEquiv_presentationEquiv, relativeEquiv_fraction,
    RelativeRationalPresentation.coefficientEquiv_fraction, dataEquiv_fraction,
    relativeEquiv_fraction]

@[simp] theorem presentationEquiv_symm_baseMap (b : B) :
    (presentationEquiv K s g f g' f' e hg hf).symm (baseMap K B s g' f' b) =
      baseMap K A s g f (e.symm b) := by
  apply (presentationEquiv K s g f g' f' e hg hf).toAlgEquiv.injective
  rw [BoundedAlgEquiv.apply_symm_apply, presentationEquiv_baseMap,
    BoundedAlgEquiv.apply_symm_apply]

@[simp] theorem presentationEquiv_symm_fraction (j : Fin m) :
    (presentationEquiv K s g f g' f' e hg hf).symm (fraction K B s g' f' j) =
      fraction K A s g f j := by
  rw [← presentationEquiv_fraction K s g f g' f' e hg hf,
    BoundedAlgEquiv.symm_apply_apply]

/-- On every scalar representative, the intrinsic target representative is the
coefficientwise image of its relative evaluation over the source. -/
theorem relativeEquiv_presentationEquiv_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquiv K B s g' f'
      (presentationEquiv K s g f g' f' e hg hf
        (presentationMap K (algebra K A s g f) h)) =
      RelativeRationalPresentation.quotientMap K B s (presentationMap K B g')
        (fun j => presentationMap K B (f' j))
        (mapCoefficientsAlgHom s e.toBoundedAlgHom
          (Adjoin.relativeSeriesEvaluation K A s h)) := by
  rw [relativeEquiv_presentationEquiv, relativeEquiv_presentationMap,
    RelativeRationalPresentation.coefficientEquiv_quotientMap, dataEquiv_quotientMap]

/-- The coefficient and fraction formulas characterize the constructed map. -/
theorem eq_presentationEquiv
    (ψ : BoundedAlgHom K (algebra K A s g f) (algebra K B s g' f'))
    (hbase : ∀ a, ψ (baseMap K A s g f a) = baseMap K B s g' f' (e a))
    (hfrac : ∀ j, ψ (fraction K A s g f j) = fraction K B s g' f' j) :
    ψ = (presentationEquiv K s g f g' f' e hg hf).toBoundedAlgHom := by
  apply hom_ext K A s g f (algebra K B s g' f')
  · intro a
    simpa only [BoundedAlgEquiv.toBoundedAlgHom_apply, presentationEquiv_baseMap]
      using hbase a
  · intro j
    simpa only [BoundedAlgEquiv.toBoundedAlgHom_apply, presentationEquiv_fraction]
      using hfrac j

/-- The supplied forward coefficient bound passes unchanged to scalar quotients. -/
theorem norm_presentationEquiv_le {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ a, ‖e a‖ ≤ c * ‖a‖) (a : algebra K A s g f) :
    ‖presentationEquiv K s g f g' f' e hg hf a‖ ≤ c * ‖a‖ := by
  calc
    ‖presentationEquiv K s g f g' f' e hg hf a‖ =
        ‖RelativeRationalPresentation.coefficientEquiv K s (presentationMap K A g)
          (fun j => presentationMap K A (f j)) e (relativeEquiv K A s g f a)‖ := by
      rw [← norm_relativeEquiv K B s g' f'
        (presentationEquiv K s g f g' f' e hg hf a),
        relativeEquiv_presentationEquiv, norm_dataEquiv]
    _ ≤ c * ‖relativeEquiv K A s g f a‖ :=
      RelativeRationalPresentation.norm_coefficientEquiv_le K s _ _ e hc he _
    _ = c * ‖a‖ := by rw [norm_relativeEquiv]

/-- The inverse bound is independent of the forward bound, including c = 0. -/
theorem norm_presentationEquiv_symm_le {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ b, ‖e.symm b‖ ≤ c * ‖b‖) (b : algebra K B s g' f') :
    ‖(presentationEquiv K s g f g' f' e hg hf).symm b‖ ≤ c * ‖b‖ := by
  change ‖(relativeEquiv K A s g f).symm
    ((RelativeRationalPresentation.coefficientEquiv K s (presentationMap K A g)
      (fun j => presentationMap K A (f j)) e).symm
      ((dataEquiv K B s (e (presentationMap K A g)) (presentationMap K B g')
        (fun j => e (presentationMap K A (f j)))
        (fun j => presentationMap K B (f' j)) hg (funext hf)).symm
        (relativeEquiv K B s g' f' b)))‖ ≤ c * ‖b‖
  rw [norm_relativeEquiv_symm]
  calc
    _ ≤ c * ‖(dataEquiv K B s (e (presentationMap K A g)) (presentationMap K B g')
        (fun j => e (presentationMap K A (f j)))
        (fun j => presentationMap K B (f' j)) hg (funext hf)).symm
        (relativeEquiv K B s g' f' b)‖ :=
      RelativeRationalPresentation.norm_coefficientEquiv_symm_le K s _ _ e hc he _
    _ = c * ‖b‖ := by rw [norm_dataEquiv_symm, norm_relativeEquiv]

/-- Norm-preserving coefficient equivalences preserve the actual quotient norms. -/
theorem norm_presentationEquiv (he : ∀ a, ‖e a‖ = ‖a‖) (a : algebra K A s g f) :
    ‖presentationEquiv K s g f g' f' e hg hf a‖ = ‖a‖ := by
  rw [← norm_relativeEquiv K B s g' f'
    (presentationEquiv K s g f g' f' e hg hf a),
    relativeEquiv_presentationEquiv, norm_dataEquiv,
    RelativeRationalPresentation.norm_coefficientEquiv K s _ _ e he,
    norm_relativeEquiv]

theorem norm_presentationEquiv_symm (he : ∀ a, ‖e a‖ = ‖a‖)
    (b : algebra K B s g' f') :
    ‖(presentationEquiv K s g f g' f' e hg hf).symm b‖ = ‖b‖ := by
  have h := norm_presentationEquiv K s g f g' f' e hg hf he
    ((presentationEquiv K s g f g' f' e hg hf).symm b)
  rw [BoundedAlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem isometry_presentationEquiv (he : ∀ a, ‖e a‖ = ‖a‖) :
    Isometry (presentationEquiv K s g f g' f' e hg hf) :=
  AddMonoidHomClass.isometry_of_norm
    (presentationEquiv K s g f g' f' e hg hf).toAlgEquiv
    (norm_presentationEquiv K s g f g' f' e hg hf he)

/-- For a fixed coefficient presentation and the identity equivalence this is
the already published representative-change map. -/
theorem presentationEquiv_eq_representativeEquiv
    (h : GeneralizedTateAlgebra A.polyradius K)
    (k : Fin m → GeneralizedTateAlgebra A.polyradius K)
    (hden : presentationMap K A g = presentationMap K A h)
    (hnum : ∀ j, presentationMap K A (f j) = presentationMap K A (k j)) :
    (presentationEquiv K s g f h k (BoundedAlgEquiv.refl K A) hden hnum).toBoundedAlgHom =
      (representativeEquiv K A s g h f k hden hnum).toBoundedAlgHom := by
  apply hom_ext K A s g f (algebra K A s h k)
  · intro a
    exact (presentationEquiv_baseMap K s g f h k
      (BoundedAlgEquiv.refl K A) hden hnum a).trans
        (representativeEquiv_baseMap K A s g h f k hden hnum a).symm
  · intro j
    exact (presentationEquiv_fraction K s g f h k
      (BoundedAlgEquiv.refl K A) hden hnum j).trans
        (representativeEquiv_fraction K A s g h f k hden hnum j).symm

/-- The genuine contravariant homeomorphism of the two scalar quotient spectra. -/
def presentationSpectrumHomeomorph :
    BanachSpectrum (algebra K B s g' f') ≃ₜ BanachSpectrum (algebra K A s g f) :=
  (presentationEquiv K s g f g' f' e hg hf).spectrumHomeomorph

@[simp] theorem presentationSpectrumHomeomorph_apply
    (x : BanachSpectrum (algebra K B s g' f')) (a : algebra K A s g f) :
    presentationSpectrumHomeomorph K s g f g' f' e hg hf x a =
      x (presentationEquiv K s g f g' f' e hg hf a) := rfl

@[simp] theorem presentationSpectrumHomeomorph_symm_apply
    (x : BanachSpectrum (algebra K A s g f)) (b : algebra K B s g' f') :
    (presentationSpectrumHomeomorph K s g f g' f' e hg hf).symm x b =
      x ((presentationEquiv K s g f g' f' e hg hf).symm b) := rfl

/-- Equality of the two continuous structural paths into the original spectrum. -/
theorem presentationSpectrumHomeomorph_naturality :
    (spectrumMap K A s g f).comp
        ⟨presentationSpectrumHomeomorph K s g f g' f' e hg hf,
          (presentationSpectrumHomeomorph K s g f g' f' e hg hf).continuous⟩ =
      (⟨e.spectrumHomeomorph, e.spectrumHomeomorph.continuous⟩ :
        C(BanachSpectrum B, BanachSpectrum A)).comp (spectrumMap K B s g' f') := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (presentationEquiv_baseMap K s g f g' f' e hg hf a)

omit [CompleteSpace K] in
/-- The coefficient spectrum homeomorphism restricts to the two scalar loci. -/
def presentationLocusHomeomorph :
    locus K B s g' f' ≃ₜ locus K A s g f :=
  e.spectrumHomeomorph.subtype (fun x => by
    change (∀ j, x (presentationMap K B (f' j)) ≤ s j * x (presentationMap K B g')) ↔
      (∀ j, x (e (presentationMap K A (f j))) ≤ s j * x (e (presentationMap K A g)))
    simp only [hg, hf])

omit [CompleteSpace K] in
@[simp] theorem presentationLocusHomeomorph_apply (x : locus K B s g' f') (a : A) :
    (presentationLocusHomeomorph K s g f g' f' e hg hf x).val a = x.val (e a) := rfl

omit [CompleteSpace K] in
@[simp] theorem presentationLocusHomeomorph_symm_apply (x : locus K A s g f) (b : B) :
    ((presentationLocusHomeomorph K s g f g' f' e hg hf).symm x).val b =
      x.val (e.symm b) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
