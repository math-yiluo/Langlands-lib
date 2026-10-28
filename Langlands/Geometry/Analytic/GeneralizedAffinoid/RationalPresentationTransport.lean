import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentatives

/-! # Bounded maps between scalar weighted rational presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

section IntrinsicData

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : A) (g' : B) (f : Fin m → A) (f' : Fin m → B)
  (φ : BoundedAlgHom K A B) (hg : φ g = g')
  (hf : (fun j => φ (f j)) = f')

/-- Relabel the target of actual intrinsic coefficient transport by data equality. -/
private def matchedTransport :
    BoundedAlgHom K (RelativeRationalPresentation.Algebra K A s g f)
      (RelativeRationalPresentation.Algebra K B s g' f') := by
  cases hg
  cases hf
  exact RelativeRationalPresentation.transport K s g f φ

private theorem matchedTransport_baseMap (a : A) :
    matchedTransport K s g g' f f' φ hg hf
      (RelativeRationalPresentation.baseMap K A s g f a) =
        RelativeRationalPresentation.baseMap K B s g' f' (φ a) := by
  cases hg
  cases hf
  exact RelativeRationalPresentation.transport_baseMap K s g f φ a

private theorem matchedTransport_fraction (j : Fin m) :
    matchedTransport K s g g' f f' φ hg hf
      (RelativeRationalPresentation.fraction K A s g f j) =
        RelativeRationalPresentation.fraction K B s g' f' j := by
  cases hg
  cases hf
  exact RelativeRationalPresentation.transport_fraction K s g f φ j

private theorem matchedTransport_quotientMap (h : GeneralizedTateAlgebra s A) :
    matchedTransport K s g g' f f' φ hg hf
      (RelativeRationalPresentation.quotientMap K A s g f h) =
        RelativeRationalPresentation.quotientMap K B s g' f'
          (mapCoefficientsAlgHom s φ h) := by
  cases hg
  cases hf
  exact RelativeRationalPresentation.transport_quotientMap K s g f φ h

private theorem norm_matchedTransport_le {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖)
    (a : RelativeRationalPresentation.Algebra K A s g f) :
    ‖matchedTransport K s g g' f f' φ hg hf a‖ ≤ c * ‖a‖ := by
  cases hg
  cases hf
  exact RelativeRationalPresentation.norm_transport_le K s g f φ hc hφ a

end IntrinsicData

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {m : ℕ}
  (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (g' : GeneralizedTateAlgebra B.polyradius K)
  (f' : Fin m → GeneralizedTateAlgebra B.polyradius K)
  (φ : BoundedAlgHom K A B)
  (hg : φ (presentationMap K A g) = presentationMap K B g')
  (hf : ∀ j, φ (presentationMap K A (f j)) = presentationMap K B (f' j))

/-- The actual scalar quotient map induced by a bounded coefficient map and
matching classes of denominator and numerator representatives. -/
def presentationTransport :
    BoundedAlgHom K (algebra K A s g f) (algebra K B s g' f') :=
  (relativeEquiv K B s g' f').symm.toBoundedAlgHom.comp
    ((matchedTransport K s (presentationMap K A g) (presentationMap K B g')
      (fun j => presentationMap K A (f j)) (fun j => presentationMap K B (f' j))
      φ hg (funext hf)).comp (relativeEquiv K A s g f).toBoundedAlgHom)

private theorem relativeEquiv_presentationTransport (a : algebra K A s g f) :
    relativeEquiv K B s g' f' (presentationTransport K s g f g' f' φ hg hf a) =
      matchedTransport K s (presentationMap K A g) (presentationMap K B g')
        (fun j => presentationMap K A (f j)) (fun j => presentationMap K B (f' j))
        φ hg (funext hf) (relativeEquiv K A s g f a) := by
  change relativeEquiv K B s g' f' ((relativeEquiv K B s g' f').symm _) = _
  exact BoundedAlgEquiv.apply_symm_apply _ _

@[simp] theorem presentationTransport_baseMap (a : A) :
    presentationTransport K s g f g' f' φ hg hf (baseMap K A s g f a) =
      baseMap K B s g' f' (φ a) := by
  apply (relativeEquiv K B s g' f').toAlgEquiv.injective
  rw [relativeEquiv_presentationTransport, relativeEquiv_baseMap,
    matchedTransport_baseMap, relativeEquiv_baseMap]

@[simp] theorem presentationTransport_fraction (j : Fin m) :
    presentationTransport K s g f g' f' φ hg hf (fraction K A s g f j) =
      fraction K B s g' f' j := by
  apply (relativeEquiv K B s g' f').toAlgEquiv.injective
  rw [relativeEquiv_presentationTransport, relativeEquiv_fraction,
    matchedTransport_fraction, relativeEquiv_fraction]

/-- On every source scalar representative, compute its image in the intrinsic target. -/
theorem relativeEquiv_presentationTransport_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    relativeEquiv K B s g' f'
      (presentationTransport K s g f g' f' φ hg hf
        (presentationMap K (algebra K A s g f) h)) =
      RelativeRationalPresentation.quotientMap K B s (presentationMap K B g')
        (fun j => presentationMap K B (f' j))
        (mapCoefficientsAlgHom s φ (Adjoin.relativeSeriesEvaluation K A s h)) := by
  rw [relativeEquiv_presentationTransport, relativeEquiv_presentationMap,
    matchedTransport_quotientMap]

/-- The coefficient and fraction values determine the bounded scalar map uniquely. -/
theorem eq_presentationTransport
    (η : BoundedAlgHom K (algebra K A s g f) (algebra K B s g' f'))
    (hbase : ∀ a, η (baseMap K A s g f a) = baseMap K B s g' f' (φ a))
    (hfrac : ∀ j, η (fraction K A s g f j) = fraction K B s g' f' j) :
    η = presentationTransport K s g f g' f' φ hg hf := by
  apply hom_ext K A s g f (algebra K B s g' f')
  · intro a
    rw [presentationTransport_baseMap, hbase]
  · intro j
    rw [presentationTransport_fraction, hfrac]

/-- Any supplied nonnegative coefficient bound passes to the quotient unchanged. -/
theorem norm_presentationTransport_le {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (a : algebra K A s g f) :
    ‖presentationTransport K s g f g' f' φ hg hf a‖ ≤ c * ‖a‖ := by
  rw [← norm_relativeEquiv K B s g' f'
    (presentationTransport K s g f g' f' φ hg hf a),
    relativeEquiv_presentationTransport]
  exact (norm_matchedTransport_le K s _ _ _ _ φ hg (funext hf) hc hφ _).trans_eq
    (congrArg (fun r : ℝ => c * r) (norm_relativeEquiv K A s g f a))

theorem norm_presentationTransport_le_of_contractive
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (a : algebra K A s g f) :
    ‖presentationTransport K s g f g' f' φ hg hf a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using norm_presentationTransport_le K s g f g' f' φ hg hf
    zero_le_one (fun a => (hφ a).trans_eq (one_mul _).symm) a

@[simp] theorem presentationTransport_id :
    presentationTransport K s g f g f (BoundedAlgHom.id K A) rfl (fun _ => rfl) =
      BoundedAlgHom.id K (algebra K A s g f) := by
  apply hom_ext K A s g f (algebra K A s g f)
  · intro a
    exact presentationTransport_baseMap K s g f g f
      (BoundedAlgHom.id K A) rfl (fun _ => rfl) a
  · intro j
    exact presentationTransport_fraction K s g f g f
      (BoundedAlgHom.id K A) rfl (fun _ => rfl) j

theorem presentationTransport_comp {C : PresentedAffinoidAlgebra K}
    (g'' : GeneralizedTateAlgebra C.polyradius K)
    (f'' : Fin m → GeneralizedTateAlgebra C.polyradius K)
    (ψ : BoundedAlgHom K B C)
    (hg' : ψ (presentationMap K B g') = presentationMap K C g'')
    (hf' : ∀ j, ψ (presentationMap K B (f' j)) = presentationMap K C (f'' j)) :
    presentationTransport K s g f g'' f'' (ψ.comp φ)
        ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) =
      (presentationTransport K s g' f' g'' f'' ψ hg' hf').comp
        (presentationTransport K s g f g' f' φ hg hf) := by
  apply hom_ext K A s g f (algebra K C s g'' f'')
  · intro a
    rw [BoundedAlgHom.comp_apply,
      presentationTransport_baseMap K s g f g' f' φ hg hf a,
      presentationTransport_baseMap K s g' f' g'' f'' ψ hg' hf' (φ a)]
    exact presentationTransport_baseMap K s g f g'' f'' (ψ.comp φ)
      ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) a
  · intro j
    rw [BoundedAlgHom.comp_apply,
      presentationTransport_fraction K s g f g' f' φ hg hf j,
      presentationTransport_fraction K s g' f' g'' f'' ψ hg' hf' j]
    exact presentationTransport_fraction K s g f g'' f'' (ψ.comp φ)
      ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) j

/-- The identity coefficient map recovers the previously constructed representative map. -/
theorem presentationTransport_eq_representativeMap
    (h : GeneralizedTateAlgebra A.polyradius K)
    (k : Fin m → GeneralizedTateAlgebra A.polyradius K)
    (hden : presentationMap K A g = presentationMap K A h)
    (hnum : ∀ j, presentationMap K A (f j) = presentationMap K A (k j)) :
    presentationTransport K s g f h k (BoundedAlgHom.id K A) hden hnum =
      representativeMap K A s g h f k hden hnum := by
  apply hom_ext K A s g f (algebra K A s h k)
  · intro a
    exact (presentationTransport_baseMap K s g f h k
      (BoundedAlgHom.id K A) hden hnum a).trans
        (representativeMap_baseMap K A s g h f k hden hnum a).symm
  · intro j
    exact (presentationTransport_fraction K s g f h k
      (BoundedAlgHom.id K A) hden hnum j).trans
        (representativeMap_fraction K A s g h f k hden hnum j).symm

/-- Actual continuous contravariant pullback on the two scalar quotient spectra. -/
def presentationSpectrumMap :
    C(BanachSpectrum (algebra K B s g' f'), BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (presentationTransport K s g f g' f' φ hg hf).toBoundedRingHom

@[simp] theorem presentationSpectrumMap_apply
    (x : BanachSpectrum (algebra K B s g' f')) (a : algebra K A s g f) :
    presentationSpectrumMap K s g f g' f' φ hg hf x a =
      x (presentationTransport K s g f g' f' φ hg hf a) := rfl

/-- The two continuous structural paths to the source coefficient spectrum agree. -/
theorem presentationSpectrumMap_naturality :
    (spectrumMap K A s g f).comp (presentationSpectrumMap K s g f g' f' φ hg hf) =
      (BanachSpectrum.comapContinuous φ.toBoundedRingHom).comp (spectrumMap K B s g' f') := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (presentationTransport_baseMap K s g f g' f' φ hg hf a)

omit [CompleteSpace K] in
/-- Coefficient pullback continuously preserves the matched scalar rational inequalities. -/
def presentationLocusMap : C(locus K B s g' f', locus K A s g f) where
  toFun x := ⟨BanachSpectrum.comap φ.toBoundedRingHom x.val, fun j => by
    change x.val (φ (presentationMap K A (f j))) ≤
      s j * x.val (φ (presentationMap K A g))
    rw [hg, hf j]
    exact x.property j⟩
  continuous_toFun :=
    ((BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous.comp
      continuous_subtype_val).subtype_mk _

omit [CompleteSpace K] in
@[simp] theorem presentationLocusMap_apply (x : locus K B s g' f') (a : A) :
    (presentationLocusMap K s g f g' f' φ hg hf x).val a = x.val (φ a) := rfl

omit [CompleteSpace K] in
@[simp] theorem presentationLocusMap_id :
    presentationLocusMap K s g f g f (BoundedAlgHom.id K A) rfl (fun _ => rfl) =
      ContinuousMap.id (locus K A s g f) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

omit [CompleteSpace K] in
theorem presentationLocusMap_comp {C : PresentedAffinoidAlgebra K}
    (g'' : GeneralizedTateAlgebra C.polyradius K)
    (f'' : Fin m → GeneralizedTateAlgebra C.polyradius K)
    (ψ : BoundedAlgHom K B C)
    (hg' : ψ (presentationMap K B g') = presentationMap K C g'')
    (hf' : ∀ j, ψ (presentationMap K B (f' j)) = presentationMap K C (f'' j)) :
    presentationLocusMap K s g f g'' f'' (ψ.comp φ)
        ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) =
      (presentationLocusMap K s g f g' f' φ hg hf).comp
        (presentationLocusMap K s g' f' g'' f'' ψ hg' hf') := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
