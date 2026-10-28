import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentationTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentationEquivalence
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRadiusRestriction

/-! # Simultaneous coefficient and radius transport of scalar rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {m : ℕ}
  (s t : PositivePolyradius (Fin m)) (hts : ∀ j, t j ≤ s j)
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (g' : GeneralizedTateAlgebra B.polyradius K)
  (f' : Fin m → GeneralizedTateAlgebra B.polyradius K)
  (φ : BoundedAlgHom K A B)
  (hg : φ (presentationMap K A g) = presentationMap K B g')
  (hf : ∀ j, φ (presentationMap K A (f j)) = presentationMap K B (f' j))

/-- Change coefficients by an actual bounded map and shrink the new radii. -/
def presentationRadiusTransport :
    BoundedAlgHom K (algebra K A s g f) (algebra K B t g' f') :=
  (radiusMap K B s t hts g' f').comp (presentationTransport K s g f g' f' φ hg hf)

@[simp] theorem presentationRadiusTransport_baseMap (a : A) :
    presentationRadiusTransport K s t hts g f g' f' φ hg hf (baseMap K A s g f a) =
      baseMap K B t g' f' (φ a) := by
  change radiusMap K B s t hts g' f'
    (presentationTransport K s g f g' f' φ hg hf (baseMap K A s g f a)) = _
  rw [presentationTransport_baseMap, radiusMap_baseMap]

@[simp] theorem presentationRadiusTransport_fraction (j : Fin m) :
    presentationRadiusTransport K s t hts g f g' f' φ hg hf (fraction K A s g f j) =
      fraction K B t g' f' j := by
  change radiusMap K B s t hts g' f'
    (presentationTransport K s g f g' f' φ hg hf (fraction K A s g f j)) = _
  rw [presentationTransport_fraction, radiusMap_fraction]

/-- The two kinds of transport commute as bounded maps of the actual quotients. -/
theorem radiusMap_presentationTransport :
    (radiusMap K B s t hts g' f').comp (presentationTransport K s g f g' f' φ hg hf) =
      (presentationTransport K t g f g' f' φ hg hf).comp (radiusMap K A s t hts g f) := by
  apply hom_ext K A s g f (algebra K B t g' f')
  · intro a
    simp only [BoundedAlgHom.comp_apply,
      presentationTransport_baseMap K s g f g' f' φ hg hf a,
      radiusMap_baseMap K B s t hts g' f' (φ a),
      radiusMap_baseMap K A s t hts g f a,
      presentationTransport_baseMap K t g f g' f' φ hg hf a]
  · intro j
    simp only [BoundedAlgHom.comp_apply,
      presentationTransport_fraction K s g f g' f' φ hg hf j,
      radiusMap_fraction K B s t hts g' f' j,
      radiusMap_fraction K A s t hts g f j,
      presentationTransport_fraction K t g f g' f' φ hg hf j]

theorem presentationRadiusTransport_eq :
    presentationRadiusTransport K s t hts g f g' f' φ hg hf =
      (presentationTransport K t g f g' f' φ hg hf).comp (radiusMap K A s t hts g f) :=
  radiusMap_presentationTransport K s t hts g f g' f' φ hg hf

/-- Coefficient and fraction values characterize the mixed map among all bounded maps. -/
theorem eq_presentationRadiusTransport
    (η : BoundedAlgHom K (algebra K A s g f) (algebra K B t g' f'))
    (hbase : ∀ a, η (baseMap K A s g f a) = baseMap K B t g' f' (φ a))
    (hfrac : ∀ j, η (fraction K A s g f j) = fraction K B t g' f' j) :
    η = presentationRadiusTransport K s t hts g f g' f' φ hg hf := by
  apply hom_ext K A s g f (algebra K B t g' f')
  · intro a
    rw [presentationRadiusTransport_baseMap, hbase]
  · intro j
    rw [presentationRadiusTransport_fraction, hfrac]

/-- Shrinking the radii introduces no loss in any nonnegative coefficient bound. -/
theorem norm_presentationRadiusTransport_le {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (a : algebra K A s g f) :
    ‖presentationRadiusTransport K s t hts g f g' f' φ hg hf a‖ ≤ c * ‖a‖ :=
  (norm_radiusMap_le K B s t hts g' f' _).trans
    (norm_presentationTransport_le K s g f g' f' φ hg hf hc hφ a)

theorem norm_presentationRadiusTransport_le_of_contractive
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (a : algebra K A s g f) :
    ‖presentationRadiusTransport K s t hts g f g' f' φ hg hf a‖ ≤ ‖a‖ :=
  (norm_radiusMap_le K B s t hts g' f' _).trans
    (norm_presentationTransport_le_of_contractive K s g f g' f' φ hg hf hφ a)

@[simp] theorem presentationRadiusTransport_self :
    presentationRadiusTransport K s s (fun _ => le_rfl) g f g' f' φ hg hf =
      presentationTransport K s g f g' f' φ hg hf := by
  apply BoundedAlgHom.ext
  intro a
  change radiusMap K B s s (fun _ => le_rfl) g' f'
    (presentationTransport K s g f g' f' φ hg hf a) = _
  rw [radiusMap_self]
  rfl

@[simp] theorem presentationRadiusTransport_id :
    presentationRadiusTransport K s t hts g f g f
        (BoundedAlgHom.id K A) rfl (fun _ => rfl) =
      radiusMap K A s t hts g f := by
  apply BoundedAlgHom.ext
  intro a
  change radiusMap K A s t hts g f
    (presentationTransport K s g f g f (BoundedAlgHom.id K A) rfl (fun _ => rfl) a) = _
  rw [presentationTransport_id]
  rfl

/-- Successive coefficient changes and successive radius restrictions compose directly. -/
theorem presentationRadiusTransport_comp {C : PresentedAffinoidAlgebra K}
    (v : PositivePolyradius (Fin m)) (hvt : ∀ j, v j ≤ t j)
    (g'' : GeneralizedTateAlgebra C.polyradius K)
    (f'' : Fin m → GeneralizedTateAlgebra C.polyradius K)
    (ψ : BoundedAlgHom K B C)
    (hg' : ψ (presentationMap K B g') = presentationMap K C g'')
    (hf' : ∀ j, ψ (presentationMap K B (f' j)) = presentationMap K C (f'' j)) :
    presentationRadiusTransport K s v (fun j => (hvt j).trans (hts j))
        g f g'' f'' (ψ.comp φ)
        ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) =
      (presentationRadiusTransport K t v hvt g' f' g'' f'' ψ hg' hf').comp
        (presentationRadiusTransport K s t hts g f g' f' φ hg hf) := by
  apply hom_ext K A s g f (algebra K C v g'' f'')
  · intro a
    rw [BoundedAlgHom.comp_apply,
      presentationRadiusTransport_baseMap K s t hts g f g' f' φ hg hf a,
      presentationRadiusTransport_baseMap K t v hvt g' f' g'' f'' ψ hg' hf' (φ a)]
    exact presentationRadiusTransport_baseMap K s v (fun j => (hvt j).trans (hts j))
      g f g'' f'' (ψ.comp φ) ((congrArg ψ hg).trans hg')
      (fun j => (congrArg ψ (hf j)).trans (hf' j)) a
  · intro j
    rw [BoundedAlgHom.comp_apply,
      presentationRadiusTransport_fraction K s t hts g f g' f' φ hg hf j,
      presentationRadiusTransport_fraction K t v hvt g' f' g'' f'' ψ hg' hf' j]
    exact presentationRadiusTransport_fraction K s v (fun j => (hvt j).trans (hts j))
      g f g'' f'' (ψ.comp φ) ((congrArg ψ hg).trans hg')
      (fun j => (congrArg ψ (hf j)).trans (hf' j)) j

/-- The general bounded-map construction recovers the forward coefficient equivalence. -/
theorem presentationTransport_eq_presentationEquiv
    (e : BoundedAlgEquiv K A B)
    (hge : e (presentationMap K A g) = presentationMap K B g')
    (hfe : ∀ j, e (presentationMap K A (f j)) = presentationMap K B (f' j)) :
    presentationTransport K s g f g' f' e.toBoundedAlgHom hge hfe =
      (presentationEquiv K s g f g' f' e hge hfe).toBoundedAlgHom :=
  eq_presentationEquiv K s g f g' f' e hge hfe _
    (presentationTransport_baseMap K s g f g' f' e.toBoundedAlgHom hge hfe)
    (presentationTransport_fraction K s g f g' f' e.toBoundedAlgHom hge hfe)

/-- Continuous contravariant pullback along simultaneous coefficient and radius transport. -/
def presentationRadiusSpectrumMap :
    C(BanachSpectrum (algebra K B t g' f'), BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous
    (presentationRadiusTransport K s t hts g f g' f' φ hg hf).toBoundedRingHom

@[simp] theorem presentationRadiusSpectrumMap_apply
    (x : BanachSpectrum (algebra K B t g' f')) (a : algebra K A s g f) :
    presentationRadiusSpectrumMap K s t hts g f g' f' φ hg hf x a =
      x (presentationRadiusTransport K s t hts g f g' f' φ hg hf a) := rfl

theorem presentationRadiusSpectrumMap_naturality :
    (spectrumMap K A s g f).comp
        (presentationRadiusSpectrumMap K s t hts g f g' f' φ hg hf) =
      (BanachSpectrum.comapContinuous φ.toBoundedRingHom).comp (spectrumMap K B t g' f') := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (presentationRadiusTransport_baseMap K s t hts g f g' f' φ hg hf a)

/-- The two orders of continuous spectrum pullback coincide. -/
theorem radiusSpectrumMap_presentationSpectrumMap :
    (presentationSpectrumMap K s g f g' f' φ hg hf).comp
        (radiusSpectrumMap K B s t hts g' f') =
      (radiusSpectrumMap K A s t hts g f).comp
        (presentationSpectrumMap K t g f g' f' φ hg hf) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (congrArg (fun η : BoundedAlgHom K
    (algebra K A s g f) (algebra K B t g' f') => η a)
      (radiusMap_presentationTransport K s t hts g f g' f' φ hg hf))

omit [CompleteSpace K] in
/-- The actual forward scalar structural map, bundled with its proved inequality codomain. -/
def spectrumToLocus (A : PresentedAffinoidAlgebra K)
    (s : PositivePolyradius (Fin m))
    (g : GeneralizedTateAlgebra A.polyradius K)
    (f : Fin m → GeneralizedTateAlgebra A.polyradius K) :
    C(BanachSpectrum (algebra K A s g f), locus K A s g f) where
  toFun x := ⟨spectrumMap K A s g f x, spectrumMap_mem_locus K A s g f x⟩
  continuous_toFun := (spectrumMap K A s g f).continuous.subtype_mk _

omit [CompleteSpace K] in
/-- Coefficient pullback and the smaller-radius inequalities give the mixed locus map. -/
def presentationRadiusLocusMap : C(locus K B t g' f', locus K A s g f) where
  toFun x := ⟨BanachSpectrum.comap φ.toBoundedRingHom x.val, fun j => by
    change x.val (φ (presentationMap K A (f j))) ≤
      s j * x.val (φ (presentationMap K A g))
    rw [hg, hf j]
    exact (x.property j).trans (mul_le_mul_of_nonneg_right (hts j)
      (apply_nonneg x.val.toMulRingSeminorm _))⟩
  continuous_toFun :=
    ((BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous.comp
      continuous_subtype_val).subtype_mk _

omit [CompleteSpace K] in
@[simp] theorem presentationRadiusLocusMap_apply (x : locus K B t g' f') (a : A) :
    (presentationRadiusLocusMap K s t hts g f g' f' φ hg hf x).val a = x.val (φ a) := rfl

omit [CompleteSpace K] in
@[simp] theorem presentationRadiusLocusMap_self :
    presentationRadiusLocusMap K s s (fun _ => le_rfl) g f g' f' φ hg hf =
      presentationLocusMap K s g f g' f' φ hg hf := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

omit [CompleteSpace K] in
theorem presentationRadiusLocusMap_comp {C : PresentedAffinoidAlgebra K}
    (v : PositivePolyradius (Fin m)) (hvt : ∀ j, v j ≤ t j)
    (g'' : GeneralizedTateAlgebra C.polyradius K)
    (f'' : Fin m → GeneralizedTateAlgebra C.polyradius K)
    (ψ : BoundedAlgHom K B C)
    (hg' : ψ (presentationMap K B g') = presentationMap K C g'')
    (hf' : ∀ j, ψ (presentationMap K B (f' j)) = presentationMap K C (f'' j)) :
    presentationRadiusLocusMap K s v (fun j => (hvt j).trans (hts j))
        g f g'' f'' (ψ.comp φ)
        ((congrArg ψ hg).trans hg') (fun j => (congrArg ψ (hf j)).trans (hf' j)) =
      (presentationRadiusLocusMap K s t hts g f g' f' φ hg hf).comp
        (presentationRadiusLocusMap K t v hvt g' f' g'' f'' ψ hg' hf') := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Naturality holds in the actual inequality subspaces as well as the coefficient spectra. -/
theorem spectrumToLocus_presentationRadiusTransport :
    (spectrumToLocus K A s g f).comp
        (presentationRadiusSpectrumMap K s t hts g f g' f' φ hg hf) =
      (presentationRadiusLocusMap K s t hts g f g' f' φ hg hf).comp
        (spectrumToLocus K B t g' f') := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (presentationRadiusTransport_baseMap K s t hts g f g' f' φ hg hf a)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
