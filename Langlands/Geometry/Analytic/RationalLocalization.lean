import Langlands.Geometry.Analytic.RationalTransport
import Langlands.Geometry.Analytic.RationalLocalization.Statement
import Langlands.Geometry.Analytic.RationalSpectrum

/-! # Rational quotients of arbitrary presented strict affinoid algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.RationalLocalization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (P : PresentedStrictAffinoidAlgebra K) [CompleteSpace K]
  (m : ℕ) (g : P) (f : Fin m → P)

theorem coordinate_equation (j : Fin m) :
    baseMap K P m g f g * fractionCoordinate K P m g f j =
      baseMap K P m g f (f j) := by
  have h := RationalPresentation.coordinate_equation K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) j
  change RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm g) *
    coordinate K (RationalPresentation.algebra K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j))) (Fin.natAdd P.arity j) =
    RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm (f j))
  simpa only [presentationMap_seriesLift] using h

omit [CompleteSpace K] in
theorem generatesUnitIdeal_model (hunit : GeneratesUnitIdeal K P m g f) :
    RationalPresentation.GeneratesUnitIdeal K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) := by
  change Ideal.span (insert (presentationMap K (model K P) (seriesLift K P g))
    (Set.range fun j => presentationMap K (model K P) (seriesLift K P (f j)))) = ⊤
  simp only [presentationMap_seriesLift]
  let J : Ideal (model K P) :=
    Ideal.span (insert ((modelEquiv K P).symm g)
      (Set.range fun j => (modelEquiv K P).symm (f j)))
  change J = ⊤
  apply J.eq_top_iff_one.mpr
  have hle : Ideal.span (insert g (Set.range f)) ≤
      Ideal.comap (modelEquiv K P).symm.toAlgEquiv.toAlgHom.toRingHom J := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))
  have h1 := hle (show (1 : P) ∈ Ideal.span (insert g (Set.range f)) by
    rw [hunit]
    trivial)
  simpa only [Ideal.mem_comap, map_one] using h1

/-- Denominator invertibility is derived from the original unit ideal. -/
theorem isUnit_baseMap_denominator (hunit : GeneratesUnitIdeal K P m g f) :
    IsUnit (baseMap K P m g f g) := by
  have h := RationalPresentation.isUnit_baseMap_denominator K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))
    (generatesUnitIdeal_model K P m g f hunit)
  change IsUnit (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm g))
  simpa only [presentationMap_seriesLift] using h

theorem comap_mem_locus (x : BanachSpectrum (algebra K P m g f)) :
    BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom x ∈ locus K P m g f := by
  have h := RationalPresentation.comap_mem_locus K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) x
  intro j
  have hj := h j
  change x (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))
      (presentationMap K (model K P) (seriesLift K P (f j)))) ≤
    x (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j))
        (presentationMap K (model K P) (seriesLift K P g))) at hj
  change x (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm (f j))) ≤
    x (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm g))
  simpa only [presentationMap_seriesLift] using hj

omit [CompleteSpace K] in
theorem modelPoint_mem_locus (x : BanachSpectrum P) (hx : x ∈ locus K P m g f) :
    (modelEquiv K P).spectrumHomeomorph x ∈
      RationalPresentation.locus K P.arity m P.ideal
        (seriesLift K P g) (fun j => seriesLift K P (f j)) := by
  intro j
  change x (modelEquiv K P (presentationMap K (model K P) (seriesLift K P (f j)))) ≤
    x (modelEquiv K P (presentationMap K (model K P) (seriesLift K P g)))
  simpa only [modelEquiv_presentationMap_seriesLift] using hx j

/-- A point over the rational locus is constructed in the actual completed
residue field of its relation-model point. -/
def pointLift (hunit : GeneratesUnitIdeal K P m g f)
    (x : BanachSpectrum P) (hx : x ∈ locus K P m g f) :
    BanachSpectrum (algebra K P m g f) :=
  RationalPresentation.pointLift K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))
    (generatesUnitIdeal_model K P m g f hunit)
    ((modelEquiv K P).spectrumHomeomorph x) (modelPoint_mem_locus K P m g f x hx)

theorem comap_pointLift (hunit : GeneratesUnitIdeal K P m g f)
    (x : BanachSpectrum P) (hx : x ∈ locus K P m g f) :
    BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom
      (pointLift K P m g f hunit x hx) = x := by
  have h := RationalPresentation.comap_pointLift K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))
    (generatesUnitIdeal_model K P m g f hunit)
    ((modelEquiv K P).spectrumHomeomorph x) (modelPoint_mem_locus K P m g f x hx)
  apply BanachSpectrum.ext
  intro a
  have ha := congrArg (fun z : BanachSpectrum (model K P) =>
    z ((modelEquiv K P).symm a)) h
  change pointLift K P m g f hunit x hx (baseMap K P m g f a) =
    x (modelEquiv K P ((modelEquiv K P).symm a)) at ha
  change pointLift K P m g f hunit x hx (baseMap K P m g f a) = x a
  simpa only [BoundedAlgEquiv.apply_symm_apply] using ha

theorem range_comap_baseMap (hunit : GeneratesUnitIdeal K P m g f) :
    Set.range (BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom) =
      locus K P m g f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact comap_mem_locus K P m g f y
  · intro hx
    exact ⟨pointLift K P m g f hunit x hx, comap_pointLift K P m g f hunit x hx⟩

theorem comap_baseMap_injective (hunit : GeneratesUnitIdeal K P m g f) :
    Function.Injective (BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom) := by
  intro x y h
  apply RationalPresentation.comap_baseMap_injective K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j))
    (generatesUnitIdeal_model K P m g f hunit)
  apply BanachSpectrum.ext
  intro a
  have ha := congrArg (fun z : BanachSpectrum P => z (modelEquiv K P a)) h
  change x (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm
      (modelEquiv K P a))) =
    y (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm
        (modelEquiv K P a))) at ha
  change x (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) a) =
    y (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) a)
  simpa only [BoundedAlgEquiv.symm_apply_apply] using ha

/-- The spectrum map is a closed embedding with the exact rational-locus image. -/
theorem comap_baseMap_closedEmbedding (hunit : GeneratesUnitIdeal K P m g f) :
    Topology.IsClosedEmbedding (BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom) :=
  (BanachSpectrum.comapContinuous (baseMap K P m g f).toBoundedRingHom).continuous.isClosedEmbedding
    (comap_baseMap_injective K P m g f hunit)

variable (Q : PresentedStrictAffinoidAlgebra K)

/-- Transport between the actual relation models of equivalent base algebras. -/
def modelTransport (e : BoundedAlgEquiv K P Q) :
    BoundedAlgEquiv K (model K P) (model K Q) :=
  ((modelEquiv K P).trans e).trans (modelEquiv K Q).symm

omit [CompleteSpace K] in
theorem modelTransport_seriesLift (e : BoundedAlgEquiv K P Q) (a : P) :
    modelTransport K P Q e (presentationMap K (model K P) (seriesLift K P a)) =
      presentationMap K (model K Q) (seriesLift K Q (e a)) := by
  change (modelEquiv K Q).symm
    (e (modelEquiv K P (presentationMap K (model K P) (seriesLift K P a)))) = _
  rw [modelEquiv_presentationMap_seriesLift, presentationMap_seriesLift]

/-- A bounded equivalence of arbitrary presented base algebras carrying the
input elements induces a constructed bounded equivalence of their rational
quotients. Neither presentation arity nor series representatives need agree. -/
def equiv (g' : Q) (f' : Fin m → Q) (e : BoundedAlgEquiv K P Q)
    (hg : e g = g') (hf : ∀ j, e (f j) = f' j) :
    BoundedAlgEquiv K (algebra K P m g f) (algebra K Q m g' f') :=
  RationalPresentation.equiv K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) Q.arity Q.ideal
    (seriesLift K Q g') (fun j => seriesLift K Q (f' j)) (modelTransport K P Q e)
    (by rw [modelTransport_seriesLift, hg])
    (fun j => by rw [modelTransport_seriesLift, hf j])

theorem equiv_comp_baseMap (g' : Q) (f' : Fin m → Q)
    (e : BoundedAlgEquiv K P Q) (hg : e g = g') (hf : ∀ j, e (f j) = f' j) :
    (equiv K P m g f Q g' f' e hg hf).toBoundedAlgHom.comp (baseMap K P m g f) =
      (baseMap K Q m g' f').comp e.toBoundedAlgHom := by
  have h := RationalPresentation.equiv_comp_baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) Q.arity Q.ideal
    (seriesLift K Q g') (fun j => seriesLift K Q (f' j)) (modelTransport K P Q e)
    (by rw [modelTransport_seriesLift, hg])
    (fun j => by rw [modelTransport_seriesLift, hf j])
  apply BoundedAlgHom.ext
  intro a
  have ha := congrArg (fun χ => χ ((modelEquiv K P).symm a)) h
  change equiv K P m g f Q g' f' e hg hf (baseMap K P m g f a) =
    baseMap K Q m g' f' (e (modelEquiv K P ((modelEquiv K P).symm a))) at ha
  change equiv K P m g f Q g' f' e hg hf (baseMap K P m g f a) =
    baseMap K Q m g' f' (e a)
  simpa only [BoundedAlgEquiv.apply_symm_apply] using ha

theorem equiv_fractionCoordinate (g' : Q) (f' : Fin m → Q)
    (e : BoundedAlgEquiv K P Q) (hg : e g = g') (hf : ∀ j, e (f j) = f' j)
    (j : Fin m) :
    equiv K P m g f Q g' f' e hg hf (fractionCoordinate K P m g f j) =
      fractionCoordinate K Q m g' f' j :=
  RationalPresentation.equiv_newCoordinate K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) Q.arity Q.ideal
    (seriesLift K Q g') (fun j => seriesLift K Q (f' j)) _ _ _ j

theorem spectrum_equiv_over_base (g' : Q) (f' : Fin m → Q)
    (e : BoundedAlgEquiv K P Q) (hg : e g = g') (hf : ∀ j, e (f j) = f' j)
    (x : BanachSpectrum (algebra K Q m g' f')) :
    BanachSpectrum.comap (baseMap K P m g f).toBoundedRingHom
        ((equiv K P m g f Q g' f' e hg hf).spectrumHomeomorph x) =
      e.spectrumHomeomorph
        (BanachSpectrum.comap (baseMap K Q m g' f').toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (congrArg (fun χ => χ a)
    (equiv_comp_baseMap K P m g f Q g' f' e hg hf))

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

/-- Construct a bounded extension for actual bounded solutions of `g*b_j=f_j`.
The target may be any complete ultrametric normed algebra. -/
def liftFromBase (φ : BoundedAlgHom K P B) (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ g * b j = φ (f j)) :
    BoundedAlgHom K (algebra K P m g f) B :=
  RationalPresentation.liftFromBase K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) B
    (φ.comp (modelEquiv K P).toBoundedAlgHom) b hb (fun j => by
      change φ (modelEquiv K P (presentationMap K (model K P) (seriesLift K P g))) *
        b j = φ (modelEquiv K P (presentationMap K (model K P) (seriesLift K P (f j))))
      simpa only [modelEquiv_presentationMap_seriesLift] using heq j)

theorem liftFromBase_comp_baseMap (φ : BoundedAlgHom K P B) (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ g * b j = φ (f j)) :
    (liftFromBase K P m g f B φ b hb heq).comp (baseMap K P m g f) = φ := by
  have h := RationalPresentation.liftFromBase_comp_baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) B
    (φ.comp (modelEquiv K P).toBoundedAlgHom) b hb
    (fun j => by
      change φ (modelEquiv K P (presentationMap K (model K P) (seriesLift K P g))) *
        b j = φ (modelEquiv K P (presentationMap K (model K P) (seriesLift K P (f j))))
      simpa only [modelEquiv_presentationMap_seriesLift] using heq j)
  apply BoundedAlgHom.ext
  intro a
  have ha := congrArg (fun χ => χ ((modelEquiv K P).symm a)) h
  change liftFromBase K P m g f B φ b hb heq (baseMap K P m g f a) =
    φ (modelEquiv K P ((modelEquiv K P).symm a)) at ha
  change liftFromBase K P m g f B φ b hb heq (baseMap K P m g f a) = φ a
  simpa only [BoundedAlgEquiv.apply_symm_apply] using ha

theorem liftFromBase_fractionCoordinate (φ : BoundedAlgHom K P B) (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ g * b j = φ (f j)) (j : Fin m) :
    liftFromBase K P m g f B φ b hb heq (fractionCoordinate K P m g f j) = b j :=
  RationalPresentation.liftFromBase_coordinate K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) B _ _ _ _ j

omit [IsUltrametricDist B] [CompleteSpace B] in
theorem hom_ext_base (hunit : GeneratesUnitIdeal K P m g f)
    (φ ψ : BoundedAlgHom K (algebra K P m g f) B)
    (h : φ.comp (baseMap K P m g f) = ψ.comp (baseMap K P m g f)) : φ = ψ := by
  apply RationalPresentation.hom_ext_base K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) B
    (generatesUnitIdeal_model K P m g f hunit)
  apply BoundedAlgHom.ext
  intro a
  have ha := congrArg (fun χ => χ (modelEquiv K P a)) h
  change φ (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm
      (modelEquiv K P a))) =
    ψ (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) ((modelEquiv K P).symm
        (modelEquiv K P a))) at ha
  change φ (RationalPresentation.baseMap K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (f j)) a) =
    ψ (RationalPresentation.baseMap K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (f j)) a)
  simpa only [BoundedAlgEquiv.symm_apply_apply] using ha

/-- The extension is unique when the actual denominator and numerators
generate the unit ideal in `P`. Power boundedness remains explicit. -/
theorem existsUnique_extension (hunit : GeneratesUnitIdeal K P m g f)
    (φ : BoundedAlgHom K P B) (b : Fin m → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (heq : ∀ j, φ g * b j = φ (f j)) :
    ∃! ψ : BoundedAlgHom K (algebra K P m g f) B,
      ψ.comp (baseMap K P m g f) = φ := by
  refine ⟨liftFromBase K P m g f B φ b hb heq,
    liftFromBase_comp_baseMap K P m g f B φ b hb heq, fun ψ hψ => ?_⟩
  apply hom_ext_base K P m g f B hunit
  rw [hψ, liftFromBase_comp_baseMap]

/-- All localization properties for actual affinoid-algebra elements. -/
theorem localization : LocalizationStatement.{u, v} := by
  intro K _ _ _ P m g f
  refine ⟨coordinate_equation K P m g f, comap_mem_locus K P m g f, ?_, ?_, ?_⟩
  · intro hunit
    refine ⟨isUnit_baseMap_denominator K P m g f hunit,
      range_comap_baseMap K P m g f hunit,
      comap_baseMap_closedEmbedding K P m g f hunit, ?_⟩
    intro B _ _ φ ψ h
    exact hom_ext_base K P m g f B hunit φ ψ h
  · intro B _ _ _ _ φ b hb heq
    exact ⟨liftFromBase K P m g f B φ b hb heq,
      liftFromBase_comp_baseMap K P m g f B φ b hb heq,
      liftFromBase_fractionCoordinate K P m g f B φ b hb heq⟩
  · intro Q g' f' e hg hf
    exact ⟨equiv K P m g f Q g' f' e hg hf,
      equiv_comp_baseMap K P m g f Q g' f' e hg hf,
      equiv_fractionCoordinate K P m g f Q g' f' e hg hf,
      spectrum_equiv_over_base K P m g f Q g' f' e hg hf⟩

end Langlands.Analytic.RationalLocalization
