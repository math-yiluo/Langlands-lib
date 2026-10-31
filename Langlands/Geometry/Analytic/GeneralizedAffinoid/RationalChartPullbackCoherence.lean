import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Coherence of chosen positive-radius rational chart pullbacks -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B C D : PresentedAffinoidAlgebra K}

/-- The chosen identity-pullback coefficients represent the original classes. -/
theorem pullback_id_denominator_class (d : RationalChart K A) :
    presentationMap K A (pullback (BoundedAlgHom.id K A) d).denominator =
      presentationMap K A d.denominator := by
  exact pullback_denominator_class (BoundedAlgHom.id K A) d

theorem pullback_id_numerator_class (d : RationalChart K A) (j : Fin d.arity) :
    presentationMap K A ((pullback (BoundedAlgHom.id K A) d).numerators j) =
      presentationMap K A (d.numerators j) := by
  exact pullback_numerator_class (BoundedAlgHom.id K A) d j

/-- Actual representative maps identify identity pullback with the original chart. -/
def pullbackIdIso (d : RationalChart K A) :
    pullback (BoundedAlgHom.id K A) d ≅ d where
  hom := {
    restriction := RationalPresentation.representativeMap K A d.radii
      d.denominator (pullback (BoundedAlgHom.id K A) d).denominator
      d.numerators (pullback (BoundedAlgHom.id K A) d).numerators
      (pullback_id_denominator_class d).symm
      (fun j => (pullback_id_numerator_class d j).symm)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K A d.radii
        d.denominator (pullback (BoundedAlgHom.id K A) d).denominator
        d.numerators (pullback (BoundedAlgHom.id K A) d).numerators
        (pullback_id_denominator_class d).symm
        (fun j => (pullback_id_numerator_class d j).symm)) }
  inv := {
    restriction := RationalPresentation.representativeMap K A d.radii
      (pullback (BoundedAlgHom.id K A) d).denominator d.denominator
      (pullback (BoundedAlgHom.id K A) d).numerators d.numerators
      (pullback_id_denominator_class d) (pullback_id_numerator_class d)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K A d.radii
        (pullback (BoundedAlgHom.id K A) d).denominator d.denominator
        (pullback (BoundedAlgHom.id K A) d).numerators d.numerators
        (pullback_id_denominator_class d) (pullback_id_numerator_class d)) }
  hom_inv_id := @Subsingleton.elim (Restriction _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (Restriction _ _) inferInstance _ _

/-- Direct and iterated pullback have the same denominator class. -/
theorem pullback_comp_denominator_class
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) (d : RationalChart K A) :
    presentationMap K C (pullback (ψ.comp φ) d).denominator =
      presentationMap K C (pullback ψ (pullback φ d)).denominator := by
  simp only [pullback_denominator_class, BoundedAlgHom.comp_apply]

/-- Direct and iterated pullback have the same numerator classes. -/
theorem pullback_comp_numerator_class
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (d : RationalChart K A) (j : Fin d.arity) :
    presentationMap K C ((pullback (ψ.comp φ) d).numerators j) =
      presentationMap K C ((pullback ψ (pullback φ d)).numerators j) := by
  calc
    presentationMap K C ((pullback (ψ.comp φ) d).numerators j) =
        ψ (φ (presentationMap K A (d.numerators j))) :=
      pullback_numerator_class (ψ.comp φ) d j
    _ = ψ (presentationMap K B ((pullback φ d).numerators j)) :=
      congrArg ψ (pullback_numerator_class φ d j).symm
    _ = presentationMap K C ((pullback ψ (pullback φ d)).numerators j) :=
      (pullback_numerator_class ψ (pullback φ d) j).symm

/-- The comparison uses actual maps of the two concrete rational quotients. -/
def pullbackCompIso (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (d : RationalChart K A) :
    pullback (ψ.comp φ) d ≅ pullback ψ (pullback φ d) where
  hom := {
    restriction := RationalPresentation.representativeMap K C d.radii
      (pullback ψ (pullback φ d)).denominator (pullback (ψ.comp φ) d).denominator
      (pullback ψ (pullback φ d)).numerators (pullback (ψ.comp φ) d).numerators
      (pullback_comp_denominator_class φ ψ d).symm
      (fun j => (pullback_comp_numerator_class φ ψ d j).symm)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K C d.radii
        (pullback ψ (pullback φ d)).denominator (pullback (ψ.comp φ) d).denominator
        (pullback ψ (pullback φ d)).numerators (pullback (ψ.comp φ) d).numerators
        (pullback_comp_denominator_class φ ψ d).symm
        (fun j => (pullback_comp_numerator_class φ ψ d j).symm)) }
  inv := {
    restriction := RationalPresentation.representativeMap K C d.radii
      (pullback (ψ.comp φ) d).denominator (pullback ψ (pullback φ d)).denominator
      (pullback (ψ.comp φ) d).numerators (pullback ψ (pullback φ d)).numerators
      (pullback_comp_denominator_class φ ψ d) (pullback_comp_numerator_class φ ψ d)
    comp_baseMap := BoundedAlgHom.ext
      (RationalPresentation.representativeMap_baseMap K C d.radii
        (pullback (ψ.comp φ) d).denominator (pullback ψ (pullback φ d)).denominator
        (pullback (ψ.comp φ) d).numerators (pullback ψ (pullback φ d)).numerators
        (pullback_comp_denominator_class φ ψ d) (pullback_comp_numerator_class φ ψ d)) }
  hom_inv_id := @Subsingleton.elim (Restriction _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (Restriction _ _) inferInstance _ _

variable [CompleteSpace K]

/-- Identity comparison is natural for actual bounded chart restrictions. -/
def pullbackIdNatIso (A : PresentedAffinoidAlgebra K) :
    pullbackFunctor (BoundedAlgHom.id K A) ≅ 𝟭 (RationalChart K A) :=
  NatIso.ofComponents pullbackIdIso
    (fun _ => @Subsingleton.elim (Restriction _ _) inferInstance _ _)

/-- Direct and successive coefficient pullback are naturally isomorphic. -/
def pullbackCompNatIso (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    pullbackFunctor (ψ.comp φ) ≅ pullbackFunctor φ ⋙ pullbackFunctor ψ :=
  NatIso.ofComponents (pullbackCompIso φ ψ)
    (fun _ => @Subsingleton.elim (Restriction _ _) inferInstance _ _)

/-- The identity comparison realizes exactly the constructed coefficient map. -/
theorem pullbackIdIso_hom_restriction (d : RationalChart K A) :
    (pullbackIdIso d).hom.restriction = pullbackMap (BoundedAlgHom.id K A) d := by
  apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
    (pullback (BoundedAlgHom.id K A) d).algebra d.generates
  exact (pullbackIdIso d).hom.comp_baseMap.trans
    (pullbackMap_comp_baseMap (BoundedAlgHom.id K A) d).symm

/-- The comparison identifies composite quotient transport with direct transport. -/
theorem pullbackCompIso_hom_transport
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) (d : RationalChart K A) :
    (pullbackCompIso φ ψ d).hom.restriction.comp
        ((pullbackMap ψ (pullback φ d)).comp (pullbackMap φ d)) =
      pullbackMap (ψ.comp φ) d := by
  apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
    (pullback (ψ.comp φ) d).algebra d.generates
  apply BoundedAlgHom.ext
  intro a
  change (pullbackCompIso φ ψ d).hom.restriction
    (pullbackMap ψ (pullback φ d) (pullbackMap φ d (d.baseMap a))) =
      pullbackMap (ψ.comp φ) d (d.baseMap a)
  rw [pullbackMap_baseMap, pullbackMap_baseMap, pullbackMap_baseMap]
  exact congrArg (fun η : BoundedAlgHom K C (pullback (ψ.comp φ) d).algebra =>
    η (ψ (φ a))) (pullbackCompIso φ ψ d).hom.comp_baseMap

/-- Identity coefficient pullback on spectra is the actual comparison map. -/
theorem pullbackIdIso_spectrumMap (d : RationalChart K A)
    (x : BanachSpectrum (pullback (BoundedAlgHom.id K A) d).algebra) :
    (pullbackIdIso d).hom.spectrumMap x =
      pullbackSpectrumMap (BoundedAlgHom.id K A) d x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun η : BoundedAlgHom K d.algebra
    (pullback (BoundedAlgHom.id K A) d).algebra => x (η a))
      (pullbackIdIso_hom_restriction d)

/-- The actual spectrum comparison intertwines direct and iterated pullback. -/
theorem pullbackCompIso_spectrumMap
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) (d : RationalChart K A)
    (x : BanachSpectrum (pullback (ψ.comp φ) d).algebra) :
    pullbackSpectrumMap φ d
        (pullbackSpectrumMap ψ (pullback φ d) ((pullbackCompIso φ ψ d).hom.spectrumMap x)) =
      pullbackSpectrumMap (ψ.comp φ) d x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun η : BoundedAlgHom K d.algebra
    (pullback (ψ.comp φ) d).algebra => x (η a))
      (pullbackCompIso_hom_transport φ ψ d)

/-- Coherence for the identity at the source of a coefficient map. -/
theorem pullbackCompIso_source_id (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullbackCompIso (BoundedAlgHom.id K A) φ d).hom ≫
        (pullbackFunctor φ).map (pullbackIdIso d).hom =
      𝟙 (pullback φ d) :=
  @Subsingleton.elim (Restriction _ _) inferInstance _ _

omit [CompleteSpace K] in
/-- Coherence for the identity at the target of a coefficient map. -/
theorem pullbackCompIso_target_id (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullbackCompIso φ (BoundedAlgHom.id K B) d).hom ≫
        (pullbackIdIso (pullback φ d)).hom =
      𝟙 (pullback φ d) :=
  @Subsingleton.elim (Restriction _ _) inferInstance _ _

/-- The two comparison paths for three successive maps agree. -/
theorem pullbackCompIso_assoc
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (χ : BoundedAlgHom K C D) (d : RationalChart K A) :
    (pullbackCompIso (ψ.comp φ) χ d).hom ≫
        (pullbackFunctor χ).map (pullbackCompIso φ ψ d).hom =
      (pullbackCompIso φ (χ.comp ψ) d).hom ≫
        (pullbackCompIso ψ χ (pullback φ d)).hom :=
  @Subsingleton.elim (Restriction _ _) inferInstance _ _

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
