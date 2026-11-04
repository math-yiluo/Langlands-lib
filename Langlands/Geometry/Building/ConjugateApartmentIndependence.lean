import Langlands.Geometry.Building.ConjugateApartmentRealization
import Langlands.Geometry.Building.CrossTorusApartmentComparison
import Langlands.GroupScheme.Rational.TorusTransporterOrbit

/-! # Independence of conjugate valuation apartments from their transporter -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ G}
  (e e' : S ≅ S') (g g' : rationalPoints G)
  (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
  (h' : i ≫ (G.innerIso g').hom = CommGroupScheme.groupHom e'.hom ≫ j)

/-- The ratio of two actual transporters, in the original source normalizer. -/
def transporterDifferenceNormalizer : normalizerPoints i :=
  ⟨g'⁻¹ * g, inv_mul_mem_normalizerPoints_of_transporters h h'⟩

@[simp] theorem transporterDifferenceNormalizer_val :
    (transporterDifferenceNormalizer e e' g g' h h' : rationalPoints G) = g'⁻¹ * g :=
  rfl

namespace RootFunctionFamily

variable [Mono i.hom.hom.left]

/-- Changing the actual transporter is the original source-normalizer action. -/
theorem transportEquiv_conjugation_compare (φ : RootFunctionFamily S G) :
    transportEquiv e (G.innerIso g) φ =
      transportEquiv e' (G.innerIso g')
        (transporterDifferenceNormalizer e e' g g' h h' • φ) := by
  let n := transporterDifferenceNormalizer e e' g g' h h'
  have hn : IsNormalizingPoint i (n : rationalPoints G) (e ≪≫ e'.symm) :=
    isNormalizingPoint_inv_mul_of_transporters h h'
  apply RootFunctionFamily.ext
  intro a u
  have ha : weylAction i n⁻¹ ((characterLattice.congr e').symm a) =
      (characterLattice.congr e).symm a := by
    rw [weylAction_eq i (n := n⁻¹) hn.inv]
    simp only [characterLattice.congr_symm_apply, Iso.symm_inv, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have hu : (n : rationalPoints G)⁻¹ *
      rationalPoints.map (G.innerIso g').inv u * (n : rationalPoints G) =
      rationalPoints.map (G.innerIso g).inv u := by
    simp only [rationalPoints.map_apply, ← innerIso_inv_hom, comp_innerIso_hom,
      constantPoint_self, inv_inv]
    change (g'⁻¹ * g)⁻¹ * (g'⁻¹ * u * g') * (g'⁻¹ * g) = g⁻¹ * u * g
    group
  rw [transportEquiv_apply, transportEquiv_apply, smul_apply]
  exact (congrArg₂ (fun a u => φ a u) ha hu).symm

end RootFunctionFamily

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- An identity-on-families comparison retains the original valuation family. -/
theorem apartmentAffineEquivOfCarrierEq_val (D₀ E₀ : KPApartmentData i ω)
    (hDE : D₀.carrier = E₀.carrier) (x : D₀.Apartment) :
    (apartmentAffineEquivOfCarrierEq D₀ E₀ hDE x).val = x.val := rfl

/-- An identity-on-families comparison has identity derivative. -/
theorem apartmentAffineEquivOfCarrierEq_linear (D₀ E₀ : KPApartmentData i ω)
    (hDE : D₀.carrier = E₀.carrier) :
    (apartmentAffineEquivOfCarrierEq D₀ E₀ hDE).linear =
      LinearEquiv.refl ℝ (TranslationSpace i) := rfl

/-- The entire transported apartment data depends only on the actual target embedding. -/
theorem transport_conjugation_independent :
    D.transport e (G.innerIso g) h = D.transport e' (G.innerIso g') h' := by
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  apply D.transport_eq_of_mem e (G.innerIso g) h (D.transport e' (G.innerIso g') h') x
  exact ⟨transporterDifferenceNormalizer e e' g g' h h' • x.val,
    D.smul_mem _ _ x.mem,
    (RootFunctionFamily.transportEquiv_conjugation_compare e e' g g' h h' x.val).symm⟩

/-- Identify both actual target apartments by the identity on their valuation families. -/
def conjugateApartmentIdentification :
    (D.transport e (G.innerIso g) h).Apartment ≃ᵃ[ℝ]
      (D.transport e' (G.innerIso g') h').Apartment :=
  apartmentAffineEquivOfCarrierEq _ _
    (congrArg KPApartmentData.carrier
      (D.transport_conjugation_independent e e' g g' h h'))

/-- The identification retains every valuation family, with no change of coordinates. -/
@[simp] theorem conjugateApartmentIdentification_val
    (x : (D.transport e (G.innerIso g) h).Apartment) :
    (D.conjugateApartmentIdentification e e' g g' h h' x).val = x.val :=
  apartmentAffineEquivOfCarrierEq_val _ _ _ x

/-- Its derivative on the common target translation space is the identity. -/
@[simp] theorem conjugateApartmentIdentification_linear :
    (D.conjugateApartmentIdentification e e' g g' h h').linear =
      LinearEquiv.refl ℝ (TranslationSpace j) :=
  apartmentAffineEquivOfCarrierEq_linear _ _ _

/-- On source coordinates the same identification uses exactly the original normalizer action. -/
theorem conjugateApartmentIdentification_transport (x : D.Apartment) :
    D.conjugateApartmentIdentification e e' g g' h h'
        (D.apartmentTransportEquiv e (G.innerIso g) h x) =
      D.apartmentTransportEquiv e' (G.innerIso g') h'
        (transporterDifferenceNormalizer e e' g g' h h' • x) := by
  apply Apartment.ext
  exact RootFunctionFamily.transportEquiv_conjugation_compare e e' g g' h h' x.val

/-- The actual map of the target valuation apartment into the original quotient is independent. -/
theorem conjugateApartmentMap_independent
    (x : (D.transport e (G.innerIso g) h).Apartment) :
    D.conjugateApartmentMap e' g' h'
        (D.conjugateApartmentIdentification e e' g g' h h' x) =
      D.conjugateApartmentMap e g h x := by
  obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e (G.innerIso g) h).surjective x
  rw [D.conjugateApartmentIdentification_transport, D.conjugateApartmentMap_transport,
    D.conjugateApartmentMap_transport, apartmentMap_smul, smul_smul,
    transporterDifferenceNormalizer_val, mul_inv_cancel_left]

/-- In particular both realizations have the same actual apartment subset. -/
theorem range_conjugateApartmentMap_independent :
    Set.range (D.conjugateApartmentMap e g h) =
      Set.range (D.conjugateApartmentMap e' g' h') := by
  apply Set.ext
  intro q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨D.conjugateApartmentIdentification e e' g g' h h' x,
      D.conjugateApartmentMap_independent e e' g g' h h' x⟩
  · rintro ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := (D.conjugateApartmentIdentification e e' g g' h h').surjective x'
    exact ⟨x, (D.conjugateApartmentMap_independent e e' g g' h h' x).symm⟩

end KPApartmentData

end Langlands.Geometry.Building
