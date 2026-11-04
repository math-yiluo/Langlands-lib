import Langlands.Geometry.Building.CrossTorusApartment

/-! # Comparing a transported apartment with separately supplied data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}

/-- Two full equipollence classes containing one common family have the same carrier. -/
theorem carrier_eq_of_common_mem {D E : KPApartmentData i ω}
    {φ : RootFunctionFamily S G} (hD : φ ∈ D.carrier) (hE : φ ∈ E.carrier) :
    D.carrier = E.carrier := by
  apply Set.ext
  intro ψ
  exact (D.mem_iff_equipollent hD).trans (E.mem_iff_equipollent hE).symm

/-- A common valuation determines equality of the full apartment data. -/
theorem eq_of_common_mem {D E : KPApartmentData i ω}
    {φ : RootFunctionFamily S G} (hD : φ ∈ D.carrier) (hE : φ ∈ E.carrier) : D = E :=
  ext (carrier_eq_of_common_mem hD hE)

/-- Equal carriers give the identity on the original valuation points as an affine map. -/
def apartmentAffineEquivOfCarrierEq (D E : KPApartmentData i ω)
    (hDE : D.carrier = E.carrier) : D.Apartment ≃ᵃ[ℝ] E.Apartment where
  toFun x := ⟨x.val, hDE ▸ x.mem⟩
  invFun y := ⟨y.val, hDE.symm ▸ y.mem⟩
  left_inv _ := rfl
  right_inv _ := rfl
  linear := LinearEquiv.refl ℝ (TranslationSpace i)
  map_vadd' x v := by
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    apply Apartment.ext
    rfl

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω) (E : KPApartmentData j ω)

/-- One transported source point in the target class identifies the entire target data. -/
theorem transport_eq_of_mem (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    D.transport e f h = E :=
  eq_of_common_mem (D := D.transport e f h)
    ⟨x₀.val, x₀.mem, rfl⟩ h₀

/-- Equality with chosen target data is equivalent to a single common transported point. -/
theorem transport_eq_iff_exists_mem :
    D.transport e f h = E ↔
      ∃ x : D.Apartment, RootFunctionFamily.transportEquiv e f x.val ∈ E.carrier := by
  constructor
  · intro hDE
    obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
    exact ⟨x, hDE ▸ (show RootFunctionFamily.transportEquiv e f x.val ∈
      (D.transport e f h).carrier from ⟨x.val, x.mem, rfl⟩)⟩
  · rintro ⟨x, hx⟩
    exact D.transport_eq_of_mem e f h E x hx

/-- Compare with separately supplied target data from a single compatible source point. -/
def apartmentTransportAffineEquivOfMem (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    D.Apartment ≃ᵃ[ℝ] E.Apartment :=
  (D.apartmentTransportAffineEquiv e f h).trans
    (apartmentAffineEquivOfCarrierEq (D.transport e f h) E
      (congrArg KPApartmentData.carrier (D.transport_eq_of_mem e f h E x₀ h₀)))

/-- The comparison's underlying family is the actual original family transport. -/
@[simp] theorem apartmentTransportAffineEquivOfMem_val (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) (x : D.Apartment) :
    (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x).val =
      RootFunctionFamily.transportEquiv e f x.val := rfl

/-- The comparison to chosen data has the same actual quotient derivative. -/
@[simp] theorem apartmentTransportAffineEquivOfMem_linear (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).linear =
      translationSpaceTransportEquiv e f h := by
  apply LinearEquiv.ext
  intro v
  rfl

/-- The actual comparison is independent of the witness used to identify the two classes. -/
theorem apartmentTransportAffineEquivOfMem_independent (x₀ x₁ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)
    (h₁ : RootFunctionFamily.transportEquiv e f x₁.val ∈ E.carrier) :
    D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ =
      D.apartmentTransportAffineEquivOfMem e f h E x₁ h₁ := by
  apply AffineEquiv.ext
  intro x
  apply Apartment.ext
  rfl

/-- The comparison uses the original source and chosen target normalizer actions. -/
theorem apartmentTransportAffineEquivOfMem_smul (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)
    (n : normalizerPoints i) (x : D.Apartment) :
    D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ (n • x) =
      normalizerPointsTransportEquiv e f h n •
        D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x := by
  apply Apartment.ext
  exact RootFunctionFamily.transportEquiv_smul e f h n x.val

/-- Every point value remains unchanged on simultaneous actual forward images. -/
@[simp] theorem apartmentTransportAffineEquivOfMem_value (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)
    (x : D.Apartment) (a : characterLattice S) (g : rationalPoints G) :
    (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x).val
        (characterLattice.congr e a) (rationalPoints.map f.hom g) = x.val a g :=
  RootFunctionFamily.transportEquiv_apply_map e f x.val a g

/-- A map with the prescribed actual valuation families is uniquely this comparison. -/
theorem apartmentTransportAffineEquivOfMem_unique (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)
    (c : D.Apartment →ᵃ[ℝ] E.Apartment)
    (hc : ∀ x, (c x).val = RootFunctionFamily.transportEquiv e f x.val) :
    c = (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀).toAffineMap := by
  apply AffineMap.ext
  intro x
  exact Apartment.ext (hc x)

section Conjugation

variable {jG : S'.toGrp ⟶ G} [Mono jG.hom.hom.left]
  (E₀ : KPApartmentData jG ω) (g : rationalPoints G)
  (hg : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ jG)

/-- Actual inner conjugation gives an affine comparison whenever one image point matches. -/
def apartmentConjugationAffineEquivOfMem (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e (G.innerIso g) x₀.val ∈ E₀.carrier) :
    D.Apartment ≃ᵃ[ℝ] E₀.Apartment :=
  D.apartmentTransportAffineEquivOfMem e (G.innerIso g) hg E₀ x₀ h₀

/-- Conjugation carries the original valuation value at `u` to that at `g*u*g⁻¹`. -/
theorem apartmentConjugationAffineEquivOfMem_value (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e (G.innerIso g) x₀.val ∈ E₀.carrier)
    (x : D.Apartment) (a : characterLattice S) (u : rationalPoints G) :
    (D.apartmentConjugationAffineEquivOfMem e E₀ g hg x₀ h₀ x).val
        (characterLattice.congr e a) (g * u * g⁻¹) = x.val a u := by
  simpa only [apartmentConjugationAffineEquivOfMem, rationalPoints.map_apply,
    comp_innerIso_hom, constantPoint_self] using
    D.apartmentTransportAffineEquivOfMem_value e (G.innerIso g) hg E₀ x₀ h₀ x a u

/-- The conjugation derivative is the quotient map from the actual torus isomorphism. -/
theorem apartmentConjugationAffineEquivOfMem_linear (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e (G.innerIso g) x₀.val ∈ E₀.carrier) :
    (D.apartmentConjugationAffineEquivOfMem e E₀ g hg x₀ h₀).linear =
      translationSpaceTransportEquiv e (G.innerIso g) hg :=
  D.apartmentTransportAffineEquivOfMem_linear e (G.innerIso g) hg E₀ x₀ h₀

end Conjugation

end Langlands.Geometry.Building.KPApartmentData
