import Langlands.Geometry.Building.CrossTorusValuation

/-! # Apartment data under actual cross-torus isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

open RootFunctionFamily

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}

/-- The carrier determines apartment data; the other fields are propositions. -/
@[ext] theorem ext {D E : KPApartmentData i ω} (h : D.carrier = E.carrier) : D = E := by
  cases D
  cases E
  cases h
  rfl

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- Carry the entire compatible, normalizer-stable orbit through the actual family map. -/
def transport (D : KPApartmentData i ω) : KPApartmentData j ω where
  carrier := RootFunctionFamily.transportEquiv e f '' D.carrier
  exists_eq_orbit := by
    obtain ⟨φ, hφ, hω, hc⟩ := D.exists_eq_orbit
    refine ⟨RootFunctionFamily.transportEquiv e f φ, hφ.transport e f h,
      hω.transport e f h, ?_⟩
    rw [hc]
    ext ψ
    constructor
    · rintro ⟨ψ, ⟨v, rfl⟩, rfl⟩
      exact ⟨cocharacterRealCongr e v, (transportEquiv_vadd e f φ v).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨v, rfl⟩ := (cocharacterRealCongr e).surjective v
      exact ⟨v +ᵥ φ, ⟨v, rfl⟩, transportEquiv_vadd e f φ v⟩
  smul_mem n ψ hψ := by
    obtain ⟨n, rfl⟩ := (normalizerPointsTransportEquiv e f h).surjective n
    obtain ⟨φ, hφ, rfl⟩ := hψ
    exact ⟨n • φ, D.smul_mem n φ hφ, transportEquiv_smul e f h n φ⟩

/-- The target carrier is precisely the image of the source carrier. -/
theorem transport_carrier (D : KPApartmentData i ω) :
    (D.transport e f h).carrier = RootFunctionFamily.transportEquiv e f '' D.carrier := rfl

/-- Membership is reflected by the original inverse family map. -/
theorem mem_transport_iff (D : KPApartmentData i ω) (ψ : RootFunctionFamily S' H) :
    ψ ∈ (D.transport e f h).carrier ↔
      (RootFunctionFamily.transportEquiv e f).symm ψ ∈ D.carrier := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    simpa only [Equiv.symm_apply_apply] using hφ
  · intro hψ
    exact ⟨_, hψ, Equiv.apply_symm_apply _ _⟩

/-- The actual isomorphisms identify the full types of valid apartment data. -/
def transportEquiv : KPApartmentData i ω ≃ KPApartmentData j ω where
  toFun := transport e f h
  invFun := transport e.symm f.symm (torusTransport_inverse_square e f h)
  left_inv D := by
    apply ext
    ext φ
    change φ ∈ (RootFunctionFamily.transportEquiv e f).symm ''
        (RootFunctionFamily.transportEquiv e f '' D.carrier) ↔ φ ∈ D.carrier
    constructor
    · rintro ⟨ψ, ⟨ξ, hξ, rfl⟩, hψ⟩
      rw [Equiv.symm_apply_apply] at hψ
      exact hψ ▸ hξ
    · intro hφ
      exact ⟨_, ⟨φ, hφ, rfl⟩, Equiv.symm_apply_apply _ _⟩
  right_inv E := by
    apply ext
    ext ψ
    change ψ ∈ RootFunctionFamily.transportEquiv e f ''
        ((RootFunctionFamily.transportEquiv e f).symm '' E.carrier) ↔ ψ ∈ E.carrier
    constructor
    · rintro ⟨φ, ⟨ξ, hξ, rfl⟩, hφ⟩
      rw [Equiv.apply_symm_apply] at hφ
      exact hφ ▸ hξ
    · intro hψ
      exact ⟨_, ⟨ψ, hψ, rfl⟩, Equiv.apply_symm_apply _ _⟩

/-- The data equivalence uses exactly the constructed orbit image. -/
@[simp] theorem transportEquiv_apply (D : KPApartmentData i ω) :
    transportEquiv e f h D = D.transport e f h := rfl

end Langlands.Geometry.Building.KPApartmentData
