import Langlands.Geometry.Building.AffineWeylTransport

/-! # Facets under an affine comparison of root arrangements -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {W : Type uW} {B : Type uB} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- Inverse precomposition of the roots preserves exactly their sign relation. -/
theorem facetRel_transportedRoots_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x y : A) :
    facetRel (transportedRoots e Ψ) (e x) (e y) ↔ facetRel Ψ x y := by
  constructor
  · intro h ψ hψ
    simpa only [affineFunctionalTransport_apply, e.symm_apply_apply] using
      h (affineFunctionalTransport e ψ) ⟨ψ, hψ, rfl⟩
  · rintro h _ ⟨ψ, hψ, rfl⟩
    simpa only [affineFunctionalTransport_apply, e.symm_apply_apply] using h ψ hψ

/-- The entire facet, rather than only points in a common facet, is transported. -/
theorem image_facet_transportedRoots (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    e '' facet Ψ x = facet (transportedRoots e Ψ) (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (facetRel_transportedRoots_iff e Ψ x z).2 hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (facetRel_transportedRoots_iff e Ψ x (e.symm y)).1
    simpa only [mem_facet, e.apply_symm_apply] using hy

/-- An affine comparison of root sets preserves and reflects being a full facet. -/
theorem isFacet_image_transportedRoots_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (Fa : Set A) :
    IsFacet (transportedRoots e Ψ) (e '' Fa) ↔ IsFacet Ψ Fa := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply Set.image_injective.mpr e.injective
    rw [image_facet_transportedRoots, e.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (image_facet_transportedRoots e Ψ x).symm⟩

/-- The explicit root-set equality used in an apartment comparison gives its
facet comparison with no apartment-axiom hypotheses. -/
theorem isFacet_image_iff_of_transportedRoots_eq (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) (Fa : Set A) :
    IsFacet Φ (e '' Fa) ↔ IsFacet Ψ Fa := by
  rw [← h]
  exact isFacet_image_transportedRoots_iff e Ψ Fa

/-- Facet closures, defined by weak sign conditions, are also transported. -/
theorem image_facetClosure_transportedRoots (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    e '' facetClosure Ψ x = facetClosure (transportedRoots e Ψ) (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    simpa only [affineFunctionalTransport_apply, e.symm_apply_apply] using hz ψ hψ
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro ψ hψ
    simpa only [affineFunctionalTransport_apply, e.symm_apply_apply] using
      hy (affineFunctionalTransport e ψ) ⟨ψ, hψ, rfl⟩

/-- A comparison identifies chambers because it preserves both full facets and
nonvanishing of all roots. -/
theorem isChamber_image_transportedRoots_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (Ca : Set A) :
    IsChamber (transportedRoots e Ψ) (e '' Ca) ↔ IsChamber Ψ Ca := by
  constructor
  · rintro ⟨y, hy, hCy⟩
    refine ⟨e.symm y, ?_, ?_⟩
    · intro ψ hψ
      exact hy (affineFunctionalTransport e ψ) ⟨ψ, hψ, rfl⟩
    · apply Set.image_injective.mpr e.injective
      rw [image_facet_transportedRoots, e.apply_symm_apply, hCy]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e x, ?_, (image_facet_transportedRoots e Ψ x).symm⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    simpa only [affineFunctionalTransport_apply, e.symm_apply_apply] using hx ψ hψ

/-- An affine identification of the complete root sets induces an equivalence
of the types of full facets, sending each facet to its image. -/
def facetEquivOfTransportedRootsEq (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) :
    {Fa : Set A // IsFacet Ψ Fa} ≃ {Fb : Set B // IsFacet Φ Fb} :=
  e.toEquiv.setCongr.subtypeEquiv fun Fa =>
    (isFacet_image_iff_of_transportedRoots_eq e h Fa).symm

@[simp] theorem facetEquivOfTransportedRootsEq_apply (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) (Fa : {Fa : Set A // IsFacet Ψ Fa}) :
    (facetEquivOfTransportedRootsEq e h Fa).val = e '' Fa.val := rfl

/-- The same image operation gives an equivalence of the types of chambers. -/
def chamberEquivOfTransportedRootsEq (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) :
    {Ca : Set A // IsChamber Ψ Ca} ≃ {Cb : Set B // IsChamber Φ Cb} :=
  e.toEquiv.setCongr.subtypeEquiv fun Ca => by
    rw [← h]
    exact (isChamber_image_transportedRoots_iff e Ψ Ca).symm

@[simp] theorem chamberEquivOfTransportedRootsEq_apply (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)}
    (h : transportedRoots e Ψ = Φ) (Ca : {Ca : Set A // IsChamber Ψ Ca}) :
    (chamberEquivOfTransportedRootsEq e h Ca).val = e '' Ca.val := rfl

end Langlands.Geometry.Building.AffineRootSystem
