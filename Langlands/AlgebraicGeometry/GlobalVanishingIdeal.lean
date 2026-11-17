import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Vanishing ideals in the ring of actual global sections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The ideal of global functions vanishing on a set of scheme points. -/
def globalVanishingIdeal (X : Scheme.{u}) (Z : Set X) : Ideal Γ(X, ⊤) :=
  PrimeSpectrum.vanishingIdeal (X.toSpecΓ '' Z)

theorem mem_globalVanishingIdeal (Z : Set X) (s : Γ(X, ⊤)) :
    s ∈ globalVanishingIdeal X Z ↔ ∀ x ∈ Z, x ∉ X.basicOpen s := by
  rw [globalVanishingIdeal, PrimeSpectrum.mem_vanishingIdeal]
  have he (x : X) :
      s ∈ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal ↔ x ∉ X.basicOpen s := by
    have hb := congrArg (fun U : X.Opens => x ∈ U) (X.toSpecΓ_preimage_basicOpen s)
    change (s ∉ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal) =
      (x ∈ X.basicOpen s) at hb
    simpa only [not_not] using not_congr hb.to_iff
  constructor
  · intro hs x hx
    exact (he x).1 (hs _ (Set.mem_image_of_mem _ hx))
  · rintro hs _ ⟨x, hx, rfl⟩
    exact (he x).2 (hs x hx)

theorem appTop_mem_globalVanishingIdeal (f : X ⟶ Y) (Z : Set X) (W : Set Y)
    (hf : Set.MapsTo f Z W) {s : Γ(Y, ⊤)}
    (hs : s ∈ globalVanishingIdeal Y W) :
    f.appTop s ∈ globalVanishingIdeal X Z := by
  rw [mem_globalVanishingIdeal] at hs ⊢
  intro x hx
  have he := congrArg (fun U : X.Opens => x ∈ U) (f.preimage_basicOpen_top s)
  exact fun hx' => hs (f x) (hf hx) (he.to_iff.mpr hx')

theorem zeroLocus_globalVanishingIdeal [IsAffine X] (Z : Set X) (hZ : IsClosed Z) :
    X.zeroLocus (U := ⊤) (globalVanishingIdeal X Z) = Z := by
  rw [← X.toSpecΓ_preimage_zeroLocus, globalVanishingIdeal,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hc : IsClosed (X.toSpecΓ '' Z) :=
    X.isoSpec.hom.homeomorph.isClosedMap Z hZ
  rw [hc.closure_eq]
  exact Set.preimage_image_eq Z X.isoSpec.hom.homeomorph.injective

theorem globalVanishingIdeal_ne_top {Z : Set X} (hZ : Z.Nonempty) :
    globalVanishingIdeal X Z ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := hZ
  have hmem : (1 : Γ(X, ⊤)) ∈ globalVanishingIdeal X Z := by rw [htop]; trivial
  have hz := (mem_globalVanishingIdeal Z 1).1 hmem x hx
  exact hz (by simp)

theorem globalVanishingIdeal_sup_eq_top [IsAffine X]
    {Z W : Set X} (hZ : IsClosed Z) (hW : IsClosed W) (hd : Disjoint Z W) :
    globalVanishingIdeal X Z ⊔ globalVanishingIdeal X W = ⊤ := by
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  rw [PrimeSpectrum.zeroLocus_sup]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  let x := X.isoSpec.inv p
  have hxZ : x ∈ Z := by
    rw [← zeroLocus_globalVanishingIdeal Z hZ]
    change p ∈ X.isoSpec.inv ⁻¹' X.zeroLocus (U := ⊤) (globalVanishingIdeal X Z)
    rw [X.isoSpec_inv_preimage_zeroLocus]
    exact hp.1
  have hxW : x ∈ W := by
    rw [← zeroLocus_globalVanishingIdeal W hW]
    change p ∈ X.isoSpec.inv ⁻¹' X.zeroLocus (U := ⊤) (globalVanishingIdeal X W)
    rw [X.isoSpec_inv_preimage_zeroLocus]
    exact hp.2
  exact Set.disjoint_left.mp hd hxZ hxW

end Langlands.AlgebraicGeometry
