import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness
import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation

/-! # The finite locus of a morphism

The finite locus of `f : X ⟶ Y` is the largest open of `Y` over which `f` is finite. For a
quasi-finite separated quasi-compact morphism of finite type to an affine scheme, it contains
every generic point of an irreducible component of `Y`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus

set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The largest open of the target over which `f` is finite. -/
def finiteLocus : Y.Opens := sSup {V : Y.Opens | IsFinite (f ∣_ V)}

theorem le_finiteLocus {V : Y.Opens} (hV : IsFinite (f ∣_ V)) : V ≤ finiteLocus f :=
  le_sSup hV

/-- Finiteness over an open passes to smaller opens. -/
theorem isFinite_restrict_of_le {V W : Y.Opens} (hVW : V ≤ W) (hW : IsFinite (f ∣_ W)) :
    IsFinite (f ∣_ V) := by
  have h2 := IsZariskiLocalAtTarget.restrict hW (W.ι ⁻¹ᵁ V)
  have h3 := (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite.{u}
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ V))).mp h2
  have heq : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVW
  exact (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite.{u}
    (morphismRestrictEq f heq)).mp h3

/-- `f` is finite over its finite locus. -/
theorem isFinite_restrict_finiteLocus : IsFinite (f ∣_ finiteLocus f) := by
  let W := finiteLocus f
  let ι := {V : Y.Opens // IsFinite (f ∣_ V)}
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun V : ι ↦ W.ι ⁻¹ᵁ V.1) ?_ ?_
  · rw [← Scheme.Hom.preimage_iSup]
    apply eq_top_iff.mpr
    intro x _
    have hx : W.ι x ∈ W := x.2
    obtain ⟨V, hV, hxV⟩ := (TopologicalSpace.Opens.mem_sSup).mp hx
    exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨V, hV⟩, hxV⟩
  · intro V
    have hle : V.1 ≤ W := le_finiteLocus f V.2
    have heq : W.ι ''ᵁ (W.ι ⁻¹ᵁ V.1) = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hle
    exact (MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite.{u}
      (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ V.1))).mpr
      ((MorphismProperty.arrow_mk_iso_iff @_root_.AlgebraicGeometry.IsFinite.{u}
        (morphismRestrictEq f heq)).mpr V.2)

/-- In a prime spectrum, generic points of irreducible components are minimal primes. -/
theorem mem_minimalPrimes_of_mem_genericPoints {A : Type u} [CommRing A] {x : PrimeSpectrum A}
    (hx : x ∈ genericPoints (PrimeSpectrum A)) : x.asIdeal ∈ minimalPrimes A := by
  rw [GenericPointAvoidance.mem_genericPoints_iff] at hx
  refine ⟨⟨x.isPrime, bot_le⟩, fun q hq hqx => ?_⟩
  have := hx ⟨q, hq.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).mp hqx)
  rw [← this]

/-- For a quasi-finite separated quasi-compact morphism of finite type to an affine scheme,
every generic point of the target lies in the finite locus. -/
theorem genericPoints_subset_finiteLocus [IsAffine Y] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f] :
    genericPoints Y ⊆ finiteLocus f := by
  intro η hη
  let e := Y.isoSpec
  have hgen : e.hom η ∈ genericPoints (Spec Γ(Y, ⊤)) := by
    rw [GenericPointAvoidance.mem_genericPoints_iff] at hη ⊢
    intro y hy
    obtain ⟨y, rfl⟩ := e.hom.homeomorph.surjective y
    have : y ⤳ η := (e.hom.homeomorph.isInducing.specializes_iff).mp hy
    rw [hη y this]
    rfl
  have hmin := mem_minimalPrimes_of_mem_genericPoints (A := Γ(Y, ⊤)) hgen
  obtain ⟨r, hr, hfin⟩ :=
    GenericFiniteness.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
      (f ≫ e.hom) _ hmin
  have hV : IsFinite (f ∣_ (e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
    rw [morphismRestrict_comp] at hfin
    exact (MorphismProperty.cancel_right_of_respectsIso @_root_.AlgebraicGeometry.IsFinite.{u}
      _ _).mp hfin
  apply le_finiteLocus f hV
  exact hr

end Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus
