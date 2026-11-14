import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion
import Langlands.AbelianScheme.FiberwiseIsogeny
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # Detecting isomorphisms on the two fibres of a discrete valuation ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A morphism over a local domain is an isomorphism on its specified
fraction-field fibre and on its canonical closed fibre. -/
def IsGenericSpecialFibreIsomorphism
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) : Prop :=
  IsIso ((Over.pullback (Spec.algebraMap R K)).map f) ∧
    IsIso ((Over.pullback (Spec.algebraMap R (IsLocalRing.ResidueField R))).map f)

/-- Isomorphisms on all residue-field fibres detect an isomorphism from a
flat, locally finitely presented scheme to a locally finite-type scheme. -/
theorem isIso_of_residueField_fibres
    {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : B, IsIso ((Over.pullback (B.fromSpecResidueField s)).map f)) :
    IsIso f := by
  have : IsOpenImmersion f.left :=
    isOpenImmersion_of_fiberwise f fun s => by
      let := hf s
      exact inferInstanceAs
        (IsOpenImmersion (((Over.forget _).map
          ((Over.pullback (B.fromSpecResidueField s)).map f))))
  have : Surjective f.left :=
    Langlands.GroupScheme.surjective_of_fiber f fun s => by
      let := hf s
      exact inferInstanceAs
        (Surjective (((Over.forget _).map
          ((Over.pullback (B.fromSpecResidueField s)).map f))))
  have : IsIso f.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget B).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget B)

private theorem isIso_pullback_of_factor
    {B B' B'' : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    (b : B' ⟶ B) (c : B'' ⟶ B')
    (hf : IsIso ((Over.pullback b).map f)) :
    IsIso ((Over.pullback (c ≫ b)).map f) := by
  let := hf
  exact (NatIso.isIso_map_iff (Over.pullbackComp c b) f).mpr
    (inferInstanceAs (IsIso ((Over.pullback c).map ((Over.pullback b).map f))))

/-- Over a DVR, every field-valued pullback is an isomorphism as soon as the
generic and closed fibres of the specified map are isomorphisms. -/
theorem isIso_field_pullback_of_generic_special
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (hf : IsGenericSpecialFibreIsomorphism (K := K) f)
    (L : Type u) [Field L] (φ : R →+* L) :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map f) := by
  by_cases hφ : Function.Injective φ
  · let ψ : K →+* L := IsFractionRing.lift hφ
    have hfac : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.algebraMap R K =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact IsFractionRing.lift_algebraMap hφ r
    rw [← hfac]
    exact isIso_pullback_of_factor f _ _ hf.1
  · have hker : RingHom.ker φ ≠ ⊥ :=
      fun h => hφ ((RingHom.injective_iff_ker_eq_bot φ).mpr h)
    have hmax : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ).isMaximal hker)
    let : IsLocalHom φ := ⟨fun r hr => by
      by_contra hunit
      have hzero : φ r = 0 := by
        apply (show r ∈ RingHom.ker φ from hmax.symm ▸ hunit)
      exact (isUnit_iff_ne_zero.mp hr) hzero⟩
    let ψ : IsLocalRing.ResidueField R →+* L := IsLocalRing.ResidueField.lift φ
    have hfac : Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.algebraMap R (IsLocalRing.ResidueField R) =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp]
      congr 1
    rw [← hfac]
    exact isIso_pullback_of_factor f _ _ hf.2

/-- A morphism from a flat locally finitely presented scheme over a DVR
to a locally finite-type scheme is an isomorphism if its generic and closed
fibres are isomorphisms. -/
theorem isIso_of_generic_special
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : IsGenericSpecialFibreIsomorphism (K := K) f) :
    IsIso f := by
  apply isIso_of_residueField_fibres f
  intro s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  have h := isIso_field_pullback_of_generic_special f hf
    ((Spec (CommRingCat.of R)).residueField s) φ.hom
  rwa [show Spec.map (CommRingCat.ofHom φ.hom) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s from Spec.map_preimage _] at h

end Langlands.AlgebraicGeometry
