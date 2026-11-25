/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.Flat.Localization

/-!
# The target flat locus of a finite morphism

## References

* Stacks Project, Tag 00RC (openness of flatness) and Tag 01WM (finite morphisms are closed)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem isOpen_flat_stalks_spec
    {R S : CommRingCat.{u}} (f : R ⟶ S) [IsNoetherianRing R]
    [LocallyOfFiniteType (Spec.map f)] :
    IsOpen {z : Spec S | ((Spec.map f).stalkMap z).hom.Flat} := by
  have hf : f.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  algebraize [f.hom]
  have : Algebra.FiniteType R S := hf
  have heq (z : PrimeSpectrum S) :
      ((Spec.map f).stalkMap z).hom.Flat ↔ Module.Flat R (Localization.AtPrime z.asIdeal) := by
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso f z)]
    algebraize [Localization.localRingHom (z.comap f.hom).asIdeal z.asIdeal f.hom rfl]
    have : IsScalarTower R (Localization.AtPrime (z.comap f.hom).asIdeal)
        (Localization.AtPrime z.asIdeal) :=
      .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
    change Module.Flat (Localization.AtPrime (z.comap f.hom).asIdeal)
      (Localization.AtPrime z.asIdeal) ↔ _
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime (z.comap f.hom).asIdeal) (z.comap f.hom).asIdeal.primeCompl
      (Localization.AtPrime z.asIdeal)
  change IsOpen {z : PrimeSpectrum S | ((Spec.map f).stalkMap z).hom.Flat}
  simpa only [heq] using (PrimeSpectrum.isOpen_setOf_flat_localization (R := R) (S := S))

private theorem isOpen_flat_stalks_affine
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffine E] [IsAffine L]
    [IsLocallyNoetherian L] [LocallyOfFiniteType p] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  have : IsNoetherianRing Γ(L, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top L⟩
  let p' := E.isoSpec.inv ≫ p ≫ L.isoSpec.hom
  have h' : IsOpen {z : Spec Γ(E, ⊤) | (p'.stalkMap z).hom.Flat} := by
    have : LocallyOfFiniteType (Spec.map (Spec.preimage p')) := by
      rw [Spec.map_preimage]
      dsimp [p']
      infer_instance
    rw [← Spec.map_preimage p']
    exact isOpen_flat_stalks_spec _
  convert h'.preimage E.isoSpec.hom.continuous using 1
  ext z
  change (p.stalkMap z).hom.Flat ↔
    ((E.isoSpec.inv ≫ p ≫ L.isoSpec.hom).stalkMap (E.isoSpec.hom z)).hom.Flat
  rw [Hom.stalkMap_comp, Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso]
  have he : E.isoSpec.inv (E.isoSpec.hom z) = z := by
    rw [← Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [he]

private theorem isOpen_finite_flat_source_locus
    {E L : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [IsLocallyNoetherian L] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨U, hU, hpz, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    L.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (p z))
  let V : L.Opens := U
  have hV : IsAffineOpen V := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (p ⁻¹ᵁ V).toScheme := hV.preimage p
  have hopen := isOpen_flat_stalks_affine (p ∣_ V)
  refine ⟨(p ⁻¹ᵁ V).ι '' {w | ((p ∣_ V).stalkMap w).hom.Flat}, ?_,
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p V w)).mp hw
  · refine ⟨⟨z, hpz⟩, ?_, rfl⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p V ⟨z, hpz⟩)).mpr hz

/-- The points over which every source stalk is flat form an open subset. -/
theorem isOpen_setOf_finite_flat_stalks
    {E L : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [IsLocallyNoetherian L] :
    IsOpen {y : L | ∀ z : E, p z = y → (p.stalkMap z).hom.Flat} := by
  have hopen := isOpen_finite_flat_source_locus p
  have hclosed := p.isClosedMap _ hopen.isClosed_compl
  convert hclosed.isOpen_compl using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image]
  constructor
  · intro hy ⟨z, hz, hzy⟩
    exact hz (hy z hzy)
  · intro hy z hzy
    by_contra hz
    exact hy ⟨z, hz, hzy⟩

end AlgebraicGeometry.Scheme
