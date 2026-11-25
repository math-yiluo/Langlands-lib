/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Detecting sections on opens by associated-point germs

## References

* Stacks Project, Tag 0311, with associated-prime localization, Tag 0310
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem eq_zero_of_Spec_associated_germs
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (s : Γ(Spec (.of R), ⊤))
    (hs : ∀ q : Spec (.of R), q.asIdeal ∈ associatedPrimes R R →
      ((Spec (.of R)).presheaf.Γgerm q).hom s = 0) : s = 0 := by
  let r : R := (ΓSpecIso (.of R)).hom s
  have heq : (ΓSpecIso (.of R)).inv r = s := Iso.hom_inv_id_apply _ s
  have hr : r = 0 := by
    apply (Module.injective_pi_localization_associatedPrimes R R).2
    intro p
    let q : Spec (.of R) := ⟨p.1, p.2.isPrime⟩
    let : Algebra R ((Spec (.of R)).presheaf.stalk q) :=
      StructureSheaf.stalkAlgebra R q
    let : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk q) p.1 :=
      StructureSheaf.IsLocalization.to_stalk R q
    have hz : algebraMap R ((Spec (.of R)).presheaf.stalk q) r = 0 := by
      change ((Spec (.of R)).presheaf.Γgerm q).hom ((ΓSpecIso (.of R)).inv r) = 0
      rw [heq]
      exact hs q p.2
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.1.primeCompl _ r).mp hz
    exact ⟨t, t.2, by simpa only [smul_eq_mul] using ht⟩
  rw [← heq, hr]
  exact map_zero _

/-- On an open of a Noetherian affine scheme, associated-point germs detect zero sections. -/
theorem eq_zero_of_associated_germs
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (s : Γ(V.toScheme, ⊤))
    (hs : ∀ (q : Spec (.of R)) (hq : q ∈ V),
      q.asIdeal ∈ associatedPrimes R R →
        (V.toScheme.presheaf.Γgerm ⟨q, hq⟩).hom s = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext V.toScheme.sheaf ⊤ s 0
  intro x hx
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.2 V.isOpen
  let e := basicOpenIsoSpecAway (R := .of R) g
  let f : Spec (.of (Localization.Away g)) ⟶ V.toScheme :=
    e.inv ≫ (Spec (.of R)).homOfLE hgV
  have hcomp : f ≫ V.ι = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    change (e.inv ≫ (Spec (.of R)).homOfLE hgV) ≫ V.ι = _
    rw [Category.assoc, homOfLE_ι]
    rw [← basicOpenIsoSpecAway_hom_SpecMap g]
    simp only [e, Iso.inv_hom_id_assoc]
  have ht : f.appTop s = 0 := by
    apply eq_zero_of_Spec_associated_germs (Localization.Away g)
    intro q hq
    have hc : q.asIdeal.comap (algebraMap R (Localization.Away g)) ∈
        associatedPrimes R R := by
      apply (open Module.associatedPrimes in
        comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
          (Submonoid.powers g) (Algebra.linearMap R (Localization.Away g)) q.asIdeal hq)
      exact Ideal.fg_of_isNoetherianRing _
    have hval : (f q).val = q.comap (algebraMap R (Localization.Away g)) :=
      congrArg (fun k : Spec (.of (Localization.Away g)) ⟶ Spec (.of R) ↦ k q) hcomp
    have hz : (V.toScheme.presheaf.Γgerm (f q)).hom s = 0 := by
      apply hs (f q).val (f q).property
      rw [hval]
      exact hc
    have h := f.germ_stalkMap_apply ⊤ q trivial s
    change (f.stalkMap q).hom ((V.toScheme.presheaf.Γgerm (f q)).hom s) =
      ((Spec (.of (Localization.Away g))).presheaf.Γgerm q).hom (f.appTop s) at h
    rw [hz, map_zero] at h
    exact h.symm
  let q : Spec (.of (Localization.Away g)) := e.hom ⟨x.val, hxg⟩
  have hfx : f q = x := by
    dsimp only [f, q]
    rw [Scheme.Hom.comp_apply]
    have he : e.inv (e.hom ⟨x.val, hxg⟩) = ⟨x.val, hxg⟩ := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [he]
    apply Subtype.ext
    exact Scheme.homOfLE_apply hgV ⟨x.val, hxg⟩
  have hz : (V.toScheme.presheaf.Γgerm (f q)).hom s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (f.stalkMap q)).1
    have h := f.germ_stalkMap_apply ⊤ q trivial s
    change (f.stalkMap q).hom ((V.toScheme.presheaf.Γgerm (f q)).hom s) =
      ((Spec (.of (Localization.Away g))).presheaf.Γgerm q).hom (f.appTop s) at h
    simpa only [ht, map_zero] using h
  rw [hfx] at hz
  change (V.toScheme.presheaf.germ ⊤ x hx).hom s =
    (V.toScheme.presheaf.germ ⊤ x hx).hom 0
  simpa only [TopCat.Presheaf.Γgerm, map_zero] using hz

end AlgebraicGeometry.Scheme
