/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.FieldTheory.Galois.Basic

import Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup

/-! # Galois field components of a finite torsor

## References

* Stacks Project, Tags 03SF and 03QR
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The field components of a finite group torsor are Galois of degree dividing the group order.
-/
theorem field_torsor_galois_components
    (K : Type u) [Field K]
    (G : Type (u + 1)) [Group G] [Finite G] (T : GaloisCover G (Spec (CommRingCat.of K))) :
    ∃ (r : ℕ) (E : Fin r → Type u) (hE : ∀ i, Field (E i))
      (aE : ∀ i, Algebra K (E i)),
      letI := hE
      letI := aE
      (∀ i, FiniteDimensional K (E i) ∧ IsGalois K (E i) ∧
        Module.finrank K (E i) ∣ Nat.card G) ∧
      ∃ e : T.P ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)),
        e.hom ≫ Sigma.desc (fun i : Fin r ↦
          Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = T.π := by
  classical
  let := T.isFinite
  let := T.etale
  have : IsAffine T.P := isAffine_of_isAffineHom T.π
  let := T.π.ΓAlgebra
  have : Algebra.Etale K Γ(T.P, ⊤) := T.π.etale_ΓAlgebra
  obtain ⟨I, hI, L, hL, aL, a, ha⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K Γ(T.P, ⊤)).mp inferInstance
  let := hI
  let := hL
  let := aL
  let : Fintype I := Fintype.ofFinite I
  let f : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E := fun i ↦ L (f i)
  let hE := fun i ↦ hL (f i)
  let aE := fun i ↦ aL (f i)
  let := hE
  let := aE
  let R := fun i : I ↦ CommRingCat.of (L i)
  let e₀ : T.P ≅ ∐ fun i ↦ Spec (R i) :=
    T.P.isoSpec ≪≫ (Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.op).symm ≪≫
      (asIso (sigmaSpec R)).symm
  have he₀ : e₀.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) = T.π := by
    have hσ : sigmaSpec R ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, L i))) =
        Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) := by
      ext i
      simp only [ι_sigmaSpec_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
      rfl
    rw [← hσ]
    dsimp [e₀]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    change T.P.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom a.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, L i))) = T.π
    rw [← Spec.map_comp]
    have hc : CommRingCat.ofHom (algebraMap K (∀ i, L i)) ≫
        CommRingCat.ofHom a.symm.toRingHom =
        CommRingCat.ofHom (algebraMap K Γ(T.P, ⊤)) := by
      ext x
      exact a.symm.commutes x
    rw [hc, Scheme.isoSpec_hom]
    change T.P.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      T.π.appTop) = T.π
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let e : T.P ≅ ∐ fun i ↦ Spec (CommRingCat.of (E i)) :=
    e₀ ≪≫ (Sigma.reindex f (fun i ↦ Spec (R i))).symm
  have he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = T.π := by
    dsimp [e]
    rw [Category.assoc, ← he₀]
    congr 1
    apply (cancel_epi (Sigma.reindex f (fun i ↦ Spec (R i))).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    ext i
    change _ = Sigma.ι ((fun i ↦ Spec (R i)) ∘ f) i ≫ _
    rw [Sigma.ι_reindex_hom_assoc]
    exact (Sigma.ι_comp_desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) i).trans
        (Sigma.ι_comp_desc (fun i ↦
          Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) (f i)).symm
  refine ⟨Fintype.card I, E, hE, aE, ?_, e, he⟩
  intro i
  have : FiniteDimensional K (E i) := (ha (f i)).1
  let j : Spec (CommRingCat.of (E i)) ⟶ T.P :=
    Sigma.ι (fun i ↦ Spec (CommRingCat.of (E i))) i ≫ e.inv
  have hj : j ≫ T.π = Spec.map (CommRingCat.ofHom (algebraMap K (E i))) := by
    rw [← he]
    simp [j]
  obtain ⟨hg, H, ⟨aH⟩⟩ := field_torsor_component_galois_group K G T (E i) j hj
  let := hg
  refine ⟨inferInstance, hg, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank K (E i), Nat.card_congr aH.toEquiv]
  exact H.card_subgroup_dvd_card

end AlgebraicGeometry.Scheme
