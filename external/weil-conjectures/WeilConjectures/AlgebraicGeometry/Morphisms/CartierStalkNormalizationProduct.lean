/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents
import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup
import WeilConjectures.AlgebraicGeometry.Morphisms.CartierStalkPuncturedComplement
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationStalkFieldCoproduct

/-! # Integral-closure product after localizing a Cartier torsor

## References

* Stacks Project, Tags 0307, 09EB, 03SF and 03QR
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Product model of the entire normalization over the Cartier DVR stalk. -/
theorem cartier_stalk_normalization_product
    {N U P : Scheme.{u}} [IsLocallyNoetherian N]
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (V : N.Opens) (κ : V.toScheme ⟶ U) (p : P ⟶ V.toScheme) [IsFinite p]
    (r : P ⟶ W.P) (hpb : IsPullback r p W.π κ) :
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (hdom : IsDomain (N.presheaf.stalk (j η))),
      letI := hdom
      IsDiscreteValuationRing (N.presheaf.stalk (j η)) →
      let R := N.presheaf.stalk (j η)
      ∃ (n : ℕ) (E : Fin n → Type u) (hE : ∀ i, Field (E i))
        (aE : ∀ i, Algebra (FractionRing R) (E i)),
        letI := hE
        letI := aE
        letI (i : Fin n) : Algebra R (E i) :=
          ((algebraMap (FractionRing R) (E i)).comp
            (algebraMap R (FractionRing R))).toAlgebra
        ∃ (T : Fin n → Subgroup G) (act : ∀ i, MulSemiringAction (T i) (E i)),
          letI := act
          (∀ i, IsGaloisGroup (T i) (FractionRing R) (E i)) ∧
          (∀ i, Module.Finite R (integralClosure R (E i))) ∧
          ∃ e : pullback a.fromNormalization (N.fromSpecStalk (j η)) ≅
              ∐ fun i : Fin n ↦ Spec (CommRingCat.of (integralClosure R (E i))),
            e.hom ≫ Sigma.desc (fun i : Fin n ↦
              Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R (E i))))) =
              pullback.snd a.fromNormalization (N.fromSpecStalk (j η)) := by
  classical
  intro a hp ha D j hD hj hV η hη hdom
  let := hdom
  intro hR
  let := hR
  let R := N.presheaf.stalk (j η)
  let K := FractionRing R
  obtain ⟨t, ht⟩ := cartier_stalk_punctured_complement V D j hD hj hV η hη
  obtain ⟨Q, ρ, hQ⟩ := GaloisCover.exists_baseChange G W (t ≫ κ)
  have hQt := hQ.of_right' hpb
  have hs := hQt.paste_vert ht
  let eQ : pullback a (N.fromSpecStalk (j η)) ≅ Q.P := hs.isoPullback.symm
  have heQ : eQ.hom ≫ Q.π ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) =
        pullback.snd a (N.fromSpecStalk (j η)) := hs.isoPullback_inv_snd
  obtain ⟨n, E, hE, aE, hf, eF, heF⟩ := field_torsor_galois_components K G Q
  let := hE
  let := aE
  let (i : Fin n) : Algebra R (E i) :=
    ((algebraMap K (E i)).comp (algebraMap R K)).toAlgebra
  have he : (eQ ≪≫ eF).hom ≫ Sigma.desc (fun i : Fin n ↦
      Spec.map (CommRingCat.ofHom (algebraMap R (E i)))) =
        pullback.snd a (N.fromSpecStalk (j η)) := by
    have hmap : Sigma.desc (fun i : Fin n ↦
        Spec.map (CommRingCat.ofHom (algebraMap R (E i)))) =
        Sigma.desc (fun i : Fin n ↦
          Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      ext i
      simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, ← Spec.map_comp]
      rfl
    rw [hmap]
    rw [Iso.trans_hom, Category.assoc, ← Category.assoc eF.hom, heF]
    exact heQ
  obtain ⟨e, he⟩ := normalization_stalk_field_coproduct a (j η) n E (eQ ≪≫ eF) he
  have hc : ∀ i : Fin n, ∃ (H : Subgroup G) (act : MulSemiringAction H (E i)),
      let := act
      IsGaloisGroup H K (E i) := by
    intro i
    let jE : Spec (CommRingCat.of (E i)) ⟶ Q.P :=
      Sigma.ι (fun i : Fin n ↦ Spec (CommRingCat.of (E i))) i ≫ eF.inv
    have hjE : jE ≫ Q.π = Spec.map (CommRingCat.ofHom (algebraMap K (E i))) := by
      rw [← heF]
      simp [jE]
    obtain ⟨hg, H, ⟨b⟩⟩ := field_torsor_component_galois_group K G Q (E i) jE hjE
    let := hg
    let act := MulSemiringAction.compHom (E i) b.symm.toMonoidHom
    let := act
    exact ⟨H, act, IsGaloisGroup.of_mulEquiv b.symm (fun _ _ ↦ rfl)⟩
  choose T act hg using hc
  let := act
  refine ⟨n, E, hE, aE, T, act, hg, ?_, e, he⟩
  intro i
  let A := fun i : Fin n ↦ integralClosure R (E i)
  let C := fun i : Fin n ↦ CommRingCat.of (A i)
  have hι : IsFinite (Sigma.ι (fun i ↦ Spec (C i)) i) := by
    let C' : ULift.{u} (Fin n) → CommRingCat.{u} := fun j ↦ C j.down
    let b := Sigma.reindex Equiv.ulift (fun i ↦ Spec (C i))
    have hsurj : Function.Surjective (Pi.evalRingHom (fun j ↦ C' j) (ULift.up i)) :=
      Function.surjective_eval _
    have hfin : IsFinite (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun j ↦ C' j) (ULift.up i)))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.Finite.of_surjective _ hsurj)
    have hcomp : IsFinite (Sigma.ι (fun j ↦ Spec (C' j)) (ULift.up i) ≫
        sigmaSpec C') := by
      rw [ι_sigmaSpec]
      exact hfin
    have : IsFinite (Sigma.ι (fun j ↦ Spec (C' j)) (ULift.up i)) :=
      (MorphismProperty.cancel_right_of_respectsIso @IsFinite
        (Sigma.ι (fun j ↦ Spec (C' j)) (ULift.up i)) (sigmaSpec C')).mp hcomp
    have hcomp : IsFinite (Sigma.ι (fun j ↦ Spec (C' j)) (ULift.up i) ≫ b.hom) :=
      inferInstance
    change IsFinite (Sigma.ι ((fun i ↦ Spec (C i)) ∘ Equiv.ulift)
      (ULift.up i) ≫ (Sigma.reindex Equiv.ulift (fun i ↦ Spec (C i))).hom) at hcomp
    rw [Sigma.ι_reindex_hom] at hcomp
    exact hcomp
  let := hι
  let := ha
  have hm : IsFinite (Sigma.ι (fun i ↦ Spec (C i)) i ≫ e.inv ≫
      pullback.snd a.fromNormalization (N.fromSpecStalk (j η))) := inferInstance
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R (A i))) =
      Sigma.ι (fun i ↦ Spec (C i)) i ≫ e.inv ≫
        pullback.snd a.fromNormalization (N.fromSpecStalk (j η)) := by
    rw [← he]
    change _ = Sigma.ι (fun i ↦ Spec (C i)) i ≫ e.inv ≫ e.hom ≫
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap R (A i))))
    simp only [Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (A i)))) :=
    hmap.symm ▸ hm
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)

end AlgebraicGeometry.Scheme
