import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The affine scheme relation of a ring étale equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry

namespace RingEtaleEquivalenceRelation

/-- The global-sections description of maps from an arbitrary scheme to an
affine scheme. -/
noncomputable def schemePointEquiv (X : Scheme.{u}) (D : CommRingCat.{u}) :
    (X ⟶ Spec D) ≃ (D ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op D)).symm.trans (CategoryTheory.opEquiv _ _)

lemma schemePointEquiv_comp {X : Scheme.{u}} {D F : CommRingCat.{u}}
    (r : X ⟶ Spec F) (f : D ⟶ F) :
    schemePointEquiv X D (r ≫ Spec.map f) = f ≫ schemePointEquiv X F r := by
  exact congrArg Quiver.Hom.unop
    (ΓSpec.adjunction.homEquiv_naturality_right_symm r f.op)

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
  {t : B →+* C}

/-- The actual affine scheme relation represented by the given ring relation.
The source and target maps are the spectrum maps of the two original ring maps. -/
noncomputable def toScheme (hE : RingEtaleEquivalenceRelation t) :
    EtaleEquivalenceRelation.{u} where
  U := Spec (CommRingCat.of B)
  R := Spec (CommRingCat.of C)
  t := Spec.map (CommRingCat.ofHom t)
  s := Spec.map (CommRingCat.ofHom (algebraMap B C))
  mono_lift := by
    constructor
    intro X r r' h
    have ht : r ≫ Spec.map (CommRingCat.ofHom t) =
        r' ≫ Spec.map (CommRingCat.ofHom t) := by
      simpa only [Category.assoc, prod.lift_fst] using congrArg
        (fun f => f ≫ prod.fst) h
    have hs : r ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
        r' ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      simpa only [Category.assoc, prod.lift_snd] using congrArg
        (fun f => f ≫ prod.snd) h
    apply (schemePointEquiv X (CommRingCat.of C)).injective
    apply CommRingCat.hom_ext
    apply hE.hom_ext
    · change (CommRingCat.ofHom t ≫ schemePointEquiv X (CommRingCat.of C) r).hom =
        (CommRingCat.ofHom t ≫ schemePointEquiv X (CommRingCat.of C) r').hom
      rw [← schemePointEquiv_comp, ← schemePointEquiv_comp, ht]
    · change (CommRingCat.ofHom (algebraMap B C) ≫
          schemePointEquiv X (CommRingCat.of C) r).hom =
        (CommRingCat.ofHom (algebraMap B C) ≫
          schemePointEquiv X (CommRingCat.of C) r').hom
      rw [← schemePointEquiv_comp, ← schemePointEquiv_comp, hs]
  refl X a := by
    obtain ⟨φ, ht, hs⟩ :=
      hE.refl Γ(X, ⊤) (schemePointEquiv X (CommRingCat.of B) a).hom
    refine ⟨(schemePointEquiv X (CommRingCat.of C)).symm (CommRingCat.ofHom φ), ?_, ?_⟩
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext ht
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext hs
  symm X r := by
    obtain ⟨φ, ht, hs⟩ :=
      hE.symm Γ(X, ⊤) (schemePointEquiv X (CommRingCat.of C) r).hom
    refine ⟨(schemePointEquiv X (CommRingCat.of C)).symm (CommRingCat.ofHom φ), ?_, ?_⟩
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext ht
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext hs
  trans X r r' h := by
    have hc : (schemePointEquiv X (CommRingCat.of C) r).hom.comp (algebraMap B C) =
        (schemePointEquiv X (CommRingCat.of C) r').hom.comp t := by
      change (CommRingCat.ofHom (algebraMap B C) ≫
          schemePointEquiv X (CommRingCat.of C) r).hom =
        (CommRingCat.ofHom t ≫ schemePointEquiv X (CommRingCat.of C) r').hom
      rw [← schemePointEquiv_comp, ← schemePointEquiv_comp, h]
    obtain ⟨φ, ht, hs⟩ := hE.trans Γ(X, ⊤)
      (schemePointEquiv X (CommRingCat.of C) r).hom
      (schemePointEquiv X (CommRingCat.of C) r').hom hc
    refine ⟨(schemePointEquiv X (CommRingCat.of C)).symm (CommRingCat.ofHom φ), ?_, ?_⟩
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext ht
    · apply (schemePointEquiv X (CommRingCat.of B)).injective
      rw [schemePointEquiv_comp, schemePointEquiv_comp, Equiv.apply_symm_apply]
      exact CommRingCat.hom_ext hs
  etale_t := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hE.etale_t
  etale_s := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hE.etale_algebraMap

@[simp]
lemma toScheme_s_apply (hE : RingEtaleEquivalenceRelation t) (p : PrimeSpectrum C) :
    hE.toScheme.s p = PrimeSpectrum.comap (algebraMap B C) p := rfl

@[simp]
lemma toScheme_t_apply (hE : RingEtaleEquivalenceRelation t) (p : PrimeSpectrum C) :
    hE.toScheme.t p = PrimeSpectrum.comap t p := rfl

end RingEtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
