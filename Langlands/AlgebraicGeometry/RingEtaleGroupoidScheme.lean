import Langlands.AlgebraicGeometry.RingEtaleGroupoid
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationScheme
import Langlands.AlgebraicGeometry.FiniteEtale.AffineQuotientCoconeProof

/-! # Affine étale groupoids in ring form and étale equivalence relations

A `RingEtaleGroupoid t` with `t : B →+* C` gives the étale equivalence relation
`Spec C ⇉ Spec B`, and an étale equivalence relation with affine `U` and `R` gives a
`RingEtaleGroupoid` on its rings of global sections.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace RingEtaleGroupoid

open RingEtaleEquivalenceRelation

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] {t : B →+* C}

/-- The étale equivalence relation `Spec C ⇉ Spec B` of a ring étale groupoid. The source
and target maps are the spectrum maps of `algebraMap B C` and `t`. -/
noncomputable def toScheme (hE : RingEtaleGroupoid t) : EtaleEquivalenceRelation.{u} where
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
lemma toScheme_U (hE : RingEtaleGroupoid t) : hE.toScheme.U = Spec (CommRingCat.of B) := rfl

@[simp]
lemma toScheme_R (hE : RingEtaleGroupoid t) : hE.toScheme.R = Spec (CommRingCat.of C) := rfl

@[simp]
lemma toScheme_t (hE : RingEtaleGroupoid t) :
    hE.toScheme.t = Spec.map (CommRingCat.ofHom t) := rfl

@[simp]
lemma toScheme_s (hE : RingEtaleGroupoid t) :
    hE.toScheme.s = Spec.map (CommRingCat.ofHom (algebraMap B C)) := rfl

end RingEtaleGroupoid

namespace EtaleEquivalenceRelation

open FiniteEtale

/-- The rings of global sections of an étale equivalence relation with affine `U` and `R`
form a ring étale groupoid. Uniqueness of ring maps out of `Γ(R, ⊤)` comes from the
monomorphism `j = (t, s)`. -/
theorem ringEtaleGroupoid (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsAffine E.R] :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    RingEtaleGroupoid E.t.appTop.hom := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  refine
    { hom_ext := ?_
      refl := ?_
      symm := ?_
      trans := ?_
      etale_algebraMap := ?_
      etale_t := ?_ }
  · intro T _ φ ψ ht hs
    let K := CommRingCat.of T
    let r := (affinePointEquiv E.R K).symm (CommRingCat.ofHom φ)
    let r' := (affinePointEquiv E.R K).symm (CommRingCat.ofHom ψ)
    have hr : affinePointEquiv E.R K r = CommRingCat.ofHom φ := Equiv.apply_symm_apply _ _
    have hr' : affinePointEquiv E.R K r' = CommRingCat.ofHom ψ := Equiv.apply_symm_apply _ _
    have htr : r ≫ E.t = r' ≫ E.t := by
      apply (affinePointEquiv E.U K).injective
      rw [affinePointEquiv_comp, affinePointEquiv_comp, hr, hr']
      exact CommRingCat.hom_ext ht
    have hsr : r ≫ E.s = r' ≫ E.s := by
      apply (affinePointEquiv E.U K).injective
      rw [affinePointEquiv_comp, affinePointEquiv_comp, hr, hr']
      exact CommRingCat.hom_ext hs
    have : Mono (prod.lift E.t E.s) := E.mono_lift
    have hrr : r = r' := by
      rw [← cancel_mono (prod.lift E.t E.s)]
      apply prod.hom_ext
      · simpa using htr
      · simpa using hsr
    have := congrArg (affinePointEquiv E.R K) hrr
    rw [hr, hr'] at this
    exact congrArg CommRingCat.Hom.hom this
  · intro T _ a
    let K := CommRingCat.of T
    obtain ⟨r, ht, hs⟩ :=
      E.refl (Spec K) ((affinePointEquiv E.U K).symm (CommRingCat.ofHom a))
    refine ⟨(affinePointEquiv E.R K r).hom, ?_, ?_⟩
    · change (E.t.appTop ≫ affinePointEquiv E.R K r).hom = a
      rw [← affinePointEquiv_comp, ht, Equiv.apply_symm_apply]
      rfl
    · change (E.s.appTop ≫ affinePointEquiv E.R K r).hom = a
      rw [← affinePointEquiv_comp, hs, Equiv.apply_symm_apply]
      rfl
  · intro T _ φ
    let K := CommRingCat.of T
    let r := (affinePointEquiv E.R K).symm (CommRingCat.ofHom φ)
    have hr : affinePointEquiv E.R K r = CommRingCat.ofHom φ :=
      Equiv.apply_symm_apply _ _
    obtain ⟨r', ht, hs⟩ := E.symm (Spec K) r
    refine ⟨(affinePointEquiv E.R K r').hom, ?_, ?_⟩
    · change (E.t.appTop ≫ affinePointEquiv E.R K r').hom =
        φ.comp E.s.appTop.hom
      rw [← affinePointEquiv_comp, ht, affinePointEquiv_comp, hr]
      rfl
    · change (E.s.appTop ≫ affinePointEquiv E.R K r').hom =
        φ.comp E.t.appTop.hom
      rw [← affinePointEquiv_comp, hs, affinePointEquiv_comp, hr]
      rfl
  · intro T _ φ ψ h
    let K := CommRingCat.of T
    let r := (affinePointEquiv E.R K).symm (CommRingCat.ofHom φ)
    let r' := (affinePointEquiv E.R K).symm (CommRingCat.ofHom ψ)
    have hr : affinePointEquiv E.R K r = CommRingCat.ofHom φ :=
      Equiv.apply_symm_apply _ _
    have hr' : affinePointEquiv E.R K r' = CommRingCat.ofHom ψ :=
      Equiv.apply_symm_apply _ _
    have hcomp : r ≫ E.s = r' ≫ E.t := by
      apply (affinePointEquiv E.U K).injective
      rw [affinePointEquiv_comp, affinePointEquiv_comp, hr, hr']
      exact congrArg CommRingCat.ofHom h
    obtain ⟨r'', ht, hs⟩ := E.trans (Spec K) r r' hcomp
    refine ⟨(affinePointEquiv E.R K r'').hom, ?_, ?_⟩
    · change (E.t.appTop ≫ affinePointEquiv E.R K r'').hom =
        φ.comp E.t.appTop.hom
      rw [← affinePointEquiv_comp, ht, affinePointEquiv_comp, hr]
      rfl
    · change (E.s.appTop ≫ affinePointEquiv E.R K r'').hom =
        ψ.comp E.s.appTop.hom
      rw [← affinePointEquiv_comp, hs, affinePointEquiv_comp, hr']
      rfl
  · exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp E.etale_s
  · exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp E.etale_t

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
