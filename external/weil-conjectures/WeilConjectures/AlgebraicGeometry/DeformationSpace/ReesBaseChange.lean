/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Base change of extended Rees algebras of regular ideals

Let `ψ : C[X₁, …, X_d] ⟶ A` be flat and `I = (ψ(X₁), …, ψ(X_d))`, so that `I` is the ideal of a
section in étale coordinates. For a ring map `a : A ⟶ A'` compatible with a flat
`ψ' : C'[X₁, …, X_d] ⟶ A'` over some `C ⟶ C'`, the extended Rees algebra commutes with base
change: `A'[t, (I A') t⁻¹] = A' ⊗_A A[t, I t⁻¹]`, although `a` need not be flat. This is the
ring-theoretic input of blueprint `prose-09-12` (5). The proof pastes flat base change of
extended Rees algebras with the base change of the origin chart `C[X][t, (X) t⁻¹] ≅ C[t][U]`.

## Main statements

- `Ideal.isPushout_extendedReesAlgebraMap_mvPolynomialOrigin`
- `Ideal.isPushout_extendedReesAlgebraMap_map_mvPolynomialOrigin`
- `Ideal.isPushout_extendedReesAlgebraMap_top`
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial LaurentPolynomial

open scoped AlgebraMonoidAlgebra

namespace Ideal

section Origin

variable {C C' : Type u} [CommRing C] [CommRing C'] (κ : C →+* C') (σ : Type)

lemma map_mvPolynomialOrigin :
    (mvPolynomialOrigin C σ).map (MvPolynomial.map κ) = mvPolynomialOrigin C' σ := by
  rw [mvPolynomialOrigin, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp

lemma map_mvPolynomialOrigin_le :
    (mvPolynomialOrigin C σ).map (MvPolynomial.map κ) ≤ mvPolynomialOrigin C' σ :=
  (map_mvPolynomialOrigin κ σ).le

/-- The chart `C[t][U_i] ≅ C[X_i][t, (X) t⁻¹]` of the deformation space of the origin is natural
in the base ring `C`. -/
lemma extendedReesAlgebraMap_comp_mvPolynomialExtendedReesAlgebraEquiv :
    ((mvPolynomialOrigin C σ).extendedReesAlgebraMap (MvPolynomial.map κ)
      (mvPolynomialOrigin C' σ) (map_mvPolynomialOrigin_le κ σ)).comp
        (mvPolynomialExtendedReesAlgebraEquiv C σ).toRingHom =
      (mvPolynomialExtendedReesAlgebraEquiv C' σ).toRingHom.comp
        (MvPolynomial.map (Polynomial.mapRingHom κ)) := by
  refine MvPolynomial.ringHom_ext (fun p ↦ Subtype.ext ?_) fun i ↦ Subtype.ext ?_
  · change LaurentPolynomial.mapRingHom _ (mvPolynomialToLaurent C σ (MvPolynomial.C p)) =
      mvPolynomialToLaurent C' σ (MvPolynomial.map _ (MvPolynomial.C p))
    rw [MvPolynomial.map_C, mvPolynomialToLaurent_C, mvPolynomialToLaurent_C,
      LaurentPolynomial.mapRingHom_toLaurent, Polynomial.map_map, Polynomial.coe_mapRingHom,
      Polynomial.map_map]
    congr 2
    ext x : 1
    simp
  · change LaurentPolynomial.mapRingHom _ (mvPolynomialToLaurent C σ (MvPolynomial.X i)) =
      mvPolynomialToLaurent C' σ (MvPolynomial.map _ (MvPolynomial.X i))
    rw [MvPolynomial.map_X, mvPolynomialToLaurent_X, mvPolynomialToLaurent_X, map_mul,
      LaurentPolynomial.mapRingHom_C, LaurentPolynomial.mapRingHom_T, MvPolynomial.map_X]

/-- **Base change of the deformation space of the origin.** For any ring map `C ⟶ C'`, the
extended Rees algebra of the origin of `C'[X_i]` is the base change of that of `C[X_i]`:
`C'[X] ⊗_{C[X]} C[X][t, (X) t⁻¹] = C'[X][t, (X) t⁻¹]`. -/
theorem isPushout_extendedReesAlgebraMap_mvPolynomialOrigin :
    IsPushout (CommRingCat.ofHom (MvPolynomial.map κ : MvPolynomial σ C →+* MvPolynomial σ C'))
      (CommRingCat.ofHom
        (algebraMap (MvPolynomial σ C) (mvPolynomialOrigin C σ).extendedReesAlgebra))
      (CommRingCat.ofHom
        (algebraMap (MvPolynomial σ C') (mvPolynomialOrigin C' σ).extendedReesAlgebra))
      (CommRingCat.ofHom ((mvPolynomialOrigin C σ).extendedReesAlgebraMap (MvPolynomial.map κ)
        (mvPolynomialOrigin C' σ) (map_mvPolynomialOrigin_le κ σ))) := by
  let := κ.toAlgebra
  -- `C' ⊗_C C[X_i] = C'[X_i]`
  have t : IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (MvPolynomial.C (σ := σ)))
      (CommRingCat.ofHom (MvPolynomial.C (σ := σ))) (CommRingCat.ofHom (MvPolynomial.map κ)) := by
    let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := C) (S := C')
    exact CommRingCat.isPushout_of_isPushout C C' (MvPolynomial σ C) (MvPolynomial σ C')
  -- `C' ⊗_C C[t][U_i] = C'[t][U_i]`
  have q₁ : IsPushout (CommRingCat.ofHom κ) (CommRingCat.ofHom (Polynomial.C (R := C)))
      (CommRingCat.ofHom (Polynomial.C (R := C')))
      (CommRingCat.ofHom (Polynomial.mapRingHom κ)) := by
    let := Polynomial.algebra (R := C) (A := C')
    exact CommRingCat.isPushout_of_isPushout C C' C[X] C'[X]
  have q₂ : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom κ))
      (CommRingCat.ofHom (MvPolynomial.C (σ := σ) (R := C[X])))
      (CommRingCat.ofHom (MvPolynomial.C (σ := σ) (R := C'[X])))
      (CommRingCat.ofHom (MvPolynomial.map (mapRingHom κ))) := by
    let := (Polynomial.mapRingHom κ).toAlgebra
    let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := C[X]) (S := C'[X])
    exact CommRingCat.isPushout_of_isPushout C[X] C'[X] (MvPolynomial σ C[X])
      (MvPolynomial σ C'[X])
  have q := q₁.paste_vert q₂
  have outer : IsPushout (CommRingCat.ofHom κ)
      (CommRingCat.ofHom (MvPolynomial.C (σ := σ)) ≫ CommRingCat.ofHom
        (algebraMap (MvPolynomial σ C) (mvPolynomialOrigin C σ).extendedReesAlgebra))
      (CommRingCat.ofHom (MvPolynomial.C (σ := σ)) ≫ CommRingCat.ofHom
        (algebraMap (MvPolynomial σ C') (mvPolynomialOrigin C' σ).extendedReesAlgebra))
      (CommRingCat.ofHom ((mvPolynomialOrigin C σ).extendedReesAlgebraMap (MvPolynomial.map κ)
        (mvPolynomialOrigin C' σ) (map_mvPolynomialOrigin_le κ σ))) := by
    refine q.of_iso (Iso.refl _) (Iso.refl _)
      (mvPolynomialExtendedReesAlgebraEquiv C σ).toCommRingCatIso
      (mvPolynomialExtendedReesAlgebraEquiv C' σ).toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · ext1
      refine RingHom.ext fun c ↦ Subtype.ext ?_
      change mvPolynomialToLaurent C σ (MvPolynomial.C (Polynomial.C c)) =
        LaurentPolynomial.C (MvPolynomial.C c)
      rw [mvPolynomialToLaurent_C, Polynomial.map_C, Polynomial.toLaurent_C]
    · ext1
      refine RingHom.ext fun c ↦ Subtype.ext ?_
      change mvPolynomialToLaurent C' σ (MvPolynomial.C (Polynomial.C c)) =
        LaurentPolynomial.C (MvPolynomial.C c)
      rw [mvPolynomialToLaurent_C, Polynomial.map_C, Polynomial.toLaurent_C]
    · ext1
      exact (extendedReesAlgebraMap_comp_mvPolynomialExtendedReesAlgebraEquiv κ σ).symm
  refine IsPushout.of_top outer ?_ t
  ext1
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  exact RingHom.ext fun p ↦
    (extendedReesAlgebraMap_algebraMap _ _ (map_mvPolynomialOrigin_le κ σ) p).symm


end Origin

section Regular

variable {C C' A A' : Type u} [CommRing C] [CommRing C'] [CommRing A] [CommRing A']

lemma extendedReesAlgebraMap_congr {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {J : Ideal S} {φ φ' : R →+* S} (e : φ = φ') (h : I.map φ ≤ J) (h' : I.map φ' ≤ J) :
    I.extendedReesAlgebraMap φ J h = I.extendedReesAlgebraMap φ' J h' := by
  subst e; rfl

/-- **Flat base change of the extended Rees algebra**, as a pushout square of rings: along a
flat `φ : R ⟶ S`, `S[t, (I S) t⁻¹] = S ⊗_R R[t, I t⁻¹]`. -/
lemma isPushout_extendedReesAlgebraMap_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R I.extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap S (I.map φ).extendedReesAlgebra))
      (CommRingCat.ofHom (I.extendedReesAlgebraMap φ (I.map φ) le_rfl)) := by
  let := φ.toAlgebra
  have : Module.Flat R S := hφ
  exact CommRingCat.isPushout_of_isPushout R S I.extendedReesAlgebra
    (I.map (algebraMap R S)).extendedReesAlgebra

variable {σ : Type} (κ : C →+* C') (ψ : MvPolynomial σ C →+* A) (ψ' : MvPolynomial σ C' →+* A')
  (a : A →+* A')

lemma map_map_mvPolynomialOrigin (h : a.comp ψ = ψ'.comp (MvPolynomial.map κ)) :
    ((mvPolynomialOrigin C σ).map ψ).map a = (mvPolynomialOrigin C' σ).map ψ' := by
  rw [Ideal.map_map, h, ← Ideal.map_map, map_mvPolynomialOrigin]

/-- **Base change of the extended Rees algebra of a regular ideal.** Let `ψ : C[X_i] ⟶ A` and
`ψ' : C'[X_i] ⟶ A'` be flat, compatible with `C ⟶ C'` and `a : A ⟶ A'`. Then the extended Rees
algebra of the ideal `I' = (ψ'(X_i))` of `A'` is the base change of that of `I = (ψ(X_i))`:
`A'[t, I' t⁻¹] = A' ⊗_A A[t, I t⁻¹]`. No flatness of `a` is needed. -/
theorem isPushout_extendedReesAlgebraMap_map_mvPolynomialOrigin (hψ : ψ.Flat) (hψ' : ψ'.Flat)
    (h : a.comp ψ = ψ'.comp (MvPolynomial.map κ)) :
    IsPushout (CommRingCat.ofHom a)
      (CommRingCat.ofHom (algebraMap A ((mvPolynomialOrigin C σ).map ψ).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap A' ((mvPolynomialOrigin C' σ).map ψ').extendedReesAlgebra))
      (CommRingCat.ofHom (((mvPolynomialOrigin C σ).map ψ).extendedReesAlgebraMap a _
        (map_map_mvPolynomialOrigin κ ψ ψ' a h).le)) := by
  have S₁ := isPushout_extendedReesAlgebraMap_of_flat ψ hψ (mvPolynomialOrigin C σ)
  have S₂ := isPushout_extendedReesAlgebraMap_mvPolynomialOrigin κ σ
  have S₄ := isPushout_extendedReesAlgebraMap_of_flat ψ' hψ' (mvPolynomialOrigin C' σ)
  have outer := S₂.paste_horiz S₄
  have e₁ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom a =
      CommRingCat.ofHom (MvPolynomial.map κ) ≫ CommRingCat.ofHom ψ' := by
    ext1
    exact h
  have e₂ : CommRingCat.ofHom ((mvPolynomialOrigin C σ).extendedReesAlgebraMap ψ _ le_rfl) ≫
      CommRingCat.ofHom (((mvPolynomialOrigin C σ).map ψ).extendedReesAlgebraMap a _
        (map_map_mvPolynomialOrigin κ ψ ψ' a h).le) =
      CommRingCat.ofHom ((mvPolynomialOrigin C σ).extendedReesAlgebraMap (MvPolynomial.map κ)
        (mvPolynomialOrigin C' σ) (map_mvPolynomialOrigin_le κ σ)) ≫
      CommRingCat.ofHom ((mvPolynomialOrigin C' σ).extendedReesAlgebraMap ψ' _ le_rfl) := by
    ext1
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, extendedReesAlgebraMap_comp,
      extendedReesAlgebraMap_comp]
    exact extendedReesAlgebraMap_congr h _ _
  rw [← e₁, ← e₂] at outer
  refine IsPushout.of_left outer ?_ S₁
  ext1
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  exact RingHom.ext fun x ↦
    (extendedReesAlgebraMap_algebraMap _ _ (map_map_mvPolynomialOrigin κ ψ ψ' a h).le x).symm

/-- The extended Rees algebra of the unit ideal, `A[t, A t⁻¹] = A[t, t⁻¹]`, commutes with
arbitrary base change. -/
theorem isPushout_extendedReesAlgebraMap_top :
    IsPushout (CommRingCat.ofHom a)
      (CommRingCat.ofHom (algebraMap A (⊤ : Ideal A).extendedReesAlgebra))
      (CommRingCat.ofHom (algebraMap A' (⊤ : Ideal A').extendedReesAlgebra))
      (CommRingCat.ofHom ((⊤ : Ideal A).extendedReesAlgebraMap a ⊤ le_top)) := by
  let := a.toAlgebra
  have L := CommRingCat.isPushout_of_isPushout A A' A[T;T⁻¹] A'[T;T⁻¹]
  let e (R : Type u) [CommRing R] : (⊤ : Ideal R).extendedReesAlgebra ≃+* R[T;T⁻¹] :=
    ((Subalgebra.equivOfEq _ _ extendedReesAlgebra_top).trans Subalgebra.topEquiv).toRingEquiv
  refine L.of_iso (Iso.refl _) (Iso.refl _) (e A).toCommRingCatIso.symm
    (e A').toCommRingCatIso.symm ?_ ?_ ?_ ?_
  · rfl
  · ext1
    exact RingHom.ext fun x ↦ Subtype.ext (by simp [e])
  · ext1
    exact RingHom.ext fun x ↦ Subtype.ext (by simp [e])
  · ext1
    refine RingHom.ext fun x ↦ Subtype.ext ?_
    simp [e]
    rfl

end Regular

end Ideal
