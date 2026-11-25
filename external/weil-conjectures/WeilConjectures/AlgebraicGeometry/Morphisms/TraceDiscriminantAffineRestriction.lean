/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Discriminant ideals under affine restriction

## References

* Stacks Project, Tag 0BVH, construction before Lemma 49.3.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem discr_span_eq_same_index
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Module.Basis ι A B) :
    Ideal.span {Algebra.discr A b} = Ideal.span {Algebra.discr A c} := by
  have hd := Algebra.discr_of_matrix_vecMul b (b.toMatrix c)
  rw [Module.Basis.toMatrix_map_vecMul] at hd
  have hu : IsUnit (b.toMatrix c).det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix c b]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl A B) c b
  rw [hd, Ideal.span_singleton_mul_left_unit (hu.pow 2)]

private theorem discr_span_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (n m : ℕ) (b : Module.Basis (Fin n) A B) (c : Module.Basis (Fin m) A B) :
    Ideal.span {Algebra.discr A b} = Ideal.span {Algebra.discr A c} := by
  cases subsingleton_or_nontrivial A
  · exact Subsingleton.elim _ _
  · let e := b.indexEquiv c
    have hr : Algebra.discr A (b.reindex e) = Algebra.discr A b := by
      simpa only [Module.Basis.coe_reindex] using Algebra.discr_reindex A b e
    rw [← hr]
    exact discr_span_eq_same_index (b.reindex e) c

private theorem discr_span_map_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (r : Γ(Y, U.1)),
      letI := (f.app (Y.basicOpen r)).hom.toAlgebra
      ∃ c : Module.Basis (Fin n) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r),
        (Ideal.span {Algebra.discr Γ(Y, U.1) b}).map
          (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
            Ideal.span {Algebra.discr Γ(Y, Y.basicOpen r) c} := by
  let := (f.app U.1).hom.toAlgebra
  intro n b r
  let A := Γ(Y, U.1)
  let B := Γ(X, f ⁻¹ᵁ U.1)
  let Ar := Γ(Y, Y.basicOpen r)
  let Br := Γ(X, f ⁻¹ᵁ Y.basicOpen r)
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra A Ar :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Ar := U.2.isLocalization_basicOpen r
  let : Algebra B Br := (X.presheaf.map
    (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away (algebraMap A B r) Br :=
    (U.2.preimage f).isLocalization_of_eq_basicOpen (algebraMap A B r) _
      (Scheme.preimage_basicOpen f r)
  let : Algebra A Br := ((algebraMap B Br).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Br := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Ar Br := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (f.naturality (homOfLE (Y.basicOpen_le r)).op)) a).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers r)) Br := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap A B r) Br)
  let c := b.localizationLocalization Ar (.powers r) Br
  refine ⟨c, ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {algebraMap A Ar (Algebra.discr A b)} = Ideal.span {Algebra.discr Ar c}
  exact congrArg (fun d : Ar ↦ Ideal.span {d})
    (Algebra.discr_localizationLocalization A (.powers r) Br b).symm

private theorem discr_span_map_eq_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens)
    (W : Y.Opens) (h : W ≤ U.1) (r : Γ(Y, U.1)) (e : W = Y.basicOpen r) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app W).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)),
      ∃ c : Module.Basis (Fin n) Γ(Y, W) Γ(X, f ⁻¹ᵁ W),
        (Ideal.span {Algebra.discr Γ(Y, U.1) b}).map
          (Y.presheaf.map (homOfLE h).op).hom = Ideal.span {Algebra.discr Γ(Y, W) c} := by
  subst W
  exact fun n b ↦ discr_span_map_basicOpen f U n b r

/-- Restriction between two free affine charts preserves the discriminant ideal. -/
theorem trace_discriminant_span_map_affine_restriction
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app V.1).hom.toAlgebra
    ∀ (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (c : Module.Basis (Fin m) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)),
      (Ideal.span {Algebra.discr Γ(Y, U.1) b}).map
        (Y.presheaf.map (homOfLE h).op).hom =
          Ideal.span {Algebra.discr Γ(Y, V.1) c} := by
  let := (f.app U.1).hom.toAlgebra
  let := (f.app V.1).hom.toAlgebra
  intro n m b c
  rw [V.2.ideal_ext_iff]
  intro y hyV
  obtain ⟨r, s, hrs, hyr⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨h hyV, hyV⟩
  let W := Y.basicOpen r
  have hWU : W ≤ U.1 := Y.basicOpen_le r
  have hWV : W ≤ V.1 := hrs.trans_le (Y.basicOpen_le s)
  let := (f.app W).hom.toAlgebra
  obtain ⟨d, hd⟩ := discr_span_map_eq_basicOpen f U W hWU r rfl n b
  obtain ⟨d', hd'⟩ := discr_span_map_eq_basicOpen f V W hWV s hrs m c
  have he : (Ideal.span {Algebra.discr Γ(Y, U.1) b}).map
      (Y.presheaf.map (homOfLE hWU).op).hom =
        (Ideal.span {Algebra.discr Γ(Y, V.1) c}).map
          (Y.presheaf.map (homOfLE hWV).op).hom := by
    rw [hd, hd']
    exact discr_span_eq n m d d'
  have hg := congrArg (Ideal.map (Y.presheaf.germ W y hyr).hom) he
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res] using hg

end AlgebraicGeometry.Scheme
