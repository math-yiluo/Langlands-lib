/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Algebra.Category.Ring.FinitePresentation

/-! # Etale algebras over a filtered colimit descend to a finite stage

Source: Stacks Project, Algebra, Lemma Tag 00U2 (9), and more-algebra.tex,
proof of Lemma Tag 0A02 (blueprint: lem-weil-pbc-etale-algebra-filtered-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma Tag 00U2 (9), and more-algebra.tex,
proof of Lemma Tag 0A02 (blueprint: lem-weil-pbc-etale-algebra-filtered-colimit-descent).

Proof, following the node:
1. By lem-weil-pbc-etale-algebra-finite-type-model choose a finitely generated
   subring A₀ of A and an etale A₀-algebra B₀ whose base change is B.
2. By lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit, the inclusion
   A₀ → A factors through a stage Aᵢ: finitely many generators and relations
   lift to a common stage of the filtered category.
3. Set Bᵢ = Aᵢ ⊗[A₀] B₀. It is etale over Aᵢ by
   lem-weil-pbc-etale-ring-base-change.
4. By lem-weil-pbc-tensor-cancel-base-change, the further base change of Bᵢ
   to A is A ⊗[A₀] B₀. Compose the inverse of this cancellation isomorphism
   with the model isomorphism from step 1 to obtain the asserted A-algebra isomorphism.
-/
theorem exists_etale_algebra_of_filteredColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (B : Type u) [CommRing B]
    (f : (colimit F : CommRingCat.{u}) ⟶ CommRingCat.of B)
    (hf : Etale (Spec.map f)) :
    ∃ (i : I) (Bi : Type u) (_ : CommRing Bi)
      (g : F.obj i ⟶ CommRingCat.of Bi),
      Etale (Spec.map g) ∧
      let A : Type u := (colimit F : CommRingCat.{u})
      letI : CommRing A := inferInstance
      letI : Algebra (F.obj i) A := (colimit.ι F i).hom.toAlgebra
      letI : Algebra (F.obj i) Bi := g.hom.toAlgebra
      letI : Algebra A B := f.hom.toAlgebra
      Nonempty (B ≃ₐ[A] (A ⊗[F.obj i] Bi)) := by
  classical
  have cancel (R S A B Bi : Type u) [CommRing R] [CommRing S] [CommRing A]
      [CommRing B] [CommRing Bi] [Algebra R S] [Algebra R A] [Algebra R B]
      [Algebra S A] [IsScalarTower R S A] [Algebra S Bi]
      (e : Bi ≃ₐ[S] S ⊗[R] B) :
      letI : Algebra S Bi := (algebraMap S Bi).toAlgebra
      Nonempty ((A ⊗[R] B) ≃ₐ[A] A ⊗[S] Bi) := by
    rw [toAlgebra_algebraMap]
    exact ⟨(Algebra.TensorProduct.cancelBaseChange R S A A B).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A)) e.symm)⟩
  let A : Type u := (colimit F : CommRingCat.{u})
  let : Algebra A B := f.hom.toAlgebra
  have : Algebra.Etale A B :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hf |>.toAlgebra
  let : Algebra (ULift.{u} ℤ) A :=
    ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : ∀ i, Algebra (ULift.{u} ℤ) (F.obj i) := fun i ↦
    ((Int.castRingHom (F.obj i)).comp ULift.ringEquiv.toRingHom).toAlgebra
  obtain ⟨A₀, B₀, instRing, instAlg, hfg, het, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg (ULift.{u} ℤ) A B
  have : Algebra.FiniteType (ULift.{u} ℤ) A₀ := A₀.fg_iff_finiteType.mp hfg
  let R := CommRingCat.of (ULift.{u} ℤ)
  let α : (Functor.const I).obj R ⟶ F :=
    { app := fun i ↦ CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (F.obj i))
      naturality := by
        intro i k h
        ext ⟨x⟩
        change (x : F.obj k) = (F.map h).hom (x : F.obj i)
        simp }
  let j : R ⟶ CommRingCat.of A₀ := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A₀)
  let _ : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv (ℤ) (ULift.ringEquiv.symm)
  have hj : j.hom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  obtain ⟨i, g, _, hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F α j
      (colimit.cocone F) (colimit.isColimit F) hj
      (CommRingCat.ofHom A₀.val.toRingHom) (by
        intro i
        ext ⟨x⟩
        change (x : A) = (colimit.ι F i).hom (x : F.obj i)
        simp)
  let : Algebra A₀ (F.obj i) := g.hom.toAlgebra
  let : Algebra (F.obj i) A := (colimit.ι F i).hom.toAlgebra
  have : IsScalarTower A₀ (F.obj i) A :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hg)
  let Bi := (F.obj i) ⊗[A₀] B₀
  let : CommRing Bi := inferInstance
  let gi : F.obj i ⟶ CommRingCat.of Bi :=
    CommRingCat.ofHom (algebraMap (F.obj i) Bi)
  refine ⟨i, Bi, inferInstance, gi, ?_, ?_⟩
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance
  · obtain ⟨ec⟩ := cancel A₀ (F.obj i) A B₀ Bi AlgEquiv.refl
    exact ⟨e.trans ec⟩

end AlgebraicGeometry
