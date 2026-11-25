/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Lifting reduced splittings in a projective class

Source: Stacks Project, More on Algebra, Tag 0BCA.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

private theorem quotient_unit_surjective
    (R : Type u) [CommRing R] (I : Ideal R) (M : ModuleCat.{max u v} R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj
      (Ideal.Quotient.mk I)).unit.app M) := by
  intro z
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M))
    (TensorProduct.quotTensorEquivQuotSMul M I z)
  refine ⟨x, ?_⟩
  apply (TensorProduct.quotTensorEquivQuotSMul M I).injective
  simpa only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.mkQ_apply] using hx

private theorem lift_reduced_morphism
    (R : Type u) [CommRing R] (I : Ideal R)
    (P Q : ModuleCat.{max u v} R) [Projective P]
    (f : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ⟶
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj Q) :
    ∃ g : P ⟶ Q, (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map g = f := by
  let adj := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)
  have : Epi (adj.unit.app Q) :=
    (ModuleCat.epi_iff_surjective _).mpr (quotient_unit_surjective R I Q)
  obtain ⟨g, hg⟩ := Projective.factors (adj.homEquiv P _ f) (adj.unit.app Q)
  refine ⟨g, (adj.homEquiv P _).injective ?_⟩
  simpa only [Adjunction.homEquiv_unit, Functor.comp_map]
    using (adj.unit.naturality g).symm.trans hg

private theorem isIso_of_reduced_isIso
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hsurj : ∀ (P₁ P₂ : ModuleCat.{max u v} R) (f : P₁ ⟶ P₂),
      P₁ ∈ Pclass → P₂ ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (hZ : (CategoryTheory.Limits.HasZeroObject.zero
      (C := ModuleCat.{max u v} R)).choose ∈ Pclass)
    (P Q : ModuleCat.{max u v} R) (f : P ⟶ Q)
    (hP : P ∈ Pclass) (hQ : Q ∈ Pclass)
    (hf : IsIso ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f)) :
    IsIso f :=
    open CategoryTheory.Limits in by
  let : Zero (ModuleCat.{max u v} R) :=
    CategoryTheory.Limits.HasZeroObject.zero' (ModuleCat.{max u v} R)
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  have : Projective Q := hproj Q hQ
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (hsurj P Q f hP hQ ((ModuleCat.epi_iff_surjective (F.map f)).mp inferInstance))
  let t : Q ⟶ P := Projective.factorThru (𝟙 Q) f
  let s := ShortComplex.Splitting.ofExactOfSection (ShortComplex.kernelSequence f)
    (ShortComplex.kernelSequence_exact f) t
    (Projective.factorThru_comp (𝟙 Q) f) inferInstance
  have hK : kernel f ∈ Pclass :=
    ((hclosed Q (kernel f) P
      ⟨s.isoBinaryBiproduct ≪≫ biprod.braiding _ _ ≪≫ ModuleCat.biprodIsoProd _ _⟩).mp
      ⟨hQ, hP⟩).2
  have hi : F.map (kernel.ι f) = 0 := by
    apply zero_of_comp_mono (F.map f)
    rw [← F.map_comp, kernel.condition, F.map_zero]
  have : Mono (F.map (kernel.ι f)) := (s.map F).mono_f
  have hFK : IsZero (F.obj (kernel f)) := by
    apply IsZero.of_mono_eq_zero (F.map (kernel.ι f)) hi
  have : Subsingleton (F.obj (kernel f)) := ModuleCat.subsingleton_of_isZero hFK
  have hred : Function.Surjective (F.map (0 : (0 : ModuleCat.{max u v} R) ⟶ kernel f)) :=
    fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  have : Epi (0 : (0 : ModuleCat.{max u v} R) ⟶ kernel f) :=
    (ModuleCat.epi_iff_surjective _).mpr (hsurj 0 (kernel f) 0 hZ hK hred)
  have hKzero : IsZero (kernel f) :=
    IsZero.of_epi_zero (0 : ModuleCat.{max u v} R) (kernel f)
  have : Mono f := Preadditive.mono_of_isZero_kernel f hKzero
  exact isIso_of_mono_of_epi f

/-- Lift a split reduced right-exact sequence for a projective class.

Source: Stacks Project, More on Algebra, Tag 0BCA, final paragraph.
(blueprint: lem-sc-projective-class-reduced-splitting).

Proof: Choose a class member T lifting the last reduced module. Lift the reduced
projection from the middle term to T using projectivity of the middle term. It is
surjective by the class hypothesis and splits by projectivity of T. Its kernel U
belongs to the class by closure under summands. The composite from the first term
into U is invertible modulo I, hence is surjective and splits. Its kernel V belongs
to the class and has zero reduction. The zero module belongs to the class as a
summand of the first term; apply the surjectivity hypothesis to zero -> V to get
V = 0. Thus the composite into U is invertible and the original first map is a
split injection. Exactness and epimorphy identify the last term with its cokernel.
The resulting decomposition of the middle term, and the class condition, put this
cokernel in the class. -/
theorem projective_class_reduced_splitting
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hsurj : ∀ (P₁ P₂ : ModuleCat.{max u v} R) (f : P₁ ⟶ P₂),
      P₁ ∈ Pclass → P₂ ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (S : ShortComplex (ModuleCat.{max u v} R))
    (hexact : S.Exact) (hepi : Epi S.g)
    (hfirst : S.X₁ ∈ Pclass) (hmiddle : S.X₂ ∈ Pclass)
    (hsplit : Nonempty ((S.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))).Splitting))
    (hlast : ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj S.X₃ ≅
        (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)) :
    S.ShortExact ∧ S.X₃ ∈ Pclass :=
    open CategoryTheory.Limits in by
  let : Zero (ModuleCat.{max u v} R) :=
    CategoryTheory.Limits.HasZeroObject.zero' (ModuleCat.{max u v} R)
  -- Only a class member is needed from the last-object lift, to put zero in the class.
  obtain ⟨P, hP, _⟩ := hlast
  have hZ : (0 : ModuleCat.{max u v} R) ∈ Pclass :=
    ((hclosed P 0 P
      ⟨isoBiprodZero (isZero_zero _) ≪≫ ModuleCat.biprodIsoProd _ _⟩).mp ⟨hP, hP⟩).2
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  have : Projective S.X₂ := hproj S.X₂ hmiddle
  obtain ⟨s⟩ := hsplit
  obtain ⟨r, hr⟩ := lift_reduced_morphism R I S.X₂ S.X₁ s.r
  have hred : IsIso (F.map (S.f ≫ r)) := by
    have hcomp : F.map (S.f ≫ r) = 𝟙 (F.obj S.X₁) := by
      rw [F.map_comp, hr]
      exact s.f_r
    rw [hcomp]
    infer_instance
  have : IsIso (S.f ≫ r) :=
    isIso_of_reduced_isIso R I Pclass hproj hclosed hsurj hZ S.X₁ S.X₁ (S.f ≫ r)
      hfirst hfirst hred
  let t : S.X₂ ⟶ S.X₁ := r ≫ inv (S.f ≫ r)
  have ht : S.f ≫ t = 𝟙 S.X₁ := by
    simp [t, ← Category.assoc]
  let split := ShortComplex.Splitting.ofExactOfRetraction S hexact t ht hepi
  refine ⟨split.shortExact, ?_⟩
  exact ((hclosed S.X₁ S.X₃ S.X₂
    ⟨split.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _⟩).mp ⟨hfirst, hmiddle⟩).2

end AlgebraicGeometry
