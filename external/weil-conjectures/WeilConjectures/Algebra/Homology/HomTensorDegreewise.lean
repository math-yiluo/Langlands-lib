/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseConstruction
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Degreewise currying for the Hom-total-tensor comparison

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- The product projections of the chosen Hom complex. These are the projections
specified together with its bifunctor in `homComplex_exists` (Stacks, Section 0A8X). -/
noncomputable abbrev homTensorProjection (L M : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) L M).X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (M.X q) :=
  homTensorCurryProjection R L M n p q h

/-- Map from the sectionwise presheaf tensor to the underlying sheaf tensor.
It is the sheafification unit followed by the inverse of the tensor comparison.
Source: Stacks, Modules on Sites, Section 03EK. -/
noncomputable abbrev homTensorSectionMap (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    A.val ⊗ B.val ⟶ (A ⊗ B).val :=
  homTensorCurrySectionMap R A B

set_option synthInstance.maxSize 256 in
/-- The degreewise comparison sends `x ⊗ y` to `f(x)(y)` on every localized site.
The equation uses pure tensors before sheafification; it therefore does not assert
that every section of a sheaf tensor is a sum of global pure tensors.
Source: Stacks, Tag 0A90, degreewise construction. -/
abbrev HomTensorCurryCondition (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n) → Prop := by
  exact HomTensorDegreewiseEquation R K L M n

set_option backward.isDefEq.respectTransparency true in
set_option synthInstance.maxSize 256 in
/-- There is a unique degreewise currying map, and it is invertible.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90),
degreewise construction and inverse (blueprint: lem-sc-hom-tensor-degreewise).

Proof: Expand both Hom terms by the product projections of `homComplex_exists`.
A section of the iterated Hom is a family of localized maps indexed by `p,q`.
Evaluate its outer map at `x` and its inner map at `y`. This is balanced bilinear
and compatible with restriction. The presheaf tensor universal property and
sheafification adjunction give a map on each `K^p ⊗ L^q`; the coproduct universal
property combines them for fixed `p+q`. This constructs the displayed map.
Conversely restrict a map out of the total-degree coproduct to each summand,
then curry twice on every localized site. Tensor-Hom adjunction and the product
and coproduct universal properties show both composites are identities.
They also show that the pure-tensor equation determines the map uniquely:
maps out of a sheafification are determined before sheafification, and maps
out of the tensor presheaf are determined on pure tensors. This uses no
boundedness and involves no differentials. -/
theorem homTensorDegreewise_exists (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃! a : (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n,
      HomTensorCurryCondition R K L M n a ∧ IsIso a := by
  let := SheafOfModules.monoidalCategory R
  obtain ⟨a, ha⟩ := homTensorDegreewise_construct R K L M n
  obtain ⟨b, hb⟩ := homTensorDegreewise_inverse R K L M n
  obtain ⟨hab, hba⟩ := hb a ha
  have hIso : IsIso a := ⟨⟨b, hab, hba⟩⟩
  refine ⟨a, ⟨ha, hIso⟩, ?_⟩
  intro c hc
  have hcb := (hb c hc.1).1
  calc
    c = c ≫ (b ≫ a) := by rw [hba, Category.comp_id]
    _ = (c ≫ b) ≫ a := (Category.assoc c b a).symm
    _ = a := by rw [hcb, Category.id_comp]

set_option synthInstance.maxSize 256 in
/-- The unique degreewise currying map, characterized on localized pure tensors.
The existence theorem determines its data uniquely, rather than choosing an
arbitrary witness. Source: Stacks, Tag 0A90. -/
noncomputable def homTensorDegreewiseMap (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n :=
  Classical.choose (ExistsUnique.exists (homTensorDegreewise_exists R K L M n))

set_option synthInstance.maxSize 256 in
/-- The chosen degreewise map satisfies its defining equation and is invertible. -/
theorem homTensorDegreewiseMap_spec (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    HomTensorCurryCondition R K L M n (homTensorDegreewiseMap R K L M n) ∧
      IsIso (homTensorDegreewiseMap R K L M n) :=
  Classical.choose_spec (ExistsUnique.exists (homTensorDegreewise_exists R K L M n))

end CategoryTheory
