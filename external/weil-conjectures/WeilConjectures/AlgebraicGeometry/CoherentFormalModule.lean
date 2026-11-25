/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Algebra.Homology.KFlat

/-! # Coherent formal modules and completion

Source: Stacks Project, Cohomology of Schemes, Section 0EHN, equation 0880,
the paragraph before Lemma 0889, proof of Theorem 088E, and Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module).

## Main definitions
* `CoherentFormalModule`: the full category of coherent adic inverse systems.
* `completion`: the functor taking quotients by positive powers of the ideal.
* `AnnihilatedBy`, `IsIdealPowerTorsion`, `SupportedOn`: annihilation predicates.
* `CohSupportProper`, `CohModuleSupportProper`: full proper-support subcategories.

The index `op n` represents level `n + 1`, so no level zero is imposed.
Products and powers are the shared `Scheme.idealModuleProduct` and `Scheme.idealSheafPower`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- Coherent modules as a full subcategory of all modules.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CoherentModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace)

/-- The quotient by the image of multiplication by the nth power of a quasi-coherent ideal.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotient {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    X.Modules :=
  cokernel (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F)

/-- The quotient projection.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotientπ {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    F ⟶ formalModuleQuotient I n F :=
  cokernel.π (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F)

/-- The defining object conditions: coherence, annihilation by I^(n+1), and an induced
quotient isomorphism whose composite with the quotient projection is the transition map.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
def IsCoherentFormalModule {X : Scheme.{u}} (I : X.IdealSheafData)
    : ObjectProperty (ℕᵒᵖ ⥤ X.Modules) := fun F ↦
  (∀ n : ℕ, RingedSpace.IsCoherent X.toRingedSpace (F.obj (op n))) ∧
  (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
    (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n)))) ∧
  (∀ n : ℕ, ∃ e : formalModuleQuotient I (n + 1) (F.obj (op (n + 1))) ≅ F.obj (op n),
    formalModuleQuotientπ I (n + 1) (F.obj (op (n + 1))) ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op)

/-- The full subcategory of inverse systems satisfying the coherent adic conditions.
This is Stacks' Coh(X, I); the object `op n` is the level `n + 1`. Morphisms are natural
transformations, hence precisely compatible families of module maps.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CoherentFormalModule (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) :=
  (IsCoherentFormalModule I).FullSubcategory

private theorem idealSheafPower_factor {X : Scheme.{u}} (I : X.IdealSheafData)
    {m n : ℕ} (h : n ≤ m) :
    ∃ j : (Scheme.idealSheafPower I.toModulesι m).1 ⟶
        (Scheme.idealSheafPower I.toModulesι n).1,
      j ≫ (Scheme.idealSheafPower I.toModulesι n).2 =
        (Scheme.idealSheafPower I.toModulesι m).2 := by
  have hs (k : ℕ) :
      ∃ j : (Scheme.idealSheafPower I.toModulesι (k + 1)).1 ⟶
          (Scheme.idealSheafPower I.toModulesι k).1,
        j ≫ (Scheme.idealSheafPower I.toModulesι k).2 =
          (Scheme.idealSheafPower I.toModulesι (k + 1)).2 := by
    cases k with
    | zero => exact ⟨I.toModulesι, Category.comp_id _⟩
    | succ k => exact ⟨Scheme.idealModuleProductι I.toModulesι
        (Scheme.idealSheafPower I.toModulesι (k + 1)).1, rfl⟩
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _⟩
  | @step m h ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hk⟩ := hs m
    exact ⟨k ≫ j, by rw [Category.assoc, hj, hk]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A map carries the product by the m-th ideal power into the product by the n-th
ideal power when n ≤ m, hence factors through that product inclusion.
Proof: induct on n ≤ m to factor the power inclusion through lower powers, using the
recursive product inclusion at each successor. Whisker this factorization with F and
use multiplication naturality for f to obtain a commutative square. Mathlib's image map
of this square gives the required map between ideal-module products.
Source: Stacks Project, Cohomology of Schemes, Section 0EHN, equation 0880
(blueprint: lem-weil-pbc-formal-module-ideal-power-factor). -/
theorem formalModuleQuotient_factor {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    ∃ k : Scheme.idealModuleProduct (Scheme.idealSheafPower I.toModulesι m).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower I.toModulesι n).2 G,
      Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 F ≫ f =
        k ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 G := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨j, hj⟩ := idealSheafPower_factor I h
  let a := (Scheme.idealSheafPower I.toModulesι m).2
  let b := (Scheme.idealSheafPower I.toModulesι n).2
  have w : (MonoidalCategoryStruct.whiskerRight j F ≫
      MonoidalCategoryStruct.whiskerLeft (Scheme.idealSheafPower I.toModulesι n).1 f) ≫
      (MonoidalCategoryStruct.whiskerRight b G ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) =
      (MonoidalCategoryStruct.whiskerRight a F ≫
        (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f := by
    rw [Category.assoc, ← MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, hj,
      MonoidalCategory.whisker_exchange_assoc]
    exact (congrArg (((MonoidalCategoryStruct.whiskerRight a F)) ≫ ·)
      (MonoidalCategory.leftUnitor_naturality f)).trans (Category.assoc _ _ _).symm
  refine ⟨image.map (Arrow.homMk' _ _ w), ?_⟩
  exact (image.map_homMk'_ι w).symm

private theorem idealModuleProduct_mono {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules) :
    Mono (Scheme.idealModuleProductι ι F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  dsimp [Scheme.idealModuleProductι]
  infer_instance

private theorem multiplication_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {J F G : C} (ι : J ⟶ MonoidalCategoryStruct.tensorUnit C) (f : F ⟶ G) :
    (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f =
      MonoidalCategoryStruct.whiskerLeft J f ≫ (MonoidalCategoryStruct.whiskerRight ι G ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) := by
  rw [Category.assoc, ← MonoidalCategory.leftUnitor_naturality,
    ← MonoidalCategory.whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_zero_of_mono {X : Scheme.{u}} {J F G : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (f : F ⟶ G) [Mono f]
    (hz : IsZero (Scheme.idealModuleProduct ι G)) :
    IsZero (Scheme.idealModuleProduct ι F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := (MonoidalCategoryStruct.whiskerRight ι F) ≫ (MonoidalCategoryStruct.leftUnitor F).hom
  let b := (MonoidalCategoryStruct.whiskerRight ι G) ≫ (MonoidalCategoryStruct.leftUnitor G).hom
  have hb : b = 0 := by
    rw [← image.fac b]
    have hi : image.ι b = 0 := hz.eq_zero_of_src _
    rw [hi, comp_zero]
  have ha : a = 0 := by
    apply (cancel_mono f).1
    rw [zero_comp]
    change (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f = 0
    rw [multiplication_naturality ι f]
    change ((MonoidalCategoryStruct.whiskerLeft J f)) ≫ b = 0
    rw [hb, comp_zero]
  have : Mono (image.ι a) := inferInstance
  apply IsZero.of_mono_eq_zero (image.ι a)
  apply (cancel_epi (factorThruImage a)).1
  simpa only [image.fac, comp_zero] using ha

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_comp_zero_iff {X : Scheme.{u}} {J F G : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (f : F ⟶ G) :
    let _ : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    Scheme.idealModuleProductι ι F ≫ f = 0 ↔
      (MonoidalCategoryStruct.whiskerRight ι F ≫
        (MonoidalCategoryStruct.leftUnitor F).hom) ≫ f = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := (MonoidalCategoryStruct.whiskerRight ι F) ≫ (MonoidalCategoryStruct.leftUnitor F).hom
  change image.ι a ≫ f = 0 ↔ a ≫ f = 0
  rw [← cancel_epi (factorThruImage a)]
  simp only [← Category.assoc, image.fac, comp_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_quotient_comp_zero_iff {X : Scheme.{u}}
    {J F Q G : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : F ⟶ Q) [Epi q] (f : Q ⟶ G) :
    Scheme.idealModuleProductι ι Q ≫ f = 0 ↔
      Scheme.idealModuleProductι ι F ≫ q ≫ f = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  have : Epi ((MonoidalCategory.tensorLeft J).map q) :=
    (MonoidalCategory.tensorLeft J).map_epi q
  have h₁ := idealModuleProduct_comp_zero_iff ι f
  have h₂ := idealModuleProduct_comp_zero_iff ι (q ≫ f)
  dsimp only at h₁ h₂
  rw [h₁, h₂, ← cancel_epi ((MonoidalCategory.tensorLeft J).map q)]
  rw [comp_zero, ← Category.assoc _ _ f]
  change (MonoidalCategoryStruct.whiskerLeft J q ≫
    (MonoidalCategoryStruct.whiskerRight ι Q ≫
      (MonoidalCategoryStruct.leftUnitor Q).hom)) ≫ f = 0 ↔
    (MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom) ≫ q ≫ f = 0
  rw [← multiplication_naturality ι q, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_quotient_zero {X : Scheme.{u}} {J F : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IsZero (Scheme.idealModuleProduct ι (cokernel (Scheme.idealModuleProductι ι F))) := by
  have := idealModuleProduct_mono ι (cokernel (Scheme.idealModuleProductι ι F))
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι ι _)
  have hz := (idealModuleProduct_quotient_comp_zero_iff ι
    (cokernel.π (Scheme.idealModuleProductι ι F)) (𝟙 _)).mpr (by simp)
  simpa only [Category.comp_id] using hz

set_option backward.isDefEq.respectTransparency false in
private theorem idealModuleProduct_quasicoherent {X : Scheme.{u}} {J : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    [J.IsQuasicoherent] [F.IsQuasicoherent] :
    (Scheme.idealModuleProduct ι F).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections J F).1
  let a := (MonoidalCategoryStruct.whiskerRight ι F) ≫ (MonoidalCategoryStruct.leftUnitor F).hom
  have := Scheme.Modules.isQuasicoherent_cokernel a
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem idealSheafPower_quasicoherent {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) : (Scheme.idealSheafPower I.toModulesι n).1.IsQuasicoherent := by
  have := Scheme.Modules.isQuasicoherent_toModules I
  induction n using Nat.twoStepInduction with
  | zero =>
    change (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent
    exact @SheafOfModules.isQuasicoherent_unit _ _ _ _ X.ringCatSheaf _ _ _ _
  | one => assumption
  | more n ih₁ ih₂ =>
    exact idealModuleProduct_quasicoherent I.toModulesι _

set_option backward.isDefEq.respectTransparency false in
private theorem isFiniteType_of_epi {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Epi f] [F.IsFiniteType] : G.IsFiniteType := by
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q : G.LocalGeneratorsData :=
    { I := p.I
      X := p.X
      coversTop := p.coversTop
      generators i := (p.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (p.X i)).map f) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    have := hp.isFiniteType i
    exact inferInstance
  constructor
  exact ⟨q, hq⟩

/-- Linear maps preserve ideal products; inclusion of powers for n ≤ m gives the
factorization needed for the canonical quotient map. Proof: node steps 1--3: on affine
opens u sends each sum a_i s_i to the sum a_i u(s_i); I^m F is contained in I^n F.
The quotient projection kills I^n F. Equality on the affine basis gives the sheaf equality.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotient_map_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 F ≫
      f ≫ formalModuleQuotientπ I n G = 0 := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor I f h
  calc
    _ = (k ≫ Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι n).2 G) ≫
      formalModuleQuotientπ I n G := by
        rw [← hk]
        simp only [Category.assoc]
    _ = 0 := by simp [formalModuleQuotientπ]

/-- Reduction of a linear map from level m to level n, n ≤ m, by the cokernel property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotientMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    formalModuleQuotient I m F ⟶ formalModuleQuotient I n G :=
  cokernel.desc (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 F)
    (f ≫ formalModuleQuotientπ I n G) (formalModuleQuotient_map_zero I f h)

/-- Reduction preserves identities. Proof: node step 6; after precomposing with the
cokernel projection both sides are the projection, so the cokernel universal property
identifies them.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotientMap_id {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) (n : ℕ) :
    formalModuleQuotientMap I (𝟙 F) (Nat.le_refl n) = 𝟙 (formalModuleQuotient I n F) := by
  apply (cancel_epi (cokernel.π
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι _).2 _))).1
  simp [formalModuleQuotientMap, formalModuleQuotientπ, formalModuleQuotient]

/-- Reduction preserves composition, including transition maps between different levels.
Proof: node step 6; precompose with the source quotient projection, use the defining
factorization of each reduction, and cancel this epimorphism by the cokernel property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotientMap_comp {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) {l m n : ℕ}
    (h₁ : m ≤ l) (h₂ : n ≤ m) :
    formalModuleQuotientMap I (f ≫ g) (Nat.le_trans h₂ h₁) =
      formalModuleQuotientMap I f h₁ ≫ formalModuleQuotientMap I g h₂ := by
  apply (cancel_epi (cokernel.π
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι _).2 _))).1
  simp [formalModuleQuotientMap, formalModuleQuotientπ, Category.assoc]

private theorem formalModuleQuotient_iterated {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) {m n : ℕ} (h : n ≤ m) :
    ∃ e : formalModuleQuotient I n (formalModuleQuotient I m F) ≅
        formalModuleQuotient I n F,
      formalModuleQuotientπ I n (formalModuleQuotient I m F) ≫ e.hom =
        formalModuleQuotientMap I (𝟙 F) h := by
  let b := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F
  let q := formalModuleQuotientπ I m F
  let t := formalModuleQuotientMap I (𝟙 F) h
  let k := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
    (formalModuleQuotient I m F)
  have : Epi q := inferInstanceAs (Epi (cokernel.π _))
  have ht : k ≫ t = 0 := by
    apply (idealModuleProduct_quotient_comp_zero_iff _ q t).mpr
    simp [q, t, formalModuleQuotientπ, formalModuleQuotientMap]
  let a := cokernel.desc k t ht
  have hv : b ≫ q ≫ cokernel.π k = 0 :=
    (idealModuleProduct_quotient_comp_zero_iff _ q (cokernel.π k)).mp
      (cokernel.condition k)
  let v := cokernel.desc b (q ≫ cokernel.π k) hv
  have hav : a ≫ v = 𝟙 _ := by
    apply (cancel_epi (cokernel.π k)).1
    apply (cancel_epi q).1
    simp [a, v, q, t, b, formalModuleQuotientπ, formalModuleQuotientMap]
  have hva : v ≫ a = 𝟙 _ := by
    apply (cancel_epi (cokernel.π b)).1
    simp [a, v, q, t, b, formalModuleQuotientπ, formalModuleQuotientMap, Category.assoc]
  refine ⟨⟨a, v, hav, hva⟩, ?_⟩
  exact cokernel.π_desc k t ht

/-- Canonical reductions form an inverse system. Proof: node steps 5--6; quotient
projections are epi, and both sides of each identity or composition law agree after
precomposition with the projection, by uniqueness in the cokernel universal property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionSystem_laws {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) :
    (∀ n : ℕᵒᵖ, formalModuleQuotientMap I (𝟙 F)
      (Nat.succ_le_succ (leOfHom (𝟙 n).unop)) =
        𝟙 (formalModuleQuotient I (n.unop + 1) F)) ∧
    (∀ (a b c : ℕᵒᵖ) (f : a ⟶ b) (g : b ⟶ c),
      formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom (f ≫ g).unop)) =
        formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom f.unop)) ≫
          formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom g.unop))) := by
  constructor
  · intro n
    exact formalModuleQuotientMap_id I F (n.unop + 1)
  · intro a b c f g
    simpa using formalModuleQuotientMap_comp I (𝟙 F) (𝟙 F)
      (Nat.succ_le_succ (leOfHom f.unop)) (Nat.succ_le_succ (leOfHom g.unop))

/-- The inverse system F/I^(n+1)F, with the canonical surjections.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionSystem {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := formalModuleQuotient I (n.unop + 1) F
  map f := formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom f.unop))
  map_id := (formalCompletionSystem_laws I F).1
  map_comp f g := (formalCompletionSystem_laws I F).2 _ _ _ f g

/-- Reduction of a module map commutes with transitions. Proof: node step 6; both
composites after precomposition with the source quotient map are u followed by the target
quotient map, so uniqueness of cokernel factorization gives equality.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionMap_naturality {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (u : F ⟶ G) (a b : ℕᵒᵖ) (f : a ⟶ b) :
    (formalCompletionSystem I F).map f ≫
      formalModuleQuotientMap I u (Nat.le_refl (b.unop + 1)) =
    formalModuleQuotientMap I u (Nat.le_refl (a.unop + 1)) ≫
      (formalCompletionSystem I G).map f := by
  dsimp only [formalCompletionSystem]
  rw [← formalModuleQuotientMap_comp, ← formalModuleQuotientMap_comp]
  simp

/-- The compatible family of reductions of a module map.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (u : F ⟶ G) : formalCompletionSystem I F ⟶ formalCompletionSystem I G
    where
  app n := formalModuleQuotientMap I u (Nat.le_refl (n.unop + 1))
  naturality := formalCompletionMap_naturality I u

set_option backward.isDefEq.respectTransparency false in
/-- Completion of a coherent module satisfies the object conditions. Proof: node steps
1--5. Ideal powers and their products with F are quasi-coherent: tensor products are
quasi-coherent, and their images are kernels of quasi-coherent cokernels. The quotient
is quasi-coherent and of finite type, since images of finite local generators generate
any epimorphic quotient; the locally Noetherian coherence criterion applies.
Naturality of multiplication and epimorphy of tensoring a quotient projection show that
I^n acts by zero on F/I^n F. The same calculation identifies maps out of the iterated
quotient with maps out of F killing I^n F. Construct both directions of the resulting
quotient isomorphism by cokernel.desc; cancel the quotient projections to prove that
they are inverse and that the isomorphism induces the specified transition map.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionSystem_coherent {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentModules X) :
    IsCoherentFormalModule I (formalCompletionSystem I F.obj) := by
  have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  have : F.obj.IsQuasicoherent := hF.1
  have : F.obj.IsFiniteType := hF.2
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change RingedSpace.IsCoherent X.toRingedSpace (formalModuleQuotient I (n + 1) F.obj)
    have := idealSheafPower_quasicoherent I (n + 1)
    have := idealModuleProduct_quasicoherent
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F.obj
    have := Scheme.Modules.isQuasicoherent_cokernel
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F.obj)
    have := isFiniteType_of_epi
      (cokernel.π (Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F.obj))
    apply (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
    change (cokernel (Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F.obj)).IsQuasicoherent ∧
      (cokernel (Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F.obj)).IsFiniteType
    exact ⟨inferInstance, inferInstance⟩
  · intro n
    exact idealModuleProduct_quotient_zero (Scheme.idealSheafPower I.toModulesι (n + 1)).2
  · intro n
    exact formalModuleQuotient_iterated I F.obj (Nat.le_succ (n + 1))

/-- The reduced maps satisfy functor laws. Proof: node step 6; check each component and
precompose with its quotient projection. For identities both sides give the projection;
for composition both sides give the original composite followed by the projection.
The cokernel property and componentwise equality identify the natural transformations.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionMap_laws {X : Scheme.{u}} (I : X.IdealSheafData) :
    (∀ F : X.Modules, formalCompletionMap I (𝟙 F) = 𝟙 (formalCompletionSystem I F)) ∧
    (∀ (F G H : X.Modules) (f : F ⟶ G) (g : G ⟶ H),
      formalCompletionMap I (f ≫ g) = formalCompletionMap I f ≫ formalCompletionMap I g) := by
  constructor
  · intro F
    apply NatTrans.ext
    funext n
    exact formalModuleQuotientMap_id I F (n.unop + 1)
  · intro F G H f g
    apply NatTrans.ext
    funext n
    exact formalModuleQuotientMap_comp I f g (Nat.le_refl (n.unop + 1))
      (Nat.le_refl (n.unop + 1))

/-- The functor to inverse systems, on objects the quotients and on maps their reductions.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionFunctor {X : Scheme.{u}} (I : X.IdealSheafData) :
    X.Modules ⥤ (ℕᵒᵖ ⥤ X.Modules) where
  obj := formalCompletionSystem I
  map := formalCompletionMap I
  map_id := (formalCompletionMap_laws I).1
  map_comp f g := (formalCompletionMap_laws I).2 _ _ _ f g

/-- The completion functor Coh(O_X) → Coh(X,I), with the specified quotient data.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def completion (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) :
    CoherentModules X ⥤ CoherentFormalModule X I :=
  ObjectProperty.lift (IsCoherentFormalModule I)
    (ObjectProperty.ι (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace) ⋙
      formalCompletionFunctor I)
    (formalCompletionSystem_coherent I)

/-- Annihilation by a quasi-coherent ideal means its product with each term is zero.
Source: Stacks, paragraph before Lemma 0889 and proof of Theorem 088E
(blueprint: def-weil-pbc-coherent-formal-module). -/
def AnnihilatedBy {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) : Prop :=
  ∀ n : ℕ, IsZero (Scheme.idealModuleProduct K.toModulesι (M.obj.obj (op n)))

/-- Uniform annihilation by a positive power of I, as opposed to the termwise adic condition.
Source: Stacks, paragraph before Lemma 0889
(blueprint: def-weil-pbc-coherent-formal-module). -/
def IsIdealPowerTorsion {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (M : CoherentFormalModule X I) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
    (Scheme.idealSheafPower I.toModulesι c).2 (M.obj.obj (op n)))

/-- Uniform annihilation by I^(c+1) is equivalent to stabilization at level c+1.
Proof: node step 7. Inclusions of higher ideal powers into lower ones transfer
annihilation to all higher powers. Uniform annihilation therefore makes each successive
quotient projection at or above c an isomorphism; the defining quotient isomorphisms
of M and induction on c ≤ n make every transition to level c an isomorphism.
Conversely, level c is annihilated by I^(c+1). Naturality of multiplication transports
this to every level n ≥ c along the monomorphic transition to level c. For n < c,
the higher-power product factors through I^(n+1)M_n, which is zero by the adic condition.
Source: Stacks, paragraph before Lemma 0889
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModule_annihilated_power_iff {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (M : CoherentFormalModule X I) (c : ℕ) :
    (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower I.toModulesι (c + 1)).2 (M.obj.obj (op n)))) ↔
    ∀ (n : ℕ) (h : c ≤ n), IsIso (M.obj.map (homOfLE h).op) := by
  have hzero {a b : ℕ} (h : a ≤ b) (F : X.Modules)
      (hz : IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower I.toModulesι a).2 F)) :
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower I.toModulesι b).2 F) := by
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor I (𝟙 F) h
    have hi := hz.eq_zero_of_src
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι a).2 F)
    have := idealModuleProduct_mono (Scheme.idealSheafPower I.toModulesι b).2 F
    apply IsZero.of_mono_eq_zero
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι b).2 F)
    simpa [hi] using hk
  constructor
  · intro hz n hn
    have hsucc (k : ℕ) (hk : c ≤ k) :
        IsIso (M.obj.map (homOfLE (Nat.le_succ k)).op) := by
      obtain ⟨e, he⟩ := M.property.2.2 k
      have hi : Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (k + 1)).2
          (M.obj.obj (op (k + 1))) = 0 :=
        (hzero (Nat.add_le_add_right hk 1) _ (hz (k + 1))).eq_zero_of_src _
      have : IsIso (formalModuleQuotientπ I (k + 1) (M.obj.obj (op (k + 1)))) := by
        exact CokernelCofork.IsColimit.isIso_π
          (CokernelCofork.ofπ (cokernel.π _) (cokernel.condition _))
          (cokernelIsCokernel _) hi
      rw [← he]
      infer_instance
    induction hn with
    | refl =>
      have he : (homOfLE (show c ≤ c from le_rfl)).op = 𝟙 (op c) := Subsingleton.elim _ _
      rw [he, M.obj.map_id]
      infer_instance
    | @step n hn ih =>
      have := hsucc n hn
      have he : (homOfLE (show c ≤ n + 1 from Nat.le_succ_of_le hn)).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op := Subsingleton.elim _ _
      rw [he, M.obj.map_comp]
      infer_instance
  · intro hs n
    by_cases hn : c ≤ n
    · have := hs n hn
      exact idealModuleProduct_zero_of_mono
        (Scheme.idealSheafPower I.toModulesι (c + 1)).2
        (M.obj.map (homOfLE hn).op) (M.property.2.1 c)
    · exact hzero (Nat.add_le_add_right (Nat.le_of_lt (Nat.lt_of_not_ge hn)) 1)
        _ (M.property.2.1 n)

/-- Support on a closed subscheme means annihilation by its ideal, including its nilpotents.
Source: Stacks, proof of Theorem 088E (blueprint: def-weil-pbc-coherent-formal-module). -/
def SupportedOn {X Z : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (M : CoherentFormalModule X I) (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  AnnihilatedBy I i.ker M

/-- The analogous scheme-theoretic support condition for a coherent module.
Source: Stacks, proof of Theorem 088E (blueprint: def-weil-pbc-coherent-formal-module). -/
def CoherentModuleSupportedOn {X Z : Scheme.{u}} (F : CoherentModules X)
    (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  IsZero (Scheme.idealModuleProduct i.ker.toModulesι F.obj)

/-- Full subcategory of formal modules whose level 1 has support proper over the base.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CohSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (fun M : CoherentFormalModule X I ↦
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)))

/-- Full subcategory of coherent modules with support proper over the base.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CohModuleSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :=
  ObjectProperty.FullSubcategory
    (fun F : CoherentModules X ↦ Scheme.Modules.HasSupportProperOver f F.obj)

/-- The support of F/IF is contained in the support of F.
Proof: node step 8. The quotient projection is surjective on sections over affine opens,
by lem-weil-pbc-quasi-coherent-module-cokernel-image, hence on stalks by the affine-basis
colimit description in def-weil-pbc-module-stalk. A quotient of a zero stalk is zero.
Therefore a nonzero quotient stalk can occur only at a nonzero original stalk.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletion_support_subset {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentModules X) :
    {x : X | ¬ Subsingleton ((formalModuleQuotient I 1 F.obj).presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (F.obj.presheaf.stalk x)} := by
  intro x hx hF
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let ι := Scheme.idealModuleProductι I.toModulesι F.obj
  have : Epi (S.map (cokernel.π ι)) :=
    ((RingedSpace.module_stalk_exact X.toRingedSpace ι).2.2.1 x).1
  have : Subsingleton (S.obj F.obj) := hF
  have hQ : Subsingleton (S.obj (cokernel ι)) :=
    Function.Surjective.subsingleton
      ((ModuleCat.epi_iff_surjective (S.map (cokernel.π ι))).mp inferInstance)
  exact hx hQ

/-- Completion preserves proper support. Proof: node step 8. A coherent module has closed
support on a Noetherian scheme. The quotient projection is surjective on affine sections,
hence on stalks. A zero stalk of F therefore gives a zero stalk of F/IF. Its closed support
is contained in the closed support of F, and a closed subset of a support proper over the
base is proper (Lemma 0CYN). Thus the level-1 support has the required properness.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletion_support_proper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData)
    (F : CohModuleSupportProper f) :
    Scheme.Modules.HasSupportProperOver f (((completion X I).obj F.obj).obj.obj (op 0)) := by
  obtain ⟨Z, hZ, hproper⟩ := F.property
  have hcoh := ((completion X I).obj F.obj).property.1 0
  have hft := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X _).mp hcoh
  let Q := (((completion X I).obj F.obj).obj.obj (op 0))
  have : Q.IsQuasicoherent := hft.1
  have : Q.IsFiniteType := hft.2
  obtain ⟨Y, hY⟩ := (Scheme.Modules.module_support_proper_over_base f Q).1
  refine ⟨Y, hY, ?_⟩
  apply (Scheme.closed_subset_proper_over_base_properties f Z).2.2.1 Y _ hproper
  intro x hx
  change x ∈ (Z : Set X)
  rw [hZ]
  apply formalCompletion_support_subset I F.obj
  have hxQ : x ∈ {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
    rw [← hY]
    exact hx
  exact hxQ

/-- Restriction of completion to the two proper-support full subcategories.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
def completionSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :
    CohModuleSupportProper f ⥤ CohSupportProper f I :=
  ObjectProperty.lift
    (fun M : CoherentFormalModule X I ↦
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)))
    (ObjectProperty.ι
      (fun F : CoherentModules X ↦ Scheme.Modules.HasSupportProperOver f F.obj) ⋙
      completion X I) (formalCompletion_support_proper f I)

end

end AlgebraicGeometry
