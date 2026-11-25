/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Algebra.Homology.ModuleHomComplex
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem

/-! # Normalized chain representatives for Koszul derived Hom

Source: Stacks Project, Tags 06Z0 and 08DD.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section

/-- The class of a chain map in the module-valued Hom complex.
Source: Stacks Project, Tag 0A8H; cycles are chain maps and boundaries are homotopies.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulHomChainClass {A : Type u} [CommRing A]
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (t : L ⟶ M) :
    (CochainComplex.moduleHomComplex L M).homology 0 :=
  let S := (CochainComplex.moduleHomComplex L M).sc 0
  (S.moduleCatCyclesIso.inv ≫ S.homologyπ)
    ⟨CochainComplex.HomComplex.Cochain.ofHom t, by
      change CochainComplex.HomComplex.δ 0 _
        (CochainComplex.HomComplex.Cochain.ofHom t) = 0
      exact CochainComplex.HomComplex.δ_ofHom t⟩

/-- Transpose a sheaf chain map through the ordinary affine tilde/sections adjunction.
Source: Stacks Project, Tag 06Z0.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulOpenHomTranspose (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F) :
    (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶
      ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F :=
  letI : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  letI : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  ((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv _ _ t

/-- The chain-map class in the specified stage of the derived Hom diagram.
This is constructed from the cycle, the homology projection, and the specified object iso.
Source: Stacks Project, Tags 0A8H and 08D1.
(blueprint: lem-sc-koszul-open-hom-chain-representatives). -/
def koszulOpenHomStageClass (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (DerivedCategory.Q.obj ((koszulCechHomDiagram A r f
        (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)).obj e)) :=
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let K := CochainComplex.moduleHomComplex
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  H.map (DerivedCategory.Q.map (koszulCechHomObjIso A r f M e).inv)
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app K).inv
      (koszulHomChainClass (koszulOpenHomTranspose A r f F e t)))

set_option backward.isDefEq.respectTransparency false in
/-- The affine derived equivalence agrees with ordinary transposition on chain maps.
Source: Stacks Project, Tag 06Z0, Lemma on the affine derived equivalence.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).

Proof: The exact tilde functor induces the affine derived equivalence. On the full
subcategory of quasi-coherent sheaves, ordinary sections is its exact inverse:
the unit is invertible on every module and the counit is invertible on every
quasi-coherent sheaf. Apply these maps termwise to L and F. The termwise counit
identifies F with tilde of its sections complex. Full faithfulness of the derived
affine equivalence, followed by that identification, gives b. For a chain map t,
the ordinary tilde/sections adjunction writes t as tilde of its transpose followed
by the counit. Apply Q to this equality. The equivalence and its inverse use the
same unit and counit, so the resulting equation is precisely the displayed one.
No boundedness of F is used: sections is exact on the quasi-coherent subcategory.
Zero complexes and the zero ring are included by the same unit/counit identities. -/
private theorem affineComplexHom_transpose
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (L : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    letI : (tilde.functor (.of A)).Additive :=
      ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
    letI : (moduleSpecΓFunctor (R := .of A)).Additive :=
      ⟨fun {_ _} _ _ ↦ rfl⟩
    ∃ b : (DerivedCategory.Q.obj
        (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L) ⟶
          DerivedCategory.Q.obj F) ≃
        (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj
          (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)),
      ∀ t : ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L ⟶ F,
        b (DerivedCategory.Q.map t) = DerivedCategory.Q.map
          (((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv _ _ t)
    := by
  classical
  let : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  let : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  let T := (tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)
  let adj := (tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨e, ⟨α⟩, _, _, _⟩ := exists_affineQCohDerivedEquivalence A
  let B := e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι
  let ff : B.FullyFaithful := e.fullyFaithfulFunctor.comp
    (schemeDerivedQCohProperty (Spec (.of A))).fullyFaithfulι
  have hε (n : ℤ) : IsIso ((adj.counit.app F).f n) := by
    let : (F.X n).IsQuasicoherent := hF n
    change IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (F.X n))
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) (F.X n)
  let : ∀ n, IsIso ((adj.counit.app F).f n) := hε
  let : IsIso (adj.counit.app F) := HomologicalComplex.Hom.isIso_of_components _
  let s : B.obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj (T.obj L) := α.app L
  let j : B.obj (DerivedCategory.Q.obj M) ≅ DerivedCategory.Q.obj F :=
    α.app M ≪≫ DerivedCategory.Q.mapIso (asIso (adj.counit.app F))
  let b := (Iso.homCongr s.symm j.symm).trans ff.homEquiv.symm
  refine ⟨b, ?_⟩
  intro t
  apply ff.homEquiv.injective
  change ff.homEquiv (b (DerivedCategory.Q.map t)) = _
  dsimp only [b, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply]
  change s.hom ≫ DerivedCategory.Q.map t ≫ j.inv =
    B.map (DerivedCategory.Q.map (adj.homEquiv _ _ t))
  have ht : T.map (adj.homEquiv _ _ t) ≫ adj.counit.app F = t := by
    exact (adj.homEquiv_symm_apply L F (adj.homEquiv _ _ t)).symm.trans
      ((adj.homEquiv _ _).symm_apply_apply t)
  have hn := α.hom.naturality (adj.homEquiv _ _ t)
  change B.map (DerivedCategory.Q.map (adj.homEquiv _ _ t)) ≫ (α.app M).hom =
    (α.app L).hom ≫ DerivedCategory.Q.map (T.map (adj.homEquiv _ _ t)) at hn
  rw [← cancel_mono j.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [j, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ht]

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cycleEquiv (A : Type u) [CommRing A]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
    Cocycle L M 0 ≃+
      LinearMap.ker ((CochainComplex.moduleHomComplex L M).sc 0).g.hom where
  toFun z := ⟨z.val, by
    change δ 0 _ z.val = 0
    exact Cocycle.δ_eq_zero z _⟩
  invFun z := ⟨z.val, by
    have hz := z.property
    change δ 0 ((ComplexShape.up ℤ).next 0) z.val = 0 at hz
    rw [CochainComplex.next ℤ 0] at hz
    exact hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cycleProjection (A : Type u) [CommRing A]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
    Cocycle L M 0 →+ (CochainComplex.moduleHomComplex L M).homology 0 :=
  let S := (CochainComplex.moduleHomComplex L M).sc 0
  ((S.moduleCatCyclesIso.inv ≫ S.homologyπ).hom.toAddMonoidHom).comp
    (cycleEquiv A L M).toAddMonoidHom

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private theorem cycleProjection_zero_iff (A : Type u) [CommRing A]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) (z : Cocycle L M 0) :
    cycleProjection A L M z = 0 ↔ z ∈ coboundaries L M 0 := by
  let S := (CochainComplex.moduleHomComplex L M).sc 0
  have hi := (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).mp inferInstance
  rw [← hi.eq_iff]
  simp only [map_zero]
  change S.moduleCatHomologyIso.hom
    ((S.moduleCatCyclesIso.inv ≫ S.homologyπ) (cycleEquiv A L M z)) = 0 ↔ _
  rw [← ConcreteCategory.comp_apply, Category.assoc, S.moduleCatCyclesIso_inv_π_assoc]
  simp only [CategoryTheory.Iso.inv_hom_id, Category.comp_id]
  change Submodule.Quotient.mk (cycleEquiv A L M z) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_coboundaries_iff z (-1) (by norm_num)]
  change (∃ x : Cochain L M ((ComplexShape.up ℤ).prev 0),
    S.moduleCatToCycles x = cycleEquiv A L M z) ↔ _
  simp only [Subtype.ext_iff]
  change (∃ x : Cochain L M ((ComplexShape.up ℤ).prev 0),
    δ ((ComplexShape.up ℤ).prev 0) 0 x = z.val) ↔ _
  rw [CochainComplex.prev ℤ 0]
  rfl


open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private theorem cycleProjection_surjective (A : Type u) [CommRing A]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
    Function.Surjective (cycleProjection A L M) := by
  let S := (CochainComplex.moduleHomComplex L M).sc 0
  have hπ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance
  intro x
  obtain ⟨y, rfl⟩ := hπ x
  refine ⟨(cycleEquiv A L M).symm (S.moduleCatCyclesIso.hom y), ?_⟩
  change (S.moduleCatCyclesIso.inv ≫ S.homologyπ)
    (cycleEquiv A L M ((cycleEquiv A L M).symm (S.moduleCatCyclesIso.hom y))) = _
  rw [AddEquiv.apply_symm_apply]
  simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id_assoc]

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def classHomologyEquiv (A : Type u) [CommRing A]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) :
    CohomologyClass L M 0 ≃+ (CochainComplex.moduleHomComplex L M).homology 0 :=
  let q := CohomologyClass.descAddMonoidHom (cycleProjection A L M)
    (fun z hz ↦ (cycleProjection_zero_iff A L M z).mpr hz)
  AddEquiv.ofBijective q (by
    constructor
    · intro x y h
      obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
      obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        ← cycleProjection_zero_iff, map_sub, sub_eq_zero]
      exact h
    · intro x
      obtain ⟨z, hz⟩ := cycleProjection_surjective A L M x
      exact ⟨CohomologyClass.mk z, hz⟩)


open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero module Hom homology computes maps out of a K-projective complex.
Source: Stacks Project, Tag 0A8H (Hom complexes), and More on Algebra, Lemma 15.75.2.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).

Proof: A degree-zero Hom cocycle is exactly a chain map, by the identity
δ(z)=d_M z-z d_L. Degree-zero boundaries are exactly differences of homotopic
chain maps: a degree-minus-one cochain is the family of components of the homotopy,
and its differential is d_M h+h d_L. Thus the quotient of cycles by boundaries
identifies with the homotopy-category Hom group. The module-valued short-complex
homology projection is that same quotient, through moduleCatCyclesIso. Apply
IsKProjective.Qh_map_bijective and quotientCompQhIso to identify this homotopy Hom
group with derived maps. Take the inverse bijection to obtain c. On Q.map t the
homotopy class is the class of t, and the quotient description gives the displayed
normalization. These constructions work without boundedness on M and also when
L or M is zero or A is the zero ring. -/
private theorem moduleHomDerived_class
    (A : Type u) [CommRing A] [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (L M : CochainComplex (ModuleCat.{u} A) ℤ) [L.IsKProjective] :
    ∃ c : (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) ≃
        (CochainComplex.moduleHomComplex L M).homology 0,
      ∀ t : L ⟶ M,
        c (DerivedCategory.Q.map t) =
          let S := (CochainComplex.moduleHomComplex L M).sc 0
          (S.moduleCatCyclesIso.inv ≫ S.homologyπ)
            ⟨CochainComplex.HomComplex.Cochain.ofHom t, by
              change CochainComplex.HomComplex.δ 0 _
                (CochainComplex.HomComplex.Cochain.ofHom t) = 0
              exact CochainComplex.HomComplex.δ_ofHom t⟩ := by
  classical
  let : Localization.HasSmallLocalizedShiftedHom.{v}
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) ℤ L M := by
    intro a b
    exact Localization.hasSmallLocalizedHom_of_isLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) DerivedCategory.Q
  let d : CohomologyClass L M 0 ≃
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) :=
    (CohomologyClass.equivOfIsKProjective.{v}.trans
      (Localization.SmallShiftedHom.equiv.{v} _ DerivedCategory.Q)).trans
        (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
  have hd (t : L ⟶ M) : d (CohomologyClass.mk (Cocycle.ofHom t)) =
      DerivedCategory.Q.map t := by
    have ht : Cocycle.equivHomShift.symm (Cocycle.ofHom t) =
        ShiftedHom.mk₀ (0 : ℤ) rfl t := by
      apply Cocycle.equivHomShift.injective
      rw [AddEquiv.apply_symm_apply]
      apply Cocycle.ext
      apply Cochain.ext
      intro p q hpq
      obtain rfl : p = q := by omega
      simp [Cocycle.equivHomShift_apply, Cochain.rightUnshift_v,
        ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero',
        CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq]
    dsimp only [d, Equiv.trans_apply]
    rw [CohomologyClass.equivOfIsKProjective_apply,
      CohomologyClass.equiv_toSmallShiftedHom_mk, ht, ShiftedHom.map_mk₀]
    exact (ShiftedHom.homEquiv (0 : ℤ) rfl).left_inv _
  refine ⟨d.symm.trans (classHomologyEquiv A L M).toEquiv, ?_⟩
  intro t
  change classHomologyEquiv A L M (d.symm (DerivedCategory.Q.map t)) = _
  rw [← hd t, Equiv.symm_apply_apply]
  rfl

/-- Normalized stage identifications and chain representability, before restriction to U.
Source: Stacks Project, Proposition 36.9.5, Tag 08DD, the derived-Hom identification;
Lemma 36.3.5, Tag 06Z0, and More on Algebra, Lemma 15.75.2.
(blueprint: lem-sc-koszul-open-hom-chain-representatives).

Proof: Let L be the extended module Koszul tail and M the top-sections complex of F.
Each term of L is a finite free exterior power, or zero outside the negative tail.
Thus L is bounded above with projective terms and is K-projective. Its derived maps
into M are homotopy classes of chain maps. The affine equivalence identifies these
with maps from Q(tilde L) into Q(F): the termwise tilde/sections counit is an iso
because every F.X n is quasi-coherent. The ordinary adjunction on complexes takes
a sheaf chain map t to exactly koszulOpenHomTranspose t. Degree-zero cycles of the
module Hom complex are chain maps and boundaries are null-homotopic maps. Quotient
by boundaries, then transport through koszulCechHomObjIso and the localization/homology
iso. This gives a, with the displayed normalization, and also proves surjectivity of
Q on maps from this tail to F. For r=0 the positive exterior powers are zero; both
Hom and Hom-complex homology vanish. Zero rings and zero complexes give the same
identification, without any nonzero or boundedness assumption on F. -/
theorem koszulOpenHom_chain_representatives
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let D := koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)
    ∃ a : ∀ e : ℕ, (koszulOpenObject A r f e ⟶ DerivedCategory.Q.obj F) ≃
        H.obj (DerivedCategory.Q.obj (D.obj e)),
      (∀ (e : ℕ) (t : koszulOpenSheafComplex A r f e ⟶ F),
        a e (DerivedCategory.Q.map t) = koszulOpenHomStageClass A r f F e t) ∧
      ∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ DerivedCategory.Q.obj F),
        ∃ t : koszulOpenSheafComplex A r f e ⟶ F, DerivedCategory.Q.map t = φ := by
  classical
  let : (tilde.functor (.of A)).Additive :=
    ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
  let : (moduleSpecΓFunctor (R := .of A)).Additive :=
    ⟨fun {_ _} _ _ ↦ rfl⟩
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let L (e : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
    (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
  have ht (e n : ℕ) : Projective ((koszulOpenTail A r f e).X n) := by
    change Projective (ModuleCat.of A (⋀[A]^(n + 1) (Fin r →₀ A)))
    infer_instance
  let (e : ℕ) (n : ℕ) : Projective ((koszulOpenTail A r f e).X n) := ht e n
  let (e : ℕ) : (L e).IsKProjective := by dsimp [L]; infer_instance
  obtain ⟨b, hb⟩ := Classical.skolem.mp
    (fun e ↦ affineComplexHom_transpose A (L e) F hF)
  obtain ⟨c, hc⟩ := Classical.skolem.mp (fun e ↦ moduleHomDerived_class A (L e) M)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let K (e : ℕ) := CochainComplex.moduleHomComplex (L e) M
  let j (e : ℕ) :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app (K e)
  let k (e : ℕ) := H.mapIso (DerivedCategory.Q.mapIso (koszulCechHomObjIso A r f M e))
  let a (e : ℕ) := (b e).trans ((c e).trans
    ((j e).symm.toLinearEquiv.toEquiv.trans (k e).symm.toLinearEquiv.toEquiv))
  refine ⟨a, ?_, ?_⟩
  · intro e t
    change (k e).inv ((j e).inv (c e (b e (DerivedCategory.Q.map t)))) = _
    rw [hb e, hc e]
    rfl
  · intro e φ
    obtain ⟨s, hs⟩ := CochainComplex.IsKProjective.exists_Q_map_eq (L e) M (b e φ)
    let t := (((tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)).homEquiv
      (L e) F).symm s
    refine ⟨t, (b e).injective ?_⟩
    rw [hb e]
    simpa only [t, Equiv.apply_symm_apply] using hs

end
end AlgebraicGeometry
