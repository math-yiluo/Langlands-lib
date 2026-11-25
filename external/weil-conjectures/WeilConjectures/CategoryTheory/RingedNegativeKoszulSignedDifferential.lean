/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.RingedNegativeKoszulBasisUnitor
import WeilConjectures.CategoryTheory.SignedKoszulSummandDifferential

/-! # Signed differential of the canonical negative Koszul basis

Source: Stacks Project, More on Algebra, Tags 0622 and 0664; Algebraization, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

attribute [local irreducible] ringedKoszulScalar ringedNegativeKoszulFactor
  ringedNegativeKoszulBasis ringedNegativeKoszul

private def endSections
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) :
    End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) →+*
        RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat) where
  toFun f := ⟨(SheafOfModules.unitHomEquiv _ f.asHom).val,
    (SheafOfModules.unitHomEquiv _ f.asHom).property⟩
  map_one' := by ext V; rfl
  map_zero' := by ext V; rfl
  map_add' f g := by ext V; rfl
  map_mul' f g := by
    ext V
    let φ : O.obj.obj V →ₗ[O.obj.obj V] O.obj.obj V := (f.asHom.val.app V).hom
    let ψ : O.obj.obj V →ₗ[O.obj.obj V] O.obj.obj V := (g.asHom.val.app V).hom
    change φ (ψ 1) = φ 1 * ψ 1
    simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using φ.map_smul (ψ 1) (1 : O.obj.obj V)

private theorem coefficient_source
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    {M : ringedSiteModules ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)}
    (c : A) (f : SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O) ⟶ M) :
    ringedKoszulCoefficientSMul O ((endSections O).comp ρ) c f = (ρ c).asHom ≫ f := by
  let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.homLinear O.obj
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O).property
  have hid : ((endSections O).comp ρ) c • 𝟙 _ = (ρ c).asHom := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let φ : O.obj.obj V →ₗ[O.obj.obj V] O.obj.obj V := (ρ c).asHom.val.app V |>.hom
    change φ 1 * (show O.obj.obj V from x) = φ x
    simpa only [smul_eq_mul, mul_one, mul_comm] using (φ.map_smul x 1).symm
  change ((endSections O).comp ρ) c • f = _
  rw [← Category.id_comp f, ← Linear.smul_comp, hid, Category.id_comp]

private theorem single_transport
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (p t : ℤ) (hp : p = 0) (ht : t = 0)
    (h : p = t) :
    (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O))
        p hp).inv ≫ ((ringedSiteRingComplex O).XIsoOfEq h).hom =
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O))
        t ht).inv := by
  subst p
  subst t
  simp

private theorem negative_basis_d_signed
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    (r : ℕ) (a : Fin r → A) (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
    let s : Fin r → (O.obj ⋙ forget CommRingCat).sections := fun i ↦
      ⟨(endSections O (ρ (a i))).val, (endSections O (ρ (a i))).property⟩
    ringedNegativeKoszulBasis O r s n I.1 q ≫
        (ringedNegativeKoszul O r s n).d q (q + 1) =
      ∑ i ∈ I.1, (ρ ((-1 : A) ^ (I.1.filter (fun j ↦ j < i)).card * a i ^ (n + 1))).asHom ≫
        ringedNegativeKoszulBasis O r s n (I.1.erase i) (q + 1) := by
  classical
  let ρS := (endSections O).comp ρ
  let s : Fin r → (O.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ ⟨(ρS (a i)).val, (ρS (a i)).property⟩
  change ringedNegativeKoszulBasis O r s n I.1 q ≫
      (ringedNegativeKoszul O r s n).d q (q + 1) = _
  cases r with
  | zero =>
    have hI : I.1 = ∅ := Subsingleton.elim _ _
    have hq : q = 0 := by simpa [hI] using I.2
    subst q
    have hd : (ringedNegativeKoszul O 0 s n).d 0 1 = 0 := by
      unfold ringedNegativeKoszul
      rfl
    simp only [hI, Finset.sum_empty]
    change ringedNegativeKoszulBasis O 0 s n ∅ 0 ≫
      (ringedNegativeKoszul O 0 s n).d 0 1 = 0
    rw [hd, comp_zero]
  | succ r =>
    let := SheafOfModules.isGrothendieckAbelian
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
        (ringedSiteModules ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.homLinear O.obj
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O).property
    let M := SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    let K := ringedSiteRingComplex O
    let N := ringedNegativeKoszul O (r + 1) s n
    let l := HomologicalComplex.leftUnitor N
    have hc : q + (I.1.card : ℤ) = 0 := by have hI := I.2; omega
    let eI := HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M (q + I.1.card) hc
    have hb := ringedNegativeKoszulBasis_leftUnitor O ρS (r + 1) a n q I
    have hD₁ : HomologicalComplex.mapBifunctor.D₁ K N
        (MonoidalCategory.curriedTensor _) (.up ℤ) q (q + 1) = 0 := by
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p t h
      rw [HomologicalComplex.mapBifunctor.ι_D₁, comp_zero]
      exact HomologicalComplex.unit_tensor_d₁ N p t (q + 1)
    have hd := ringedNegativeKoszulSummand_D₂_succ O ρS r a n K q I.1
    apply (cancel_mono (l.inv.f (q + 1))).1
    calc
      _ = eI.inv ≫ ringedNegativeKoszulSummand O ρS a n K q I.1 ≫
          (HomologicalComplex.mapBifunctor K N (MonoidalCategory.curriedTensor _)
            (.up ℤ)).d q (q + 1) := by
        rw [Category.assoc, ← l.inv.comm, ← Category.assoc, hb, Category.assoc]
        rfl
      _ = eI.inv ≫ ringedNegativeKoszulSummand O ρS a n K q I.1 ≫
          HomologicalComplex.mapBifunctor.D₂ K N
            (MonoidalCategory.curriedTensor _) (.up ℤ) q (q + 1) := by
        rw [HomologicalComplex.mapBifunctor.d_eq, hD₁, zero_add]
      _ = _ := by
        rw [hd]
        simp only [Preadditive.comp_sum, Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro i hi
        have he : q + 1 = -((I.1.erase i).card : ℤ) := by
          have hcard : (I.1.erase i).card = I.1.card - 1 :=
            Finset.card_erase_of_mem hi
          have hI : q = -(I.1.card : ℤ) := I.2
          have hpos : 0 < I.1.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega
        have hdeg : q + (I.1.card : ℤ) = (q + 1) + ((I.1.erase i).card : ℤ) := by
          omega
        let eE := HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M
          ((q + 1) + ((I.1.erase i).card : ℤ)) (by omega)
        have ht : eI.inv ≫ (K.XIsoOfEq hdeg).hom = eE.inv :=
          single_transport O _ _ hc (by omega) hdeg
        have hpar : Even (q + (I.1.card : ℤ)) := by rw [hc]; exact Even.zero
        erw [dite_eq_left hdeg]
        simp only [ite_eq_left hpar, one_mul]
        rw [← Category.assoc]
        change (eI.inv ≫ (ρS _ • (K.XIsoOfEq hdeg).hom)) ≫ _ = _
        rw [Linear.comp_smul, ht]
        have hs := coefficient_source O ρ
          ((-1 : A) ^ (I.1.filter (fun j ↦ j < i)).card * a i ^ (n + 1)) eE.inv
        change (ρS _ • eE.inv) = _ at hs
        rw [hs]
        simp only [Category.assoc]
        erw [ringedNegativeKoszulBasis_leftUnitor O ρS (r + 1) a n (q + 1) ⟨I.1.erase i, he⟩]

/-- The canonical negative pure tensor has the signed erased-index boundary.

Source: Stacks Project, More on Algebra, Tags 0622 and 0664, contraction on ordered
Koszul generators and the graded tensor Leibniz rule; Algebraization, Tag 0A0E,
lemma-derived-completion-koszul, the finite free calculation.
(auxiliary; not a blueprint node).

Proof: evaluate endomorphisms of the regular module sheaf at one to construct a
ring homomorphism into the ring of global sections. A module endomorphism sends
x to x times its value at one, so scalar action by this section is precomposition
by the original endomorphism. The supplied compatibility identifies the sections
of all generators with s. Tensor O[0] with the negative Koszul complex. Its first
total differential is zero. Apply ringedNegativeKoszulSummand_D₂_succ to its second
one: the coefficient degree q+card I is zero, so that sign is positive, and the
remaining sign counts selected indices before i. The coefficient is a_i^(n+1).
The left unitor identifies the specified summand, preceded by the inverse
single-complex identification, with the canonical basis vector. Naturality of
scalar action and equality transports therefore converts the summand formula
into the displayed boundary. For no factors the complex is O[0] with zero
differential and the selected subset is empty. No scalar is inverted, so zero
rings, empty sites, and zero or unit sections are included. -/
theorem ringedNegativeKoszulBasis_signed_d
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    (r : ℕ) (a : Fin r → A)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hρ : ∀ i, ρ (a i) = ringedKoszulScalar O (s i))
    (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
    ringedNegativeKoszulBasis O r s n I.1 q ≫
        (ringedNegativeKoszul O r s n).d q (q + 1) =
      ∑ i ∈ I.1, (ρ ((-1 : A) ^ (I.1.filter (fun j ↦ j < i)).card * a i ^ (n + 1))).asHom ≫
        ringedNegativeKoszulBasis O r s n (I.1.erase i) (q + 1) := by
  classical
  let s' : Fin r → (O.obj ⋙ forget CommRingCat).sections := fun i ↦
    ⟨(endSections O (ρ (a i))).val, (endSections O (ρ (a i))).property⟩
  have hs : s' = s := by
    funext i
    have h := congrArg (SheafOfModules.unitHomEquiv _) (congrArg End.asHom (hρ i))
    apply Subtype.ext
    change (SheafOfModules.unitHomEquiv _ (ρ (a i)).asHom).val = (s i).val
    simpa only [ringedKoszulScalar, Equiv.apply_symm_apply] using
      congrArg Subtype.val h
  rw [← hs]
  change ringedNegativeKoszulBasis O r s' n I.1 q ≫
      (ringedNegativeKoszul O r s' n).d q (q + 1) = _
  exact negative_basis_d_signed O ρ r a n q I

end CategoryTheory
