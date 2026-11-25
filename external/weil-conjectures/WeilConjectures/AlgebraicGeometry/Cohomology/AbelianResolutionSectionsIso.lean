/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Section homology of an injective resolution

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2, the identification of
resolution-section cohomology with sheaf cohomology.
(blueprint: new-abelian-resolution-sections-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev sectionFunctor (X : Scheme.{u}) :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))

private noncomputable def sectionHomEquiv {X : Scheme.{u}}
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) ≃+ G.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).homAddEquiv _ G).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private theorem sectionHomEquiv_apply {X : Scheme.{u}}
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) :
    sectionHomEquiv G a =
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ a) (ULift.up 1) := by
  rfl

private theorem sectionHomEquiv_naturality {X : Scheme.{u}}
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) (f : G ⟶ G') :
    sectionHomEquiv G' (a ≫ f) = (sectionFunctor X).map f (sectionHomEquiv G a) := by
  simp only [sectionHomEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def homSectionsComplexIso {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))) I.cochainComplex ≅
      (((sectionFunctor X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans
      (sectionHomEquiv (I.cochainComplex.X n))).toAddCommGrpIso)
    (fun n m _ ↦ by
      ext x
      obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
        x n (zero_add n)
      change (sectionFunctor X).map (I.cochainComplex.d n m)
        (sectionHomEquiv _
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n)))) =
        sectionHomEquiv _
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add m)
            (CochainComplex.HomComplex.δ n m
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add n))))
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk a (zero_add n) m m
        (zero_add m),
        CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
        CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      exact (sectionHomEquiv_naturality a (I.cochainComplex.d n m)).symm)

/-- Section homology computes Ext from the constant integer sheaf, with its
specified cocycle formula.

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: new-abelian-resolution-sections-iso)

Proof: The constant-sheaf adjunction, followed by evaluation at the generator
of the lifted integers, is an additive bijection from morphisms out of the
constant integer sheaf to global sections. Naturality identifies the induced
differentials. Extend the resolution by zero to integer degrees; the Hom complex
from the sheaf placed in degree zero then has the same cycles and boundaries as
the section complex in every nonnegative degree. Hence this additive bijection
induces an additive isomorphism of cohomology groups. Compose its inverse with
InjectiveResolution.extAddEquivCohomologyClass.symm to obtain the displayed
isomorphism. The lemma extEquivCohomologyClass_extMk computes it on representatives;
monicity of iCycles identifies the representative with z. This formula determines
the isomorphism, since homologyπ is surjective. The construction works in degree
zero (there are no incoming boundaries), for the zero sheaf, and on the empty
space as well. No cover or quasi-isomorphism hypothesis is involved. -/
theorem exists_abelianResolutionSectionsIso
    {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ) :
    ∃ e : (abelianCechSections I).homology q ≅
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F,
      ∀ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I).cycles q),
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I).iCycles q z →
        e.hom ((abelianCechSections I).homologyπ q z) = I.extMk a (q + 1) rfl ha := by
  classical
  let K₀ := (CochainComplex.singleFunctor _ 0).obj
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
  let K := CochainComplex.HomComplex K₀ I.cochainComplex
  let A := abelianCechSections I
  let d : K ≅ A.extend ComplexShape.embeddingUpNat :=
    homSectionsComplexIso I ≪≫
      I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (sectionFunctor X)
  let e₀ : K.homology (q : ℤ) ≅
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F :=
    ((CochainComplex.HomComplex.homologyAddEquiv K₀ I.cochainComplex (q : ℤ)).trans
      I.extAddEquivCohomologyClass.symm).toAddCommGrpIso
  let e := (A.extendHomologyIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).symm ≪≫
    HomologicalComplex.homologyMapIso d.symm (q : ℤ) ≪≫ e₀
  refine ⟨e, ?_⟩
  intro a ha z hz
  let v := CochainComplex.HomComplex.Cocycle.fromSingleMk
    (a ≫ (I.cochainComplexXIso q q rfl).inv) (zero_add (q : ℤ))
    (q + 1 : ℤ) (by omega)
    (by simp [I.cochainComplex_d (q : ℤ) (q + 1 : ℤ) q (q + 1) rfl (by simp), reassoc_of% ha])
  let zK := (CochainComplex.HomComplex.leftHomologyData K₀ I.cochainComplex
    (q : ℤ)).cyclesIso.inv v
  have hclass : e₀.hom (K.homologyπ (q : ℤ) zK) = I.extMk a (q + 1) rfl ha := by
    change I.extAddEquivCohomologyClass.symm
      (CochainComplex.HomComplex.homologyAddEquiv K₀ I.cochainComplex (q : ℤ)
        (K.homologyπ (q : ℤ) zK)) = _
    have hπ := (CochainComplex.HomComplex.leftHomologyData K₀ I.cochainComplex
      (q : ℤ)).homologyπ_comp_homologyIso_hom
    have hv := ConcreteCategory.congr_hom hπ zK
    change CochainComplex.HomComplex.homologyAddEquiv K₀ I.cochainComplex (q : ℤ)
      (K.homologyπ (q : ℤ) zK) =
      CochainComplex.HomComplex.CohomologyClass.mk
        ((CochainComplex.HomComplex.leftHomologyData K₀ I.cochainComplex
          (q : ℤ)).cyclesIso.hom zK) at hv
    rw [hv]
    simp only [zK, ← ConcreteCategory.comp_apply, Iso.inv_hom_id, CategoryTheory.id_apply]
    rfl
  have hd : (HomologicalComplex.cyclesMap d.hom (q : ℤ)) zK =
      (A.extendCyclesIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).inv z := by
    apply (AddCommGrpCat.mono_iff_injective
      ((A.extend ComplexShape.embeddingUpNat).iCycles (q : ℤ))).1 inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
    have hv := ConcreteCategory.congr_hom
      (CochainComplex.HomComplex.leftHomologyData K₀ I.cochainComplex
        (q : ℤ)).cyclesIso_inv_comp_iCycles v
    change K.iCycles (q : ℤ) zK = v.val at hv
    rw [hv]
    have hzA := ConcreteCategory.congr_hom
      (A.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat
        (j' := (q : ℤ)) rfl) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hzA
    rw [hzA]
    change (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
      (sectionFunctor X)).hom.f (q : ℤ)
      (sectionHomEquiv (I.cochainComplex.X q)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (q : ℤ))
          (CochainComplex.HomComplex.Cochain.fromSingleMk
            (a ≫ (I.cochainComplexXIso q q rfl).inv) (zero_add (q : ℤ))))) = _
    rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
      sectionHomEquiv_naturality]
    have hm : (sectionFunctor X).map (I.cochainComplexXIso q q rfl).inv ≫
        (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
          (sectionFunctor X)).hom.f (q : ℤ) =
        (A.extendXIso ComplexShape.embeddingUpNat (i' := (q : ℤ)) (i := q) rfl).inv := by
      have hr : ComplexShape.embeddingUpNat.r (q : ℤ) = some q :=
        ComplexShape.embeddingUpNat.r_f q
      change (sectionFunctor X).map
        (I.cocomplex.extendXIso ComplexShape.embeddingUpNat
          (i' := (q : ℤ)) (i := q) rfl).inv ≫
        (HomologicalComplex.mapExtendX I.cocomplex (sectionFunctor X)
          (ComplexShape.embeddingUpNat.r (q : ℤ))).hom = _
      rw [HomologicalComplex.mapExtendX_hom_eq I.cocomplex (sectionFunctor X) hr]
      simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
    calc
      _ = ((sectionFunctor X).map (I.cochainComplexXIso q q rfl).inv ≫
          (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
            (sectionFunctor X)).hom.f (q : ℤ)) (sectionHomEquiv _ a) := rfl
      _ = (A.extendXIso ComplexShape.embeddingUpNat
          (i' := (q : ℤ)) (i := q) rfl).inv (sectionHomEquiv _ a) := by rw [hm]; rfl
      _ = _ := by rw [sectionHomEquiv_apply, hz]
  have hd' : HomologicalComplex.cyclesMap d.inv (q : ℤ)
      ((A.extendCyclesIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).inv z) =
      zK := by
    rw [← hd, ← ConcreteCategory.comp_apply, ← HomologicalComplex.cyclesMap_comp]
    simp
  have hhom : e.hom (A.homologyπ q z) = e₀.hom (K.homologyπ (q : ℤ) zK) := by
    have hπ₁ := ConcreteCategory.congr_hom
      (A.homologyπ_extendHomologyIso_inv ComplexShape.embeddingUpNat
        (j' := (q : ℤ)) rfl) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hπ₁
    have hπ₂ := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality d.inv (q : ℤ))
      ((A.extendCyclesIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).inv z)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hπ₂
    change e₀.hom (HomologicalComplex.homologyMap d.inv (q : ℤ)
      ((A.extendHomologyIso ComplexShape.embeddingUpNat (j' := (q : ℤ)) rfl).inv
        (A.homologyπ q z))) = _
    rw [hπ₁, hπ₂, hd']
  exact hhom.trans hclass

end AlgebraicGeometry.Scheme.Modules
