/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Canonical Ext/section identification on an injective resolution

Source: Stacks Project, Tag 01EQ, resolution computation of global cohomology,
and Mathlib's InjectiveResolution.extEquivCohomologyClass.
(blueprint: lem-pc-abelian-cech-ext-section-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private noncomputable abbrev integralSheaf (X : Scheme.{u}) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

private noncomputable def sectionEquiv {X : Scheme.{u}}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (integralSheaf X ⟶ F) ≃+ F.obj.obj (op (⊤ : X.Opens)) :=
  ((constantSheafAdj _ _ isTerminalTop).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma sectionEquiv_naturality {X : Scheme.{u}}
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (a : integralSheaf X ⟶ F) :
    sectionEquiv G (a ≫ f) = f.hom.app (op (⊤ : X.Opens)) (sectionEquiv F a) := by
  dsimp only [sectionEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionComplexIso {X : Scheme.{u}}
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor _ 0).obj (integralSheaf X)) K ≅
      (((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans
      (sectionEquiv (K.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ :=
          CochainComplex.HomComplex.Cochain.fromSingleMk_surjective a i (zero_add i)
        change (K.d i j).hom.app (op (⊤ : X.Opens))
          (sectionEquiv (K.X i)
            (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add i)
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)))) =
          sectionEquiv (K.X j) (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
            (CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i))))
        simp only [CochainComplex.HomComplex.Cochain.δ_fromSingleMk, zero_add,
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
        exact (sectionEquiv_naturality (K.d i j) a).symm)

private noncomputable def extendedSectionIso {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor _ 0).obj (integralSheaf X))
        I.cochainComplex ≅ (abelianCechSections I).extend ComplexShape.embeddingUpNat :=
  sectionComplexIso I.cochainComplex ≪≫ I.cocomplex.mapExtendIso
    ComplexShape.embeddingUpNat
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens)))

set_option backward.isDefEq.respectTransparency false in
/-- Ext cohomology is the homology of the section complex, with compatible representatives.
Source: Stacks 01EQ, resolution computation; Mathlib InjectiveResolution.Ext.
(blueprint: lem-pc-abelian-cech-ext-section-iso)

Proof: Apply extAddEquivCohomologyClass to the constant integral sheaf and I.
In every degree the constant-sheaf adjunction followed by evaluation at 1
identifies morphisms from this sheaf with sections over the terminal open.
The inverse sends a section s to the additive map n ↦ n • s and then applies
the inverse adjunction. Naturality of the adjunction shows these mutually
inverse additive maps commute with the resolution differentials. Thus they
identify cycles and boundaries, inducing an additive isomorphism on homology.
Compose it with the Ext equivalence and convert the additive equivalence to
an AddCommGrpCat isomorphism. For t choose a cocycle using extMk_surjective;
the corresponding section is a cycle by differential compatibility. Its
cycle lift z exists by the kernel universal property. The formula for extMk
under extEquivCohomologyClass gives e(t) = homologyπ(z). This also proves that
the representative condition determines e on every class, independently of
choices. In degree zero boundaries vanish; zero sheaves and empty spaces give
zero groups. No open cover or finiteness assumption occurs in this assertion. -/
theorem abelianCechExtSectionIso_exists
    {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ) :
    ∃ (e : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F ≅
        (abelianCechSections I).homology q),
    ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I).cycles q),
        I.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I).iCycles q z ∧
        e.hom t = (abelianCechSections I).homologyπ q z := by
  classical
  -- Compute Ext on the Hom complex and then restrict the section homology to ℕ.
  let P := extendedSectionIso I
  let H := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor _ 0).obj (integralSheaf X)) I.cochainComplex (q : ℤ)
  let E := (abelianCechSections I).extendCyclesIso ComplexShape.embeddingUpNat
    (j := q) rfl
  let e₀ : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F ≅
      AddCommGrpCat.of (CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor _ 0).obj (integralSheaf X)) I.cochainComplex (q : ℤ)) :=
    I.extAddEquivCohomologyClass.toAddCommGrpIso
  let e := e₀ ≪≫ H.homologyIso.symm ≪≫
    HomologicalComplex.homologyMapIso P (q : ℤ) ≪≫
      (abelianCechSections I).extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
  refine ⟨e, ?_⟩
  intro t
  obtain ⟨a, ha, ht⟩ := I.extMk_surjective t (q + 1) rfl
  -- Transport the same cocycle through the cycle isomorphisms defining e.
  let x := CochainComplex.HomComplex.Cocycle.fromSingleMk (a ≫ (I.cochainComplexXIso q q rfl).inv)
    (zero_add (q : ℤ)) (q + 1) (by omega)
      (by
        rw [I.cochainComplex_d _ _ q (q + 1) rfl (by simp)]
        simp [reassoc_of% ha])
  let y := H.cyclesIso.inv x
  let w := HomologicalComplex.cyclesMap P.hom (q : ℤ) y
  let z := E.hom w
  refine ⟨a, ha, z, ht, ?_, ?_⟩
  · have h₁ := ConcreteCategory.congr_hom
      ((abelianCechSections I).extendCyclesIso_hom_iCycles
        ComplexShape.embeddingUpNat (j := q) rfl) w
    have h₂ := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i P.hom (q : ℤ)) y
    have h₃ := ConcreteCategory.congr_hom H.cyclesIso_inv_comp_iCycles x
    simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃
    change (CochainComplex.HomComplex _ I.cochainComplex).iCycles (q : ℤ) y = x.val at h₃
    change _ = (abelianCechSections I).iCycles q (E.hom w)
    rw [h₁]
    change _ = ((abelianCechSections I).extendXIso
      ComplexShape.embeddingUpNat (i := q) rfl).hom
        (((abelianCechSections I).extend ComplexShape.embeddingUpNat).iCycles (q : ℤ) w)
    rw [h₂, h₃]
    change sectionEquiv (I.cocomplex.X q) a =
      ((abelianCechSections I).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom
        ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
          (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
            (op (⊤ : X.Opens)))).hom.f (q : ℤ)
          (sectionEquiv (I.cochainComplex.X q)
            ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (q : ℤ))) x.val)))
    simp only [x, CochainComplex.HomComplex.Cocycle.fromSingleMk_coe,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
    rw [HomologicalComplex.mapExtendIso]
    simp only [HomologicalComplex.Hom.isoOfComponents_hom_f]
    erw [HomologicalComplex.mapExtendX_hom_eq _ _ (ComplexShape.embeddingUpNat.r_f q)]
    simp only [eqToIso.hom]
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom,
      InjectiveResolution.cochainComplexXIso, eqToIso.inv, sectionEquiv_naturality,
      ObjectProperty.eqToHom_hom, eqToHom_app]
    -- The three remaining equality transports compose to the identity.
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    erw [eqToHom_trans, eqToHom_trans]
    rfl
  · have h₁ := ConcreteCategory.congr_hom H.π_comp_homologyIso_inv x
    have h₂ := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality P.hom (q : ℤ)) y
    have h₃ := ConcreteCategory.congr_hom
      ((abelianCechSections I).homologyπ_extendHomologyIso_hom
        ComplexShape.embeddingUpNat (j := q) rfl) w
    simp only [ConcreteCategory.comp_apply] at h₁ h₂ h₃
    change H.homologyIso.inv (CochainComplex.HomComplex.CohomologyClass.mk x) =
      (CochainComplex.HomComplex _ I.cochainComplex).homologyπ (q : ℤ) y at h₁
    have hx : e₀.hom t = CochainComplex.HomComplex.CohomologyClass.mk x := by
      rw [← ht]
      exact I.extEquivCohomologyClass_extMk a (q + 1) rfl ha
    change ((abelianCechSections I).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl).hom
        (HomologicalComplex.homologyMap P.hom (q : ℤ) (H.homologyIso.inv (e₀.hom t))) = _
    rw [hx, h₁, h₂]
    exact h₃

end AlgebraicGeometry.Scheme.Modules
