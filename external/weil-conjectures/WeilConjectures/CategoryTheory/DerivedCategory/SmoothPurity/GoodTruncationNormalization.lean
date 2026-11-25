/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedDegreeZeroNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# Good-truncation normalization and exact functors

Source: Stacks Project, Homology, Tags 0118 and 010N; Derived Categories,
Tags 06XS and 015F (blueprint: lem-pur-good-truncation-exact-normalization).

The projection is constructed using the cycles-to-homology quotient. The normalization
is selected from the landed uniqueness theorem
`DerivedCategory.existsUnique_iso_single_homology_zero`
(blueprint: lem-amb-derived-degree-zero-normalization), not from an undetermined
existence statement.
The comparisons for exact functors, identities and composition are the existing termwise
localization comparisons. All category and localization universes are independent.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] in
private theorem truncation_cycles_inclusion (A : CochainComplex C ℤ) :
    (A.truncLEXIsoCycles 0).hom ≫ A.iCycles 0 = (A.ιTruncLE 0).f 0 := by
  apply Quiver.Hom.op_inj
  change (A.iCycles 0).op ≫ (A.opcyclesOpIso 0).inv ≫
      (A.op.truncGEXIsoOpcycles (ComplexShape.embeddingUpIntLE 0).op
        (i := 0) (by simp)
        (by simpa using ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl))).inv =
    (A.op.πTruncGE (ComplexShape.embeddingUpIntLE 0).op).f 0
  dsimp only [HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ (show
    (ComplexShape.embeddingUpIntLE 0).op.f 0 = 0 by simp)]
  rw [HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    _ _ rfl (by simpa using
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl))]
  simp only [HomologicalComplex.truncGEXIsoOpcycles, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  have hop : (A.iCycles 0).op ≫ (A.opcyclesOpIso 0).inv = A.op.pOpcycles 0 := by
    apply (cancel_mono (A.opcyclesOpIso 0).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (A.sc 0).op_pOpcycles_opcyclesOpIso_hom.symm
  erw [reassoc_of% hop]
  rfl

set_option linter.unusedSectionVars false in
/-- The quotient of cycles kills the incoming differential of the good truncation.
Source: Stacks Tag 0118 (blueprint: lem-pur-good-truncation-exact-normalization).
Proof: the degree-zero truncation term is the kernel of d⁰. The incoming differential
is d⁻¹ factored through that kernel, and the homology quotient kills its image.
This is Step 1 of the node's proof; it applies to every complex, without concentration. -/
theorem goodTruncationProjection_condition (A : CochainComplex C ℤ) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel i 0) :
    (A.truncLE 0).d i 0 ≫ (A.truncLEXIsoCycles 0).hom ≫ A.homologyπ 0 = 0 := by
  obtain rfl : i = -1 := by
    change i + 1 = 0 at hi
    omega
  have hd : (A.truncLE 0).d (-1) 0 ≫ (A.truncLEXIsoCycles 0).hom =
      (A.ιTruncLE 0).f (-1) ≫ A.toCycles (-1) 0 := by
    apply (cancel_mono (A.iCycles 0)).mp
    rw [Category.assoc, truncation_cycles_inclusion, Category.assoc, HomologicalComplex.toCycles_i]
    exact ((A.ιTruncLE 0).comm (-1) 0).symm
  rw [← Category.assoc, hd, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ,
    comp_zero]

/-- The specified projection τ≤⁰ A → H⁰(A)[0], with the cycles quotient at zero and
zero components elsewhere. Source: Stacks Tag 0118
(blueprint: lem-pur-good-truncation-exact-normalization). -/
noncomputable def goodTruncationProjection (A : CochainComplex C ℤ) :
    A.truncLE 0 ⟶ (CochainComplex.singleFunctor C 0).obj (A.homology 0) :=
  HomologicalComplex.mkHomToSingle
    ((A.truncLEXIsoCycles 0).hom ≫ A.homologyπ 0)
    (goodTruncationProjection_condition A)

/-- The representative-independent good-truncation normalization ε_K: the unique
isomorphism whose H⁰ map, followed by the single-cohomology comparison, is the identity.
It is selected from the uniqueness theorem `existsUnique_iso_single_homology_zero`
(blueprint: lem-amb-derived-degree-zero-normalization), which fixes the morphism.
Source: Stacks Tags 0118 and 06XS(2)
(blueprint: lem-pur-good-truncation-exact-normalization). -/
noncomputable def goodTruncationNormalization (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)) :
    K ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj K) :=
  Classical.choose (existsUnique_iso_single_homology_zero K hK).exists

private theorem normalization_homology (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)) :
    (homologyFunctor C 0).map (goodTruncationNormalization K hK).hom ≫
      (singleFunctorCompHomologyFunctorIso C 0).hom.app ((homologyFunctor C 0).obj K) =
      𝟙 _ :=
  (Classical.choose_spec (existsUnique_iso_single_homology_zero K hK).exists)

private theorem homology_injective_single {M N : C}
    {f g : (singleFunctor C 0).obj M ⟶ (singleFunctor C 0).obj N}
    (h : (homologyFunctor C 0).map f = (homologyFunctor C 0).map g) : f = g := by
  obtain ⟨a, rfl⟩ := (singleFunctor C 0).map_surjective f
  obtain ⟨b, rfl⟩ := (singleFunctor C 0).map_surjective g
  have : (singleFunctor C 0 ⋙ homologyFunctor C 0).Faithful :=
    CategoryTheory.Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso C 0).symm
  exact congrArg ((singleFunctor C 0).map)
    ((singleFunctor C 0 ⋙ homologyFunctor C 0).map_injective h)

private theorem homology_injective {K L : DerivedCategory C} {M N : C}
    (eK : K ≅ (singleFunctor C 0).obj M) (eL : L ≅ (singleFunctor C 0).obj N)
    {f g : K ⟶ L} (h : (homologyFunctor C 0).map f = (homologyFunctor C 0).map g) :
    f = g := by
  apply (cancel_epi eK.inv).mp
  apply (cancel_mono eL.hom).mp
  apply homology_injective_single
  simp only [CategoryTheory.Functor.map_comp, h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem projection_homology (A : CochainComplex C ℤ) :
    HomologicalComplex.homologyMap (goodTruncationProjection A) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (A.homology 0)).hom =
      HomologicalComplex.homologyMap (A.ιTruncLE 0) 0 := by
  have hcyc : (A.truncLE 0).iCycles 0 ≫ (A.truncLEXIsoCycles 0).hom =
      HomologicalComplex.cyclesMap (A.ιTruncLE 0) 0 := by
    apply (cancel_mono (A.iCycles 0)).mp
    simp only [Category.assoc, truncation_cycles_inclusion, HomologicalComplex.cyclesMap_i]
  apply (cancel_epi ((A.truncLE 0).homologyπ 0)).mp
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc]
  erw [HomologicalComplex.cyclesMap_i]
  erw [goodTruncationProjection, HomologicalComplex.mkHomToSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hcyc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem projection_derived_homology (A : CochainComplex C ℤ) :
    (homologyFunctor C 0).map (Q.map (goodTruncationProjection A)) ≫
      (singleFunctorCompHomologyFunctorIso C 0).hom.app (A.homology 0) =
    (homologyFunctor C 0).map (Q.map (A.ιTruncLE 0)) ≫
      (homologyFunctorFactors C 0).hom.app A := by
  have hs : (singleFunctorCompHomologyFunctorIso C 0).hom.app (A.homology 0) =
      (homologyFunctorFactors C 0).hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj (A.homology 0)) ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (A.homology 0)).hom := by
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj,
      singleFunctorCompHomologyFunctorIso, Iso.trans_hom,
      CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.mapIso_hom,
      SingleFunctors.evaluation_map, singleFunctorsPostcompQIso_hom_hom,
      CategoryTheory.Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      CategoryTheory.Functor.whiskerRight_app, NatTrans.id_app,
      CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.whiskerLeft_app,
      HomologicalComplex.homologyFunctorSingleIso_hom_app, Q_obj_single_obj]
    erw [(homologyFunctor C 0).map_id, Category.id_comp, Category.id_comp]
  rw [hs]
  erw [homologyFunctorFactors_hom_naturality_assoc,
    homologyFunctorFactors_hom_naturality, projection_homology]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Both arrows in the specified roof are quasi-isomorphisms, and every representative
isomorphism r gives the same ε_K. The equation is the roof formula multiplied by Q(c_A).
Source: Stacks Tags 0118 and 06XS(2)
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof: Step 1 computes Hⁿ(c_A): it is the identity in retained degrees, and the other
cohomology vanishes by hK and the representative isomorphism. The projection has the
identity quotient map on H⁰ and zero cohomology in other degrees. Both arrows are
quasi-isomorphisms. Localize and transport the roof along r; its action on H⁰ is the
identity. The uniqueness theorem, as in Steps 2--3, identifies it with ε_K, independently
of A and r and of kernel/quotient models under their canonical identifications. -/
theorem goodTruncationNormalization_roof (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (A : CochainComplex C ℤ) (r : Q.obj A ≅ K) :
    QuasiIso (A.ιTruncLE 0) ∧ QuasiIso (goodTruncationProjection A) ∧
      Q.map (A.ιTruncLE 0) ≫ r.hom ≫ (goodTruncationNormalization K hK).hom =
        Q.map (goodTruncationProjection A) ≫
          (singleFunctorIsoCompQ C 0).inv.app (A.homology 0) ≫
          (singleFunctor C 0).map
            ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom) := by
  have hA (n : ℤ) (hn : n ≠ 0) : IsZero (A.homology n) :=
    (hK n hn).of_iso
      ((homologyFunctorFactors C n).symm.app A ≪≫ (homologyFunctor C n).mapIso r)
  have : A.IsLE 0 := (CochainComplex.isLE_iff A 0).2 (fun n hn ↦
    (HomologicalComplex.exactAt_iff_isZero_homology A n).2 (hA n (ne_of_gt hn)))
  have hc : QuasiIso (A.ιTruncLE 0) := inferInstance
  have : IsIso (Q.map (A.ιTruncLE 0)) := by infer_instance
  let eT := asIso (Q.map (A.ιTruncLE 0)) ≪≫ r ≪≫ goodTruncationNormalization K hK
  have heq : Q.map (A.ιTruncLE 0) ≫ r.hom ≫ (goodTruncationNormalization K hK).hom =
      Q.map (goodTruncationProjection A) ≫
        (singleFunctorIsoCompQ C 0).inv.app (A.homology 0) ≫
        (singleFunctor C 0).map
          ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom) := by
    apply homology_injective eT (Iso.refl _)
    apply (cancel_mono ((singleFunctorCompHomologyFunctorIso C 0).hom.app
      ((homologyFunctor C 0).obj K))).mp
    simp only [singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app]
    simp only [(homologyFunctor C 0).map_comp, Category.assoc,
      normalization_homology, Category.comp_id]
    have hn := (singleFunctorCompHomologyFunctorIso C 0).hom.naturality
      ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom)
    dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
    erw [hn, (homologyFunctor C 0).map_id, Category.id_comp]
    rw [← Category.assoc]
    erw [projection_derived_homology]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  refine ⟨hc, ?_, heq⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have : IsIso ((singleFunctor C 0).map
      ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom)) := by
    infer_instance
  have : IsIso (Q.map (goodTruncationProjection A) ≫
      (singleFunctorIsoCompQ C 0).inv.app (A.homology 0) ≫
      (singleFunctor C 0).map
        ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom)) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_right (Q.map (goodTruncationProjection A))
    ((singleFunctorIsoCompQ C 0).inv.app (A.homology 0) ≫
      (singleFunctor C 0).map
        ((homologyFunctorFactors C 0).inv.app A ≫ (homologyFunctor C 0).map r.hom))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality, the H⁰ Hom bijection, and the unique-b characterization for the
specified normalization on the full subcategory with cohomology only in degree zero.
Source: Stacks Tag 06XS(2) (blueprint: lem-pur-good-truncation-exact-normalization).
Proof: Step 2 conjugates by the roofs and uses full faithfulness of the single functor.
Applying H⁰ recovers the unique morphism b. This proves the Hom bijection. In Step 3,
both sides of naturality induce H⁰(a), so injectivity identifies them. Conjugating this
equality and using faithfulness of the single functor proves the equivalence for b.
The inverse family is natural by multiplying by inverses. In the zero category all
Hom sets are singletons and the same argument applies (Step 8). -/
theorem goodTruncationNormalization_naturality_hom
    (K L : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (hL : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj L)) (a : K ⟶ L) :
    a ≫ (goodTruncationNormalization L hL).hom =
      (goodTruncationNormalization K hK).hom ≫
        (singleFunctor C 0).map ((homologyFunctor C 0).map a) ∧
    Function.Bijective (fun f : K ⟶ L ↦ (homologyFunctor C 0).map f) ∧
    ∀ b : (homologyFunctor C 0).obj K ⟶ (homologyFunctor C 0).obj L,
      (singleFunctor C 0).map b =
        (goodTruncationNormalization K hK).inv ≫ a ≫
          (goodTruncationNormalization L hL).hom ↔ b = (homologyFunctor C 0).map a := by
  let eK := goodTruncationNormalization K hK
  let eL := goodTruncationNormalization L hL
  have hk : (homologyFunctor C 0).map eK.hom ≫ (singleFunctorCompHomologyFunctorIso C 0).hom.app
      ((homologyFunctor C 0).obj K) = 𝟙 _ := normalization_homology K hK
  have hl : (homologyFunctor C 0).map eL.hom ≫ (singleFunctorCompHomologyFunctorIso C 0).hom.app
      ((homologyFunctor C 0).obj L) = 𝟙 _ := normalization_homology L hL
  have hli : (homologyFunctor C 0).map eL.inv = (singleFunctorCompHomologyFunctorIso C 0).hom.app
      ((homologyFunctor C 0).obj L) := by
    apply (cancel_epi ((homologyFunctor C 0).map eL.hom)).mp
    rw [← (homologyFunctor C 0).map_comp, eL.hom_inv_id, (homologyFunctor C 0).map_id, hl]
  have hn (b : (homologyFunctor C 0).obj K ⟶ (homologyFunctor C 0).obj L) :
      (homologyFunctor C 0).map ((singleFunctor C 0).map b) ≫ (singleFunctorCompHomologyFunctorIso C
          0).hom.app ((homologyFunctor C 0).obj L) = (singleFunctorCompHomologyFunctorIso C
          0).hom.app ((homologyFunctor C 0).obj K) ≫ b :=
    (singleFunctorCompHomologyFunctorIso C 0).hom.naturality b
  have hi : Function.Injective (fun f : K ⟶ L ↦ (homologyFunctor C 0).map f) :=
    fun _ _ h ↦ homology_injective eK eL h
  have nat : a ≫ eL.hom = eK.hom ≫ (singleFunctor C 0).map ((homologyFunctor C 0).map a) := by
    apply homology_injective eK (Iso.refl _)
    apply (cancel_mono ((singleFunctorCompHomologyFunctorIso C 0).hom.app ((homologyFunctor C 0).obj
        L))).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, hl, Category.comp_id, hn]
    rw [← Category.assoc, hk, Category.id_comp]
  refine ⟨nat, ⟨hi, ?_⟩, ?_⟩
  · intro b
    refine ⟨eK.hom ≫ (singleFunctor C 0).map b ≫ eL.inv, ?_⟩
    change (homologyFunctor C 0).map (eK.hom ≫ (singleFunctor C 0).map b ≫ eL.inv) = b
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hli, hn, ← Category.assoc,
        hk,
      Category.id_comp]
  · intro b
    constructor
    · intro hb
      apply (singleFunctor C 0).map_injective
      rw [hb, nat]
      simp [eK]
    · rintro rfl
      rw [nat]
      simp [eK]

/-- Exact functors preserve the full subcategory with cohomology only in degree zero.
Source: Stacks Tag 015F and Homology Tag 010N
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof (Step 4): lem-weil-pbc-exact-functor-complex-cohomology gives the canonical
kernel/image/quotient comparison on complexes. Descend it using the factorization
and localization universal property (situation-conventions,
lem-weil-pbc-localization-universal-property). In nonzero degrees its source is zero,
since an exact additive functor preserves zero objects. -/
theorem goodTruncationNormalization_exact_concentrated (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K)) :
    ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor D n).obj (F.mapDerivedCategory.obj K)) := by
  intro n hn
  exact (F.map_isZero (hK n hn)).of_iso
    ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
-- The inherited hypothesis on L is retained; χ is natural without concentration.
set_option linter.unusedVariables false in
/-- The roof normalization commutes with the canonical exact-functor comparisons χ and σ;
χ is natural on all derived morphisms in the full subcategory.
Source: Stacks Tags 010N, 0118, 015F
(blueprint: lem-pur-good-truncation-exact-normalization).
Proof: apply H⁰-injectivity between objects identified with single complexes and
postcompose with the single-homology comparison. Naturality of χ on ε_K and the
compatibility of χ with σ on single objects reduce the right-hand side to F applied
to the normalization equation H⁰(ε_K) followed by the single-homology comparison.
This is the identity. Cancel χ_K to obtain the formula. The second equation is
naturality of the canonical exact-functor homology comparison. -/
theorem goodTruncationNormalization_exact (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K L : DerivedCategory C)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj K))
    (hL : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj L)) (a : K ⟶ L) :
    (goodTruncationNormalization (F.mapDerivedCategory.obj K)
      (goodTruncationNormalization_exact_concentrated F K hK)).hom =
      F.mapDerivedCategory.map (goodTruncationNormalization K hK).hom ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app ((homologyFunctor C 0).obj K) ≫
        (singleFunctor D 0).map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K) ∧
    (F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K ≫
        (homologyFunctor D 0).map (F.mapDerivedCategory.map a) =
      F.map ((homologyFunctor C 0).map a) ≫
        (F.mapDerivedCategoryHomologyFunctorIso 0).hom.app L := by
  let e := goodTruncationNormalization K hK
  constructor
  · apply homology_injective
      (goodTruncationNormalization (F.mapDerivedCategory.obj K)
        (goodTruncationNormalization_exact_concentrated F K hK)) (Iso.refl _)
    apply (cancel_mono ((singleFunctorCompHomologyFunctorIso D 0).hom.app
      ((homologyFunctor D 0).obj (F.mapDerivedCategory.obj K)))).mp
    rw [normalization_homology]
    have hs := (singleFunctorCompHomologyFunctorIso D 0).hom.naturality
      ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K)
    dsimp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hs
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hs]
    apply (cancel_epi ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K)).mp
    have hn := (F.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality e.hom
    dsimp only [CategoryTheory.Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [reassoc_of% (F.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0
      ((homologyFunctor C 0).obj K))]
    rw [← F.map_comp_assoc, normalization_homology, F.map_id, Category.id_comp]
    erw [Category.comp_id]
  · exact ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality a).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem short_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (S : ShortComplex C) :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let h := S.homologyData.left
  have hc : ((h.map F).map G).cyclesIso.hom = (h.map (F ⋙ G)).cyclesIso.hom := by
    apply (cancel_mono ((F ⋙ G).map h.i)).1
    change ((h.map F).map G).cyclesIso.hom ≫ ((h.map F).map G).i =
      (h.map (F ⋙ G)).cyclesIso.hom ≫ (h.map (F ⋙ G)).i
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rfl
  have hh : ((h.map F).map G).homologyIso.hom = (h.map (F ⋙ G)).homologyIso.hom := by
    apply (cancel_epi ((S.map (F ⋙ G)).homologyπ)).1
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
    rfl
  rw [h.mapHomologyIso_eq (F ⋙ G), (h.map F).mapHomologyIso_eq G,
    h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
      CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_assoc]
  rw [hh]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (A : CochainComplex C ℤ) (n : ℤ) :
    ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app A =
      (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A) ≫
      G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app A) := by
  rw [CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq,
    CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq,
    CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq]
  exact short_homology_comp F G (A.sc n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem derived_homology_factor (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : CochainComplex C ℤ) (n : ℤ) :
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (Q.obj A) ≫
      (homologyFunctor D n).map (F.mapDerivedCategoryFactors.hom.app A) ≫
      (homologyFunctorFactors D n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A) =
    F.map ((homologyFunctorFactors C n).hom.app A) ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app A := by
  rw [CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc]
  erw [← (homologyFunctor D n).map_comp_assoc, Iso.inv_hom_id_app,
    (homologyFunctor D n).map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem derived_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory C) :
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso 0).hom.app K ≫
        (homologyFunctor E 0).map ((CategoryTheory.Functor.mapDerivedCategoryCompIso F G).inv.app K)
            =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso 0).hom.app (F.mapDerivedCategory.obj K) := by
  let τ₁ := ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso 0).hom ≫
    CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.mapDerivedCategoryCompIso F G).inv
        (homologyFunctor E 0)
  let τ₂ := CategoryTheory.Functor.whiskerRight (F.mapDerivedCategoryHomologyFunctorIso 0).hom G ≫
    CategoryTheory.Functor.whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso
        0).hom
  have h : τ₁ = τ₂ := by
    apply Localization.natTrans_ext Q (HomologicalComplex.quasiIso C (.up ℤ))
    intro A
    dsimp only [τ₁, τ₂, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
      CategoryTheory.Functor.whiskerLeft_app]
    apply (cancel_mono ((homologyFunctor E 0).map
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app A)) ≫
      (homologyFunctor E 0).map (G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A)) ≫
      (homologyFunctorFactors E 0).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj A)))).mp
    have hfac := CategoryTheory.Functor.mapDerivedCategoryCompIso_fac F G A
    have hc : (CategoryTheory.Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (.up ℤ)).hom.app A = 𝟙 _ := rfl
    erw [hc, CategoryTheory.Functor.map_id, Category.comp_id] at hfac
    have hχ := (G.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app A)
    dsimp only [CategoryTheory.Functor.comp_map] at hχ
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Category.assoc, hfac]
    erw [derived_homology_factor]
    erw [← reassoc_of% hχ, derived_homology_factor]
    erw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, derived_homology_factor]
    erw [G.map_comp, Category.assoc]
    congr 1
    apply (cancel_mono (((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) 0).hom.app A)).mp
    erw [Iso.inv_hom_id_app, complex_homology_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    erw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
    rfl
  exact congr_app h K

end DerivedCategory
