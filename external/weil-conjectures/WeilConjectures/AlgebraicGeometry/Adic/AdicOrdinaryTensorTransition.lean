/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicOrdinaryTensorDiagram

/-! # The consecutive square for ordinary algebraic quotient tensors

Source: Stacks Project, More on Algebra, Tag 09AW; More on Algebra, Tag 06Y6.
(blueprint: lem-weil-pbc-adic-ordinary-tensor-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

private theorem restrictionComp_factors
    {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ)
    (V : CochainComplex (ModuleCat.{t} (A ⧸ I ^ (n + 1))) ℤ) :
    let U := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
    let S := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))
    let R := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))
    let e := ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc I (n + 1))
      (Ideal.Quotient.mk (I ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm
    (DerivedCategory.adicRestrictionComp I n).hom.app (DerivedCategory.Q.obj V) ≫
        U.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app V) ≫
        U.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj V) =
      R.mapDerivedCategoryFactors.hom.app V ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app V) := by
  dsimp only
  unfold DerivedCategory.adicRestrictionComp DerivedCategory.adicLevelRestriction
    DerivedCategory.adicStepRestriction
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fac
    (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) V
  have hi : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))
      (.up ℤ)).hom.app V = 𝟙 _ := by
    ext j
    rfl
  rw [hi] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  rw [hc]
  exact Functor.mapDerivedCategoryNatIso_fac _ V

private def ordinaryCoefficientMap
    {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1))) ⟶
      ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1))) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1)) := by
  let U := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
  let S := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))
  let e := ModuleCat.restrictScalarsComp'
    (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
    (Ideal.Quotient.factorPowSucc I (n + 1))
    (Ideal.Quotient.mk (I ^ (n + 1)))
    (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm
  let α : 𝟭 (ModuleCat.{t} A) ⟶ F ⋙ S ⋙ U :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ (n + 1)))).unit ≫
      Functor.whiskerLeft F e.hom
  let ad := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
  exact { app := fun M ↦ (ad.homEquiv _ _).symm (α.app M)
          naturality := by
            intro M N f
            apply (ad.homEquiv _ _).injective
            rw [ad.homEquiv_naturality_left, ad.homEquiv_naturality_right]
            simpa only [Equiv.apply_symm_apply, Functor.id_map, Functor.comp_map]
              using α.naturality f }

private theorem ordinaryCoefficientMap_tmul
    {A : Type t} [CommRing A] (I : Ideal A) (n : ℕ)
    (M : ModuleCat.{t} A) (a : A ⧸ I ^ (n + 1 + 1)) (x : M) :
    (ordinaryCoefficientMap I n).app M (a ⊗ₜ[A, Ideal.Quotient.mk _] x) =
      (Ideal.Quotient.factorPowSucc I (n + 1)) a ⊗ₜ[A, Ideal.Quotient.mk _] x := by
  let _ : Module A ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1))) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))).obj M) :=
    Module.compHom _ (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
  change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (Y := ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1))) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))).obj M))
    (Ideal.Quotient.mk (I ^ (n + 1 + 1))) _)
    (a ⊗ₜ[A, Ideal.Quotient.mk _] x) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change (Ideal.Quotient.factorPowSucc I (n + 1)) a •
    ((1 : A ⧸ I ^ (n + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (n + 1))] x) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private theorem ordinaryCoefficientMap_square
    {A : Type t} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (n : ℕ) :
    let U := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
    let V := ((ModuleCat.extendScalars
      (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (.up ℤ)).obj P
    let e := ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc I (n + 1))
      (Ideal.Quotient.mk (I ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm
    (U.mapHomologicalComplex (.up ℤ)).map
        (((ordinaryCoefficientMap I n).mapHomologicalComplex (.up ℤ)).app P) ≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).inv.app V ≫
        (adicOrdinaryQuotientComplexIso I P n).hom =
      (adicOrdinaryQuotientComplexIso I P (n + 1)).hom ≫
        (adicOrdinaryTensorComplexDiagram I P).map (homOfLE (Nat.le_succ n)).op := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul a x =>
    change TensorProduct.comm A _ _ ((ordinaryCoefficientMap I n).app (P.X j)
      (a ⊗ₜ[A, Ideal.Quotient.mk (I ^ (n + 1 + 1))] x)) = _
    rw [ordinaryCoefficientMap_tmul]
    change x ⊗ₜ[A] ((Ideal.Quotient.factorPowSucc I (n + 1)) a) =
      x ⊗ₜ[A] ((adicOrdinaryCoefficientDiagram I).map (homOfLE (Nat.le_succ n)).op a)
    simp only [adicOrdinaryCoefficientDiagram, Functor.ofOpSequence_map_homOfLE_succ]
    rfl

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] adicOrdinaryQuotientComplexIso adicOrdinaryTensorComplexDiagram
attribute [local irreducible] adicOrdinaryTensorLevelMap

/-- The explicitly constructed level maps commute with the consecutive
canonical quotient transition and the ordinary quotient homomorphism.

Source: Stacks Project, Tags 09AW and 0BYK, quotient scalar transitions; Tag 06Y6, the unit
normalization of the scalar-extension representative comparison.
(blueprint: lem-weil-pbc-adic-ordinary-tensor-transition).

Proof: write q_n for A→A/I^(n+1), U_n for its exact restriction, and η_n for the
ordinary cochain scalar-insertion unit. The level comparison is U_n applied to
the transpose of Q(η_n), followed by the exact restriction factorization and the
tensor symmetry. Consequently composing its restricted derived transpose with
the derived unit gives Q(η_n); the two restriction factorization maps cancel.
Transport the displayed square through these exact restriction and symmetry
isomorphisms. Its source is the restriction of L_(n+1)(Q(P)), and its target is
the restriction of the ordinary nth scalar-extension complex. Undo the canonical
isomorphism U_n≅U_(n+1)∘Res(A/I^(n+2)→A/I^(n+1)), and use injectivity of the
(n+1)st adjunction Hom bijection. The transpose of the canonical transition is
its defining lower unit. The other transpose is the localized ordinary quotient
transition composed with scalar insertion. In each cochain degree the latter
sends x to the image of 1 tensor x, namely 1 tensor x, since the quotient ring
homomorphism preserves 1. This is η_n. The equality commutes with differentials
by naturality of insertion. Exact restriction composition and its localization
factorization carry that equality to the required transpose equality, proving
the square. This argument permits arbitrary ideals, zero rings and unbounded
complexes. All level maps have already been constructed without this assertion;
this assertion only identifies their consecutive square. No K-flatness or
invertibility assertion is needed here. -/
theorem adicOrdinaryTensorLevelMap_transition
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (n : ℕ) :
    (finitePerfectAdicQuotientDiagram I L adj (DerivedCategory.Q.obj P)).map
        (homOfLE (Nat.le_succ n)).op ≫
        adicOrdinaryTensorLevelMap I L adj P n =
      adicOrdinaryTensorLevelMap I L adj P (n + 1) ≫
        DerivedCategory.Q.map ((adicOrdinaryTensorComplexDiagram I P).map
          (homOfLE (Nat.le_succ n)).op) := by
  let U (k : ℕ) := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (k + 1)))
  let S := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))
  let V (k : ℕ) := ((ModuleCat.extendScalars
    (Ideal.Quotient.mk (I ^ (k + 1)))).mapHomologicalComplex (.up ℤ)).obj P
  let η (k : ℕ) : P ⟶ ((U k).mapHomologicalComplex (.up ℤ)).obj (V k) :=
    ((ModuleCat.extendRestrictScalarsAdj
      (Ideal.Quotient.mk (I ^ (k + 1)))).mapHomologicalComplex (.up ℤ)).unit.app P
  let e := ModuleCat.restrictScalarsComp'
    (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
    (Ideal.Quotient.factorPowSucc I (n + 1))
    (Ideal.Quotient.mk (I ^ (n + 1)))
    (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm
  let ec : (U n).mapHomologicalComplex (.up ℤ) ≅
      S.mapHomologicalComplex (.up ℤ) ⋙ (U (n + 1)).mapHomologicalComplex (.up ℤ) :=
    NatIso.mapHomologicalComplex e (.up ℤ)
  let v : V (n + 1) ⟶ (S.mapHomologicalComplex (.up ℤ)).obj (V n) :=
    ((ordinaryCoefficientMap I n).mapHomologicalComplex (.up ℤ)).app P
  let c : (U n).mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ (U (n + 1)).mapDerivedCategory :=
    DerivedCategory.adicRestrictionComp I n
  let τ : (L (n + 1)).obj (DerivedCategory.Q.obj P) ⟶
      S.mapDerivedCategory.obj ((L n).obj (DerivedCategory.Q.obj P)) :=
    finitePerfectAdicQuotientTransition I L adj (DerivedCategory.Q.obj P) n
  let r (k : ℕ) : (L k).obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (V k) :=
    ((adj k).homEquiv _ (DerivedCategory.Q.obj (V k))).symm
      (DerivedCategory.Q.map (η k) ≫ (U k).mapDerivedCategoryFactors.inv.app (V k))
  let a (k : ℕ) : (U k).mapDerivedCategory.obj (DerivedCategory.Q.obj (V k)) ⟶
      DerivedCategory.Q.obj ((adicOrdinaryTensorComplexDiagram I P).obj (op k)) :=
    (U k).mapDerivedCategoryFactors.hom.app (V k) ≫
      DerivedCategory.Q.map (adicOrdinaryQuotientComplexIso I P k).hom
  let w : DerivedCategory.Q.obj (V (n + 1)) ⟶
      S.mapDerivedCategory.obj (DerivedCategory.Q.obj (V n)) :=
    DerivedCategory.Q.map v ≫ S.mapDerivedCategoryFactors.inv.app (V n)
  have hu (k : ℕ) : (adj k).unit.app (DerivedCategory.Q.obj P) ≫
      (U k).mapDerivedCategory.map (r k) =
        DerivedCategory.Q.map (η k) ≫ (U k).mapDerivedCategoryFactors.inv.app (V k) :=
    ((adj k).homEquiv _ _).apply_symm_apply _
  have hv : η (n + 1) ≫ ((U (n + 1)).mapHomologicalComplex (.up ℤ)).map v =
      η n ≫ ec.hom.app (V n) := by
    ext j : 1
    exact ((ModuleCat.extendRestrictScalarsAdj
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))).homEquiv _ _).apply_symm_apply _
  have hc := restrictionComp_factors I n (V n)
  dsimp only at hc
  have hw : (U (n + 1)).mapDerivedCategory.map w ≫
      c.inv.app (DerivedCategory.Q.obj (V n)) ≫ a n =
        a (n + 1) ≫ DerivedCategory.Q.map
          ((adicOrdinaryTensorComplexDiagram I P).map (homOfLE (Nat.le_succ n)).op) := by
    have hb : c.inv.app (DerivedCategory.Q.obj (V n)) ≫
        (U n).mapDerivedCategoryFactors.hom.app (V n) =
        (U (n + 1)).mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app (V n)) ≫
          (U (n + 1)).mapDerivedCategoryFactors.hom.app
            ((S.mapHomologicalComplex (.up ℤ)).obj (V n)) ≫
          DerivedCategory.Q.map (ec.inv.app (V n)) := by
      apply (cancel_epi (c.hom.app (DerivedCategory.Q.obj (V n)))).1
      simp only [Iso.hom_inv_id_app_assoc]
      rw [reassoc_of% hc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
        Category.comp_id]
    dsimp only [w, a]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hb]
    rw [← (U (n + 1)).mapDerivedCategory.map_comp_assoc
      (S.mapDerivedCategoryFactors.inv.app (V n))
      (S.mapDerivedCategoryFactors.hom.app (V n)), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    simp only [← Functor.map_comp]
    exact congrArg (fun f ↦ (U (n + 1)).mapDerivedCategoryFactors.hom.app (V (n + 1)) ≫
      DerivedCategory.Q.map f) (ordinaryCoefficientMap_square I P n)
  have hr : r (n + 1) ≫ w = τ ≫ S.mapDerivedCategory.map (r n) := by
    apply ((adj (n + 1)).homEquiv _ _).injective
    change (adj (n + 1)).unit.app (DerivedCategory.Q.obj P) ≫
        (U (n + 1)).mapDerivedCategory.map (r (n + 1) ≫ w) =
      (adj (n + 1)).unit.app (DerivedCategory.Q.obj P) ≫
        (U (n + 1)).mapDerivedCategory.map (τ ≫ S.mapDerivedCategory.map (r n))
    simp only [Functor.map_comp]
    rw [reassoc_of% hu (n + 1)]
    have ht := ((adj (n + 1)).homEquiv (DerivedCategory.Q.obj P)
      (S.mapDerivedCategory.obj ((L n).obj (DerivedCategory.Q.obj P)))).apply_symm_apply
      ((adj n).unit.app (DerivedCategory.Q.obj P) ≫
        c.hom.app ((L n).obj (DerivedCategory.Q.obj P)))
    change (adj (n + 1)).unit.app (DerivedCategory.Q.obj P) ≫
      (U (n + 1)).mapDerivedCategory.map τ =
      (adj n).unit.app (DerivedCategory.Q.obj P) ≫
        c.hom.app ((L n).obj (DerivedCategory.Q.obj P)) at ht
    rw [reassoc_of% ht]
    have hn := c.hom.naturality (r n)
    dsimp only [Functor.comp_map] at hn
    rw [← hn, reassoc_of% hu n]
    apply (cancel_mono ((U (n + 1)).mapDerivedCategory.map
      (S.mapDerivedCategoryFactors.hom.app (V n)))).1
    apply (cancel_mono ((U (n + 1)).mapDerivedCategoryFactors.hom.app
      ((S.mapHomologicalComplex (.up ℤ)).obj (V n)))).1
    simp only [w, Functor.map_comp, Category.assoc]
    rw [hc]
    rw [Iso.inv_hom_id_app_assoc]
    rw [← (U (n + 1)).mapDerivedCategory.map_comp_assoc
      (S.mapDerivedCategoryFactors.inv.app (V n))
      (S.mapDerivedCategoryFactors.hom.app (V n)), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality,
      Iso.inv_hom_id_app_assoc, ← Functor.map_comp, hv, Functor.map_comp]
  dsimp only [finitePerfectAdicQuotientDiagram]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  unfold adicOrdinaryTensorLevelMap
  change ((U (n + 1)).mapDerivedCategory.map τ ≫
      c.inv.app ((L n).obj (DerivedCategory.Q.obj P))) ≫
      ((U n).mapDerivedCategory.map (r n) ≫ a n) =
    ((U (n + 1)).mapDerivedCategory.map (r (n + 1)) ≫ a (n + 1)) ≫ _
  have hn := c.inv.naturality (r n)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, ← hr, Functor.map_comp_assoc, hw]

/-- Consecutive compatibility and K-flat invertibility assemble the entire quotient diagram.
Source: Stacks Project, Tags 09AW and 06Y6
(blueprint: lem-weil-pbc-adic-ordinary-tensor-transition).
Proof: construct a natural transformation by the inverse-sequence constructor.
Each component is the explicit level map, invertible on K-flat inputs. A natural
transformation with invertible components is a natural isomorphism. -/
theorem adicOrdinaryTensorComplexDiagram_comparison
    {A : Type t} [CommRing A] (I : Ideal A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction I n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (hP : P.IsKFlatForTotalTensor) :
    Nonempty (adicOrdinaryTensorComplexDiagram I P ⋙ DerivedCategory.Q ≅
      finitePerfectAdicQuotientDiagram I L adj (DerivedCategory.Q.obj P)) := by
  let α : finitePerfectAdicQuotientDiagram I L adj (DerivedCategory.Q.obj P) ⟶
      adicOrdinaryTensorComplexDiagram I P ⋙ DerivedCategory.Q :=
    NatTrans.ofOpSequence (fun n ↦ adicOrdinaryTensorLevelMap I L adj P n)
      (adicOrdinaryTensorLevelMap_transition I L adj P)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := by
    change IsIso (adicOrdinaryTensorLevelMap I L adj P n.unop)
    exact adicOrdinaryTensorLevelMap_isIso I L adj P hP n.unop
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨(asIso α).symm⟩

end AlgebraicGeometry.Scheme
