/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement

import WeilConjectures.AlgebraicGeometry.Sp.SpRootBasisLevel
import WeilConjectures.AlgebraicGeometry.Sp.SpSliceNormalizedScalarExtensionBasis

/-! # Normalized rational root bases compatible with finite field inclusions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.ProEtale

private def liftSliceIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (e : (spRootBasisSliceSections X R W).obj M ≅
      (spRootBasisSliceSections X R W).obj N) :
    let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
    (O.mapMod R).obj M ≅ (O.mapMod R).obj N := by
  let J := Scheme.ProEt.topology X
  let O := J.overPullback AddCommGrpCat.{u + 1} W
  let G := sheafToPresheaf (J.over W) AddCommGrpCat.{u + 1}
  let H := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let j : O.obj M.X ≅ O.obj N.X := (SheafOfModules.toSheaf _).mapIso e
  refine Mod.isoMk j ?_
  rw [Functor.act_mapMod_obj, Functor.act_mapMod_obj]
  change (Functor.LaxMonoidal.μ O R M.X ≫ O.map (Mod.act M.X)) ≫ j.hom =
    O.obj R ◁ j.hom ≫ (Functor.LaxMonoidal.μ O R N.X ≫ O.map (Mod.act N.X))
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  apply NatTrans.ext
  funext V
  simp only [NatTrans.comp_app]
  have hμ (P T : Sheaf J AddCommGrpCat.{u + 1}) :
      (Functor.LaxMonoidal.μ G (O.obj P) (O.obj T)).app V ≫
          (G.map (Functor.LaxMonoidal.μ O P T)).app V =
        (Functor.LaxMonoidal.μ H P T).app (op V.unop.left) :=
    Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (Over.forget W) AddCommGrpCat.{u + 1} (J.over W) J P T V
  rw [reassoc_of% hμ R M.X, reassoc_of% hμ R N.X]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro r m
  exact (e.hom.val.app V).hom.map_smul r m

private theorem normalizedTower
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n))
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ t : spEllCoefficientSystem X ℓ E ⋙ spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W ≅
      spIntegralTwistSystem X ℓ E ⋙ spRootBasisSliceSections X
        (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W,
      ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
        (b : ((spRootBasisSliceSections X
          (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) W).obj
            (spEllCoefficientLevel X ℓ E n)).val.obj V),
        (t.hom.app (op n)).val.app V b =
          (Functor.LaxMonoidal.μ
            (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
            (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)
            (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))).app (op V.unop.left)
              (b ⊗ₜ[ℤ] (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n)) := by
  classical
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let S := spRootBasisSliceSections X R W
  let C := spEllCoefficientSystem X ℓ E ⋙ S
  let T := spIntegralTwistSystem X ℓ E ⋙ S
  choose i hi using fun n ↦ spRootBasisLevel X ℓ W n (ζ n) (e n) (he n) E
  let t : C ⟶ T := NatTrans.ofOpSequence (F := C) (G := T) (fun n ↦ (i n).hom) (by
    intro n
    dsimp only [C, T]
    simp only [Functor.comp_map, spEllCoefficientSystem, spIntegralTwistSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (i n).hom.val.app V
        ((coefficientMap.{u} (spEllPointTransition ℓ E n) X).hom.app
          (op V.unop.left) b) =
      (spIntegralLevelTransition X ℓ E n).hom.hom.app (op V.unop.left)
        ((i (n + 1)).hom.val.app V b)
    rw [hi n, hi (n + 1)]
    have ht := (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose_spec
    change (spIntegralLevelTransition X ℓ E n).hom = _ at ht
    rw [ht]
    let B₁ := condensedRingObj.{u} (spEllPointRingObj ℓ E (n + 1)) X
    let B₀ := condensedRingObj.{u} (spEllPointRingObj ℓ E n) X
    let M₁ := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 2))
    let M₀ := Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
    let r : B₁ ⟶ B₀ := coefficientMap.{u} (spEllPointTransition ℓ E n) X
    let q : M₁ ⟶ M₀ := Scheme.proEtaleRootsOfUnityTransition X
      (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    have hq := NatTrans.naturality_apply q.hom V.unop.hom.op (ζ (n + 1))
    change q.hom.app (op V.unop.left)
        ((Scheme.purTwistRootsModule X ℓ (n + 1)).val.map V.unop.hom.op (ζ (n + 1))) =
      (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op
        (q.hom.app (op W) (ζ (n + 1))) at hq
    rw [hζ n] at hq
    have hμ := Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) r q
    have hh := congrArg (fun f ↦ f.app (op V.unop.left)
      (b ⊗ₜ[ℤ] (Scheme.purTwistRootsModule X ℓ (n + 1)).val.map
        V.unop.hom.op (ζ (n + 1)))) hμ
    change _ = (r ⊗ₘ q).hom.app (op V.unop.left) _
    change (Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) B₀ M₀).app
        (op V.unop.left)
        (r.hom.app (op V.unop.left) b ⊗ₜ[ℤ]
          q.hom.app (op V.unop.left)
            ((Scheme.purTwistRootsModule X ℓ (n + 1)).val.map
              V.unop.hom.op (ζ (n + 1)))) = _ at hh
    rw [hq] at hh
    exact hh)
  have (n : ℕᵒᵖ) : IsIso (t.app n) := by
    change IsIso (i n.unop).hom
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, hi⟩

private theorem normalizedIntegral
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n))
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
    let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
    ∃ i : Mod.regular (O.obj R) ≅
        (O.mapMod R).obj (spIntegralTwist X ℓ E),
      ∀ (n : ℕ) (V : (Over W)ᵒᵖ) (r : (O.obj R).obj.obj V),
        ((limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom.hom.app
          (op V.unop.left)) (i.hom.hom.hom.app V r) =
        (Functor.LaxMonoidal.μ
          (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
          (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)
          (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))).app (op V.unop.left)
            ((spEllReduction X ℓ E n).hom.app (op V.unop.left) r ⊗ₜ[ℤ]
              (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n)) := by
  classical
  let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let S := spRootBasisSliceSections X R W
  obtain ⟨t, ht⟩ := normalizedTower X ℓ W ζ e hζ he E
  obtain ⟨hc⟩ := spEllCoefficientCone_isLimit X ℓ E
  let cC := S.mapCone (spEllCoefficientCone X ℓ E)
  let cT := S.mapCone (limit.cone (spIntegralTwistSystem X ℓ E))
  have hC : IsLimit cC := by
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    exact isLimitOfPreserves
      (SheafOfModules.evaluation _ (op V.unop.left))
      (isLimitOfPreserves
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R).functor hc)
  have hT : IsLimit cT := by
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro V
    exact isLimitOfPreserves
      (SheafOfModules.evaluation _ (op V.unop.left))
      (isLimitOfPreserves
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R).functor
        (limit.isLimit (spIntegralTwistSystem X ℓ E)))
  let j := hC.conePointsIsoOfNatIso hT t
  let i := liftSliceIso X R W (Mod.regular R) (spIntegralTwist X ℓ E) j
  refine ⟨i, ?_⟩
  intro n V r
  have hj := hC.conePointsIsoOfNatIso_hom_comp hT t (op n)
  have hj' := congrArg (fun f ↦ f.val.app V r) hj
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at hj'
  change ((limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom.hom.app
      (op V.unop.left)) (i.hom.hom.hom.app V r) =
    (t.hom.app (op n)).val.app V
      ((spEllReduction X ℓ E n).hom.app (op V.unop.left) r) at hj'
  exact hj'.trans (ht n V _)

private def mapSemilinear
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (hg : Mod.act M.X ≫ g = (a ⊗ₘ g) ≫ Mod.act N.X) :
    (F.mapMod R).obj M ⟶ (Mod.comap (F.map a)).obj ((F.mapMod S).obj N) := by
  refine Mod.homMk (F.map g) ?_
  simp only [Mod.act_comap_obj, Functor.act_mapMod_obj, Category.assoc]
  rw [← F.map_comp, hg, F.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [tensorHom_def', Category.assoc]
  rfl

private theorem extensionUnit_natural
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S A B : C} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj A] [IsCommMonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (c : A ⟶ B) [IsMonHom c] (M : Mod C R) (N : Mod C S)
    (g : M.X ⟶ N.X)
    (f : (Mod.extendScalarsObj p M).X ⟶ (Mod.extendScalarsObj q N).X)
    (hf : Mod.extendπ p M ≫ f = (c ⊗ₘ g) ≫ Mod.extendπ q N) :
    Mod.extendUnitHom p M ≫ f = g ≫ Mod.extendUnitHom q N := by
  simp only [Mod.extendUnitHom, Category.assoc]
  rw [hf, MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc,
    IsMonHom.one_hom, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

private theorem basisNaturality
    {D : Type*} [Category D] [MonoidalCategory D]
    {R S A B : D} [MonObj R] [MonObj S] [MonObj A] [MonObj B]
    (p : R ⟶ A) [IsMonHom p] (q : S ⟶ B) [IsMonHom q]
    (d : R ⟶ S) [IsMonHom d] (c : A ⟶ B) [IsMonHom c]
    {M : Mod D R} {N : Mod D S} {U : Mod D A} {V : Mod D B}
    (i : Mod.regular R ≅ M) (j : Mod.regular S ≅ N)
    (b : Mod.regular A ≅ U) (e : Mod.regular B ≅ V)
    (t : U ⟶ (Mod.comap c).obj V)
    (u : M.X ⟶ U.X) (v : N.X ⟶ V.X) (g : M.X ⟶ N.X)
    (hb : p ≫ b.hom.hom = i.hom.hom ≫ u)
    (he : q ≫ e.hom.hom = j.hom.hom ≫ v)
    (hi : d ≫ j.hom.hom = i.hom.hom ≫ g)
    (hu : u ≫ t.hom = g ≫ v) :
    c ≫ e.hom.hom = b.hom.hom ≫ t.hom := by
  let k : Mod.regular A ⟶ (Mod.comap c).obj (Mod.regular B) :=
    Mod.homMk c (by
      change MonObj.mul ≫ c = A ◁ c ≫ (c ▷ B ≫ MonObj.mul)
      simpa only [tensorHom_def', Category.assoc] using (IsMonHom.mul_hom c))
  let f := k ≫ (Mod.comap c).map e.hom
  have hbp : MonObj.one (X := A) ≫ b.hom.hom =
      MonObj.one (X := R) ≫ i.hom.hom ≫ u := by
    rw [← IsMonHom.one_hom p, Category.assoc, hb]
  have hep : MonObj.one (X := B) ≫ e.hom.hom =
      MonObj.one (X := S) ≫ j.hom.hom ≫ v := by
    rw [← IsMonHom.one_hom q, Category.assoc, he]
  have h : f = b.hom ≫ t := by
    apply Mod.regular_hom_ext
    change MonObj.one (X := A) ≫ c ≫ e.hom.hom =
      MonObj.one (X := A) ≫ b.hom.hom ≫ t.hom
    rw [← Category.assoc, IsMonHom.one_hom c]
    calc
      _ = MonObj.one (X := S) ≫ j.hom.hom ≫ v := hep
      _ = MonObj.one (X := R) ≫ d ≫ j.hom.hom ≫ v := by
        rw [← IsMonHom.one_hom d, Category.assoc]
      _ = MonObj.one (X := R) ≫ i.hom.hom ≫ g ≫ v := by
        rw [reassoc_of% hi]
      _ = MonObj.one (X := R) ≫ i.hom.hom ≫ u ≫ t.hom := by rw [hu]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ t.hom) hbp.symm
  exact congrArg Mod.Hom.hom h

/-- The prescribed roots give an isomorphism of the rational coefficient and twist
abelian-sheaf diagrams on the slice, whose components are linear for each finite field.

Source: blueprint latest, sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md,
paragraph beginning "These maps commute with every finite-field-extension transition";
sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md, clause (3).
(blueprint: lem-sp-rational-root-diagram-basis)

Proof: at level n tensor the normalized map e_n with O_E/(ell^(n+1)). Its inverse
sends b tensor z to b times the image of e_n inverse applied to z. Balancing gives
the inverse identities. The normalization of e_n and compatibility of the roots
make these maps commute with quotient reductions, so they induce inverse integral
basis maps. Identify the coefficient limit by the positive ell-power coefficient
limit theorem. Extend both maps to E by the specified scalar extension; the
balancing relation proves E-linearity. For E contained in F, the finite transition
sends b tensor zeta_n to its coefficient image tensor the same zeta_n. Thus the
integral maps commute with field inclusions by limit projection extensionality,
and their rational extensions commute by scalar-tensor extensionality. This is
the naturality equation for the asserted diagram isomorphism. The displayed action
identity is precisely the E-linearity of each component, expressed before section
reconstruction. No colimit over fields or positive tensor power is taken here.
The argument includes the empty slice: all the natural maps and inverse equations
remain valid on its sections. -/
theorem spRationalRootDiagramBasis
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] (W : X.ProEt)
    (ζ : ∀ n : ℕ, (Scheme.purTwistRootsModule X ℓ n).val.obj (op W))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over W ≅
        (Scheme.purTwistRootsModule X ℓ n).over W)
    (hζ : ∀ n : ℕ,
      (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op W) (ζ (n + 1)) = ζ n)
    (he : ∀ (n : ℕ) (V : (Over W)ᵒᵖ)
      (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over W).obj.obj V),
      (e n).hom.val.app V a =
        a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n)) :
    let A := Profinite.padicSubfieldRingObjFunctor.{u} ℓ ⋙ upperStarFromPoint X
    let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
    ∃ b : A ⋙ O ≅ spRationalTwistDiagram X ℓ ⋙ O,
      ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Functor.LaxMonoidal.μ O (A.obj E) (A.obj E) ≫
            O.map (MonObj.mul (X := condensedRingObj.{u}
              (Profinite.continuousMapRingObj.{u} E.1) X)) ≫ b.hom.app E =
          O.obj (A.obj E) ◁ b.hom.app E ≫
            Functor.LaxMonoidal.μ O (A.obj E) (spRationalTwist X ℓ E).X ≫
              O.map (Mod.act (A := condensedRingObj.{u}
                (Profinite.continuousMapRingObj.{u} E.1) X) (spRationalTwist X ℓ E).X) := by
  classical
  let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
  let R (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  choose i hi using fun E ↦ normalizedIntegral X ℓ W ζ e hζ he E
  choose b hb using fun E ↦ spSliceNormalizedScalarExtensionBasis X
    (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) W (i E)
  have hincl {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
      O.map (spIntegersMap X ℓ h) ≫ (i F).hom.hom =
        (i E).hom.hom ≫ O.map (spIntegralTwistMap X ℓ h) := by
    let hc := isLimitOfPreserves O
      (isLimitOfPreserves (Mod.forget (R F))
        (limit.isLimit (spIntegralTwistSystem X ℓ F)))
    apply hc.hom_ext
    intro n
    have hm := (spIntegralTwistMap_existsUnique X ℓ h).exists.choose_spec n.unop
    change spIntegralTwistMap X ℓ h ≫
      (limit.π (spIntegralTwistSystem X ℓ F) n).hom = _ at hm
    change (O.map (spIntegersMap X ℓ h) ≫ (i F).hom.hom) ≫
        O.map (limit.π (spIntegralTwistSystem X ℓ F) n).hom =
      ((i E).hom.hom ≫ O.map (spIntegralTwistMap X ℓ h)) ≫
        O.map (limit.π (spIntegralTwistSystem X ℓ F) n).hom
    rw [Category.assoc, Category.assoc, ← O.map_comp, hm, O.map_comp]
    ext V r
    change (limit.π (spIntegralTwistSystem X ℓ F) n).hom.hom.app (op V.unop.left)
        ((i F).hom.hom.hom.app V
          ((spIntegersMap X ℓ h).hom.app (op V.unop.left) r)) =
      (spEllMap X ℓ h n.unop ⊗ₘ
        𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n.unop + 1)))).hom.app
          (op V.unop.left)
          ((limit.π (spIntegralTwistSystem X ℓ E) n).hom.hom.app (op V.unop.left)
            ((i E).hom.hom.hom.app V r))
    rw [hi F n.unop, hi E n.unop]
    have hd := (spEllMap_existsUnique X ℓ h n.unop).exists.choose_spec
    change spEllReduction X ℓ E n.unop ≫ spEllMap X ℓ h n.unop =
      spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n.unop at hd
    have hd' := congrArg (fun f ↦ f.hom.app (op V.unop.left) r) hd
    change (spEllMap X ℓ h n.unop).hom.app (op V.unop.left)
        ((spEllReduction X ℓ E n.unop).hom.app (op V.unop.left) r) =
      (spEllReduction X ℓ F n.unop).hom.app (op V.unop.left)
        ((spIntegersMap X ℓ h).hom.app (op V.unop.left) r) at hd'
    rw [← hd']
    have ht := Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (spEllMap X ℓ h n.unop)
      (𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n.unop + 1))))
    exact ConcreteCategory.congr_hom (congr_app ht (op V.unop.left))
      ((spEllReduction X ℓ E n.unop).hom.app (op V.unop.left) r ⊗ₜ[ℤ]
        (Scheme.purTwistRootsModule X ℓ n.unop).val.map V.unop.hom.op (ζ n.unop))
  let K (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X
  have hnat {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
      O.map (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X) ≫
          (b F).hom.hom =
        (b E).hom.hom ≫ O.map (spRationalTwistMap X ℓ h) := by
    let a := coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X
    let t := mapSemilinear O a (spRationalTwist X ℓ E) (spRationalTwist X ℓ F)
      (spRationalTwistMap X ℓ h) (spRationalTwistMap_semilinear X ℓ h)
    have hu := extensionUnit_natural
      (padicIntegersToPadicSubfield X ℓ E) (padicIntegersToPadicSubfield X ℓ F)
      a (spIntegralTwist X ℓ E) (spIntegralTwist X ℓ F)
      (spIntegralTwistMap X ℓ h) (spRationalTwistMap X ℓ h)
      ((spRationalTwistMap_existsUnique X ℓ h).exists.choose_spec)
    have : IsMonHom (spIntegersMap X ℓ h) :=
      (spIntegersMap_existsUnique X ℓ h).exists.choose_spec.1
    apply basisNaturality
      (O.map (padicIntegersToPadicSubfield X ℓ E))
      (O.map (padicIntegersToPadicSubfield X ℓ F))
      (O.map (spIntegersMap X ℓ h)) (O.map a)
      (i E) (i F) (b E) (b F) t
      (O.map (Mod.extendUnitHom (padicIntegersToPadicSubfield X ℓ E)
        (spIntegralTwist X ℓ E)))
      (O.map (Mod.extendUnitHom (padicIntegersToPadicSubfield X ℓ F)
        (spIntegralTwist X ℓ F)))
      (O.map (spIntegralTwistMap X ℓ h)) (hb E) (hb F) (hincl h)
    exact (O.map_comp _ _).symm.trans ((congrArg O.map hu).trans (O.map_comp _ _))
  refine ⟨NatIso.ofComponents
    (fun E ↦ (Mod.forget (O.obj (K E))).mapIso (b E)) ?_, ?_⟩
  · intro E F f
    exact hnat (leOfHom f)
  · intro E
    exact Mod.act_hom (b E).hom

end AlgebraicGeometry.ProEtale
