/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage

/-!
# Inverse image of profinite coefficient rings

Source: Stacks Project, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

private theorem adjunct_comp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

namespace AlgebraicGeometry.Scheme

private theorem proEtaleConstantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) : IsIso ((proEtaleConstantComparison f).app A) := by
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let adjY := constantSheafAdj (ProEt.topology Y) CommRingCat.{u + 1} hT
  let adjX := constantSheafAdj (ProEt.topology X) CommRingCat.{u + 1} hGT
  let adj := (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{u + 1})).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X) (op T))
  have he : (proEtaleConstantComparison f).app A =
      (adj.leftAdjointUniq adjX).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjY.comp (proEtaleSheafAdjunction f CommRingCat.{u + 1})).homEquiv _ _
      ((proEtaleConstantComparison f).app A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjY.homEquiv _ _
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1})).homEquiv _ _
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The constant ring-sheaf tower; index `op n` means the paper's level `n+1`.
Source: Stacks, Tags 098T (2), 097N and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable abbrev proEtaleCoefficientTower (X : Scheme.{u})
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :=
  Q ⋙ constantSheaf (ProEt.topology X) CommRingCat.{u + 1}

/-- The specific infinite-limit comparison, without assuming preservation of limits.
Its data is the universal limit comparison followed by the map induced by the canonical
constant comparisons. Source: Stacks, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image). -/
noncomputable def proEtaleProfiniteComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (limit (proEtaleCoefficientTower Y Q)) ⟶ limit (proEtaleCoefficientTower X Q) :=
  limit.post (proEtaleCoefficientTower Y Q)
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}) ≫
    limMap (Functor.whiskerLeft Q (proEtaleConstantComparison f))

private theorem proEtaleProfiniteComparison_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (n : ℕᵒᵖ) :
    proEtaleProfiniteComparison f Q ≫ limit.π (proEtaleCoefficientTower X Q) n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (proEtaleCoefficientTower Y Q) n) ≫
          (proEtaleConstantComparison f).app (Q.obj n) := by
  simp [proEtaleProfiniteComparison]

private theorem proEtaleConstantComparison_id (X : Scheme.{u})
    (A : CommRingCat.{u + 1}) :
    (proEtaleConstantComparison (𝟙 X)).app A =
      (proEtaleRingInverseImageId X).hom.app
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) CommRingCat.{u + 1}
      (ProEt.topology X)
  have hρ : proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A =
      e.inv.app ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj A) _).injective
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_apply]
    apply NatTrans.ext
    funext U
    change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange (𝟙 X)).op.obj U) =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app U ≫
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    have h := (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change (proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).map
      (proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A) ≫ _ = _
  rw [hρ]
  have h := conjugateEquiv_counit_symm Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}) e.inv
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)
  change _ = _ ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact h

private theorem proEtaleConstantComparison_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : CommRingCat.{u + 1}) :
    (proEtaleConstantComparison (f ≫ g)).app A =
      (proEtaleRingInverseImageComp f g).hom.app
        ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).obj A) ≫
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison g).app A) ≫
          (proEtaleConstantComparison f).app A := by
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
        (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  have hρ : proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
            e.hom.app ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
    apply ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj A) _).injective
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right]
    rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext U
    have hf := Equiv.apply_symm_apply
      ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
          ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A)))
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
    have hfU := congrArg (fun t ↦ t.app ((proEtaleBaseChange g).op.obj U)) hf
    change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange g).op.obj U) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
        ((proEtaleBaseChange g).op.obj U) =
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
            ((proEtaleBaseChange f).op.obj ((proEtaleBaseChange g).op.obj U)) at hfU
    change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange (f ≫ g)).op.obj U) =
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
          ((proEtaleBaseChange g).op.obj U) ≫
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
          ((proEtaleBaseChange g).op.obj U)) ≫
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
              ((MorphismProperty.Over.pullbackComp
                (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    rw [hfU]
    have h := (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app U.unop).op
    change 𝟙 A ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact h
  change ((proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}).homEquiv _ _).symm _ = _
  rw [hρ]
  exact adjunct_comp_comparison (proEtaleSheafAdjunction g CommRingCat.{u + 1})
    (proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1}) e
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A)
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A)

/-- Compatible canonical inverse image of a countable tower of finite commutative rings.
The value universe is `u+1`, as required by sheafification on the small site; finite rings
in universe `u` are included by their canonical `ULift`. No surjectivity of transitions is
required. Source: Stacks, Tags 098T (2), 097N, 04D3 and 01YW
(blueprint: lem-weil-pbc-profinite-coefficient-inverse-image).

Proof plan, following the node's eight steps:
1. Use fpqc descent of morphisms to show the small pro-etale site is subcanonical.
2. Represent the finite constant sheaf by the finite disjoint union of copies of the base,
   labelled by ring elements; clopen partitions identify this with sheafified constants.
3. The finite transition maps are affine. Form their scheme limit; over Spec B it is
   Spec of the filtered colimit of B^Q_n. This is ind-etale, hence weakly etale, and small.
4. The representing limit sheaf is the sectionwise inverse limit of the constant rings;
   all ring operations and projections are determined coordinatewise.
5. By the inverse-image adjunction and Yoneda, inverse image of a representable sheaf
   is represented by base change; the adjunct sends each map to its base change.
6. Base change preserves these representing limits and their finite labelled objects.
   Thus the specific canonical limit comparison, rather than arbitrary limits, is invertible.
7. Finite-product preservation transports the ring operations; naturality with respect
   to these operations proves the comparisons are ring isomorphisms with the stated adjunct.
8. Projections determine the limit map uniquely. Label maps give transition and tower
   naturality. Identity base change preserves labels, and iterated base change agrees with
   composite base change; projectionwise uniqueness proves the coherence at the limit.
Dependencies: fpqc-representable-descent, scheme-coproduct-family, limit-affine-transition,
ind-etale-stability, sheaf-algebraic-structures-objects, coyoneda-iso-of-natural-hom-bijection,
presheaf-pullback-sets-left-exact and sheafification-sets-exact, all as listed in the DAG. -/
theorem proEtale_profinite_coefficient_inverse_image
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      IsIso ((proEtaleConstantComparison f).app (Q.obj n))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsIso (proEtaleProfiniteComparison f Q)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      proEtaleProfiniteComparison f Q ≫ limit.π (proEtaleCoefficientTower X Q) n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫
            (proEtaleConstantComparison f).app (Q.obj n)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (a : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (limit (proEtaleCoefficientTower Y Q)) ⟶ limit (proEtaleCoefficientTower X Q)),
      (∀ n : ℕᵒᵖ, a ≫ limit.π (proEtaleCoefficientTower X Q) n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫
            (proEtaleConstantComparison f).app (Q.obj n)) →
      a = proEtaleProfiniteComparison f Q) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n m : ℕᵒᵖ) (a : n ⟶ m),
      (proEtaleConstantComparison f).app (Q.obj n) ≫
          (proEtaleCoefficientTower X Q).map a =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((proEtaleCoefficientTower Y Q).map a) ≫
            (proEtaleConstantComparison f).app (Q.obj m)) ∧
    (∀ (P : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (P.obj n)]
      (a : Q ⟶ P) (X Y : Scheme.{u}) (f : X ⟶ Y),
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limMap (Functor.whiskerRight a
            (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}))) ≫
          proEtaleProfiniteComparison f P =
        proEtaleProfiniteComparison f Q ≫
          limMap (Functor.whiskerRight a
            (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}))) ∧
    (∀ (P : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (P.obj n)]
      (a : Q ⟶ P) (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕᵒᵖ),
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (a.app n)) ≫
          (proEtaleConstantComparison f).app (P.obj n) =
        (proEtaleConstantComparison f).app (Q.obj n) ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (a.app n)) ∧
    (∀ (X : Scheme.{u}) (n : ℕᵒᵖ),
      (proEtaleConstantComparison (𝟙 X)).app (Q.obj n) =
        (proEtaleRingInverseImageId X).hom.app ((proEtaleCoefficientTower X Q).obj n)) ∧
    (∀ X : Scheme.{u}, proEtaleProfiniteComparison (𝟙 X) Q =
      (proEtaleRingInverseImageId X).hom.app (limit (proEtaleCoefficientTower X Q))) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕᵒᵖ),
      (proEtaleConstantComparison (f ≫ g)).app (Q.obj n) =
        (proEtaleRingInverseImageComp f g).hom.app ((proEtaleCoefficientTower Z Q).obj n) ≫
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison g).app (Q.obj n)) ≫
          (proEtaleConstantComparison f).app (Q.obj n)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z),
      proEtaleProfiniteComparison (f ≫ g) Q =
        (proEtaleRingInverseImageComp f g).hom.app (limit (proEtaleCoefficientTower Z Q)) ≫
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
            (proEtaleProfiniteComparison g Q) ≫ proEtaleProfiniteComparison f Q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f n
    exact proEtaleConstantComparison_isIso f (Q.obj n)
  · intro X Y f
    let := proEtaleSheafInverseImage_preserves_finite_tower f Q
    let : ∀ A, IsIso ((proEtaleConstantComparison f).app A) :=
      proEtaleConstantComparison_isIso f
    let : IsIso (proEtaleConstantComparison f) := NatIso.isIso_of_isIso_app _
    unfold proEtaleProfiniteComparison
    infer_instance
  · intro X Y f n
    exact proEtaleProfiniteComparison_π f Q n
  · intro X Y f a ha
    apply limit.hom_ext
    intro n
    rw [ha n, proEtaleProfiniteComparison_π]
  · intro X Y f n m a
    exact ((proEtaleConstantComparison f).naturality (Q.map a)).symm
  · intro P _ a X Y f
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, proEtaleProfiniteComparison_π, limMap_π,
      Functor.whiskerRight_app]
    rw [← Category.assoc, ← Functor.map_comp, limMap_π]
    dsimp only [Functor.whiskerRight_app]
    rw [Functor.map_comp, Category.assoc]
    calc
      _ = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫
            (proEtaleConstantComparison f).app (Q.obj n) ≫
              (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (a.app n) :=
        congrArg (fun t ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (proEtaleCoefficientTower Y Q) n) ≫ t)
            (proEtaleConstantInverseImageMap_naturality f (a.app n))
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun t ↦ t ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (a.app n))
            (proEtaleProfiniteComparison_π f Q n).symm
  · intro P _ a X Y f n
    exact proEtaleConstantInverseImageMap_naturality f (a.app n)
  · intro X n
    exact proEtaleConstantComparison_id X (Q.obj n)
  · intro X
    apply limit.hom_ext
    intro n
    rw [proEtaleProfiniteComparison_π, proEtaleConstantComparison_id]
    exact (proEtaleRingInverseImageId X).hom.naturality
      (limit.π (proEtaleCoefficientTower X Q) n)
  · intro X Y Z f g n
    exact proEtaleConstantComparison_comp f g (Q.obj n)
  · intro X Y Z f g
    apply limit.hom_ext
    intro n
    rw [proEtaleProfiniteComparison_π]
    let π := limit.π (proEtaleCoefficientTower Z Q) n
    let Lf := proEtaleSheafInverseImage f CommRingCat.{u + 1}
    let Lg := proEtaleSheafInverseImage g CommRingCat.{u + 1}
    let Lfg := proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}
    let e := proEtaleRingInverseImageComp f g
    calc
      _ = Lfg.map π ≫ e.hom.app ((proEtaleCoefficientTower Z Q).obj n) ≫
          Lf.map ((proEtaleConstantComparison g).app (Q.obj n)) ≫
            (proEtaleConstantComparison f).app (Q.obj n) := by
        rw [proEtaleConstantComparison_comp]
        rfl
      _ = e.hom.app (limit (proEtaleCoefficientTower Z Q)) ≫
          Lf.map (Lg.map π) ≫ Lf.map ((proEtaleConstantComparison g).app (Q.obj n)) ≫
            (proEtaleConstantComparison f).app (Q.obj n) := by
        rw [← Category.assoc, ← Category.assoc, e.hom.naturality]
        simp only [Category.assoc]
        rfl
      _ = e.hom.app (limit (proEtaleCoefficientTower Z Q)) ≫
          Lf.map (proEtaleProfiniteComparison g Q ≫
            limit.π (proEtaleCoefficientTower Y Q) n) ≫
              (proEtaleConstantComparison f).app (Q.obj n) := by
        rw [proEtaleProfiniteComparison_π, Lf.map_comp, Category.assoc]
      _ = _ := by
        rw [Lf.map_comp]
        simp only [Category.assoc, proEtaleProfiniteComparison_π]
        rfl

end AlgebraicGeometry.Scheme
