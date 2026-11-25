/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentFactorization

/-! # Invertible evaluation diagonal

Source: Stacks Project, Tags 08DQ and 08DM.
(blueprint: lem-pc-ordinary-evaluation-diagonal-block).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

private lemma localHom_isZero_target (X : Scheme.{u}) (U : X.Opens)
    (A B : localEvaluationModules X U) (hB : IsZero B) :
    IsZero (SheafOfModules.homObj (R := X.sheaf.over U) A B) := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) A _ B).symm.injective
  exact hB.eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency true in
private theorem dualProjection_isIso (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) (r : ℤ) :
    IsIso (localEvaluationProjection X U P (localEvaluationUnit X U) (-r) r 0
      (by omega)) := by
  classical
  let L := localEvaluationUnit X U
  let M (p : ℤ) := SheafOfModules.homObj (R := X.sheaf.over U)
    (P.X p) (L.X (p + -r))
  let T := (localEvaluationDual X U P).X (-r)
  let π : ∀ p, T ⟶ M p := fun p ↦
    localEvaluationProjection X U P L (-r) p (p + -r) rfl
  let hπ : IsLimit (Fan.mk T π) :=
    ((Classical.choose_spec (homComplex_projections_exists
      (R := X.sheaf.over U))).1 P L (-r)).some
  let ι : M r ⟶ T := Fan.IsLimit.lift hπ
    (fun p ↦ if h : p = r then eqToHom (congrArg M h.symm) else 0)
  have hι (p : ℤ) : ι ≫ π p =
      if h : p = r then eqToHom (congrArg M h.symm) else 0 :=
    Fan.IsLimit.fac hπ _ p
  have hleft : π r ≫ ι = 𝟙 T := by
    apply Fan.IsLimit.hom_ext hπ
    intro p
    change (π r ≫ ι) ≫ π p = 𝟙 T ≫ π p
    rw [Category.assoc, hι]
    by_cases h : p = r
    · subst p
      simp
    · have hz : IsZero (M p) := localHom_isZero_target X U _ _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
          (𝟙_ (localEvaluationModules X U)) (p + -r) (by omega))
      exact hz.eq_of_tgt _ _
  have hright : ι ≫ π r = 𝟙 (M r) := by simp [hι]
  have hi : IsIso (π r) := ⟨⟨ι, hleft, hright⟩⟩
  have hr : r + -r = (0 : ℤ) := by omega
  have hh : ∀ (q : ℤ) (h : r + -r = q),
      IsIso (localEvaluationProjection X U P L (-r) r q h) := by
    intro q h
    subst q
    exact hi
  exact hh 0 hr

set_option backward.isDefEq.respectTransparency true in
/-- The diagonal component is invertible whenever its module evaluation is.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`,
termwise evaluation; Tag 08DM, degree of the dual complex.
(blueprint: lem-pc-ordinary-evaluation-diagonal-block).

Proof: in degree -r of Hom(P,O[0]), every product factor except the r-th
vanishes, since O[0] is zero in all other degrees. The product universal property
therefore makes the r-th projection an isomorphism. Compose it with internal Hom
of the single-complex degree-zero unit isomorphism. In the displayed component,
r+(-r)=0 and (r+n)+(-r)=n. Naturality of tensor-Hom adjunction, the associator,
the braiding and the right unitor identify this component with tensoring that
dual projection by F^(r+n), followed by moduleDualEvaluation. The degree transport
is the identity because its endpoints coincide. Both factors are isomorphisms:
tensoring preserves the first and hblock supplies the second. This uses no bound
on P or F, and also applies to zero modules and the empty open. -/
theorem ordinaryEvaluation_diagonal_block (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (n r : ℤ)
    (hblock : IsIso (SheafOfModules.moduleDualEvaluation
      (X.sheaf.over U) (P.X r) (F.X (r + n)))) :
    IsIso (localEvaluationComponent X U P F (r + n) (-r) n r (by omega)) := by
  classical
  let := hblock
  let d := localEvaluationProjection X U P (localEvaluationUnit X U) (-r) r 0
      (by omega) ≫
    SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (localEvaluationModules X U))).hom
  let hd : IsIso d := by
    have hp := dualProjection_isIso X U P r
    have hm : IsIso (SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (𝟙_ (localEvaluationModules X U))).hom) := by
      change IsIso (((SheafOfModules.homFunctor (X.sheaf.over U)).obj
        (op (P.X r))).map _)
      infer_instance
    exact IsIso.comp_isIso' hp hm
  have he : localEvaluationComponent X U P F (r + n) (-r) n r (by omega) =
      (F.X (r + n) ◁ d) ≫
        SheafOfModules.moduleDualEvaluation (X.sheaf.over U) (P.X r) (F.X (r + n)) := by
    simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      SheafOfModules.homObjMap_id, Category.comp_id] using
      ordinaryEvaluation_component_factorization X U P F (r + n) (-r) n r
        (by omega) (by omega)
  rw [he]
  apply IsIso.comp_isIso' _ hblock
  change IsIso ((tensorLeft (F.X (r + n))).map d)
  infer_instance

end AlgebraicGeometry
