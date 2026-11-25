/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationTensorSummands
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationComponentOverTransport

/-! # Tensor summand calculation for ordinary evaluation under open reindexing

Source: Stacks Project, Tags 0A8X, 08DL and 08DQ, ordinary Hom and evaluation.
(blueprint: lem-pc-ordinary-evaluation-over-tensor-formula). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

noncomputable local instance ordinaryOverSchemePreadditive (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1

attribute [local irreducible] homComplexFunctor IsSchemeOrdinaryEvaluation

/-- With the Hom comparison pinned on product projections, the ordinary tensor
comparison and a natural termwise Hom comparison can be chosen to preserve the
evaluation component formula. The dual
comparison in this statement is constructed from the single-unit isomorphism.
Source: Stacks Project, Tags 0A8X, 08DL and 08DQ; ordinary-complex calculation.
(blueprint: lem-pc-ordinary-evaluation-over-tensor-formula).

Proof: first construct e by reindexing the compatible families of local linear
maps on the slice over each open. The inverse uses the inverse slice equivalence;
composition with f and g commutes with this construction. Thus e is natural, and
its action on sections is explicitly fixed. Use the tensorator obtained by
reindexing pure tensors along the equivalence
of open sites. Naturality in each factor gives a bicomplex isomorphism. Preservation
of coproducts identifies its total complex with the image of the original total
complex; call this comparison c. Compose c with the total tensor of the identity
and d, where d is the supplied Hom comparison at the single unit followed by Hom
of the canonical single-unit isomorphism a. Precompose with each tensor summand
and postcompose with each Hom projection. The prescribed projection equation for
b and the tensor summand equation for c identify the transported left side with
the image of the local evaluation component. If r+q is zero, uncurry that component:
both maps reindex the same local linear map (y,phi,x) sent to y*phi(x). The unit
isomorphism a identifies the coefficient actions; the associator and symmetry
reindex the same tensor factors. If r+q is nonzero both components vanish, since
the single unit is zero in that degree. The maps induced by equality of output
degrees agree by functoriality. These component identities prove the displayed
predicate. No chain-map naturality of b, boundedness, perfectness, acyclicity or
nonempty-open hypothesis is needed. In particular zero complexes and the empty
open satisfy the same product and coproduct calculation. -/
theorem exists_ordinaryEvaluation_over_tensor_formula (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    ∃ (e : ∀ A B : localEvaluationModules X U,
        L.obj (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
          SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A) (L.obj B)),
      (∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
        L.map (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
            (e A' B').hom =
          (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
            (L.map f) (L.map g)) ∧
    ∀ (b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
        T.obj (homComplex (R := X.sheaf.over U) P M) ≅
          homComplex (R := U.toScheme.sheaf) (T.obj P) (T.obj M)),
      (∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
          (n r s : ℤ) (h : r + n = s),
        (b M).hom.f n ≫
            (Classical.choose (homComplex_projections_exists (R := U.toScheme.sheaf)))
              (T.obj P) (T.obj M) n r s h =
          L.map (localEvaluationProjection X U P M n r s h) ≫
            (e (P.X r) (M.X s)).hom) →
      let a : T.obj (localEvaluationUnit X U) ≅ O' :=
        (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app _ ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso
            (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
      let d := b (localEvaluationUnit X U) ≪≫
        ((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).mapIso a
      ∀ F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F,
            IsLocalOrdinaryEvaluation X U P F f →
              IsSchemeOrdinaryEvaluation U.toScheme (T.obj P) (T.obj F)
                ((c ≪≫ (((curriedTensor (SheafOfModules.{u}
                  (moduleRings U.toScheme.toRingedSpace))).map₂CochainComplex).obj
                    (T.obj F)).mapIso d).inv ≫
                  T.map f ≫ (b F).hom) := by
  dsimp only
  set_option backward.isDefEq.respectTransparency true in
    let h := internalHom_overEquiv (Y := X) U
    let e := Classical.choose h
    have he := Classical.choose_spec h
    refine ⟨e, he, ?_⟩
    intro b hπ
    have hcalc := ordinaryEvaluation_component_over_transport X U P e he b hπ
    let ht := exists_ordinaryEvaluation_tensor_summands X U
    let m := Classical.choose ht
    have hm := Classical.choose_spec ht
    intro F
    let hF := hm.2.2 P F
    let c := Classical.choose hF
    have hc := Classical.choose_spec hF
    exact ⟨c, hcalc m hm.1 hm.2.1 F c hc⟩

end AlgebraicGeometry
