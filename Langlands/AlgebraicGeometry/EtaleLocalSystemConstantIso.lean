import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Maps between constant abelian presheaves -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

variable {S T : Scheme.{u}} {M N : AddCommGrpCat.{u}}

private def constSection (V : Over S) : M →+ (constant S M).obj (op V) :=
  (constantSections S M V).symm.toAddMonoidHom.comp LocallyConstant.constAddMonoidHom

@[simp] private lemma constSection_eval (V : Over S) (m : M) (x : V.left) :
    constantSections S M V (constSection V m) x = m := by
  change (constantSections S M V) ((constantSections S M V).symm
    (LocallyConstant.const V.left m)) x = m
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Evaluate a map of constant presheaves on the constant sections at a point of the base. -/
def constantHomAt (α : constant S M ⟶ constant S N) (x : S) : M →+ N where
  toFun m := constantSections S N (Over.mk (𝟙 S))
    (α.app (op (Over.mk (𝟙 S))) (constSection _ m)) x
  map_zero' := by
    rw [map_zero, map_zero, map_zero]
    rfl
  map_add' m n := by
    rw [map_add, map_add, map_add]
    rfl

/-- A map of constant presheaves acts pointwise through its value on the base. -/
theorem constantHomAt_app (α : constant S M ⟶ constant S N) (V : Over S)
    (a : (constant S M).obj (op V)) (x : V.left) :
    constantSections S N V (α.app (op V) a) x =
      constantHomAt α (V.hom x) (constantSections S M V a x) := by
  let W : Over S := Over.mk (V.left.fromSpecResidueField x ≫ V.hom)
  let r : W ⟶ V := Over.homMk (V.left.fromSpecResidueField x) rfl
  let t : W ⟶ Over.mk (𝟙 S) := Over.homMk W.hom (Category.comp_id _)
  let y : W.left := IsLocalRing.closedPoint (V.left.residueField x)
  let m := constantSections S M V a x
  have hr : r.left y = x := Scheme.fromSpecResidueField_apply x y
  have ht : t.left y = V.hom x := by
    change (V.left.fromSpecResidueField x ≫ V.hom) y = V.hom x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have he : (constant S M).map r.op a =
      (constant S M).map t.op (constSection _ m) := by
    apply (constantSections _ _ _).injective
    apply LocallyConstant.ext
    intro z
    rw [constantSections_map, constantSections_map, constSection_eval]
    change constantSections S M V a (V.left.fromSpecResidueField x z) = m
    rw [Scheme.fromSpecResidueField_apply]
  have natural (Z : Over S) (f : W ⟶ Z) (a : (constant S M).obj (op Z)) :
      constantSections S N W (α.app (op W) ((constant S M).map f.op a)) y =
        constantSections S N Z (α.app (op Z) a) (f.left y) := by
    rw [NatTrans.naturality_apply, constantSections_map]
  have key := congrArg (fun v => constantSections S N W (α.app (op W) v) y) he
  change constantSections S N W (α.app (op W) ((constant S M).map r.op a)) y =
    constantSections S N W (α.app (op W) ((constant S M).map t.op (constSection _ m))) y at key
  rw [natural, natural, hr, ht] at key
  exact key

/-- The evaluation of a composite of constant presheaf maps is pointwise composition. -/
theorem constantHomAt_comp {P : AddCommGrpCat.{u}}
    (α : constant S M ⟶ constant S N) (β : constant S N ⟶ constant S P)
    (x : S) (m : M) :
    constantHomAt (α ≫ β) x m = constantHomAt β x (constantHomAt α x m) := by
  change constantSections S P (Over.mk (𝟙 S))
    (β.app _ (α.app _ (constSection _ m))) x = _
  exact constantHomAt_app β (Over.mk (𝟙 S)) (α.app _ (constSection _ m)) x

@[simp] theorem constantHomAt_id (x : S) (m : M) :
    constantHomAt (𝟙 (constant S M)) x m = m :=
  constSection_eval (Over.mk (𝟙 S)) m x

private def constantIsoAt (e : constant S M ≅ constant S N) (x : S) : M ≃+ N :=
  { constantHomAt e.hom x with
    toFun := constantHomAt e.hom x
    invFun := constantHomAt e.inv x
    left_inv := fun m => by rw [← constantHomAt_comp, e.hom_inv_id, constantHomAt_id]
    right_inv := fun n => by rw [← constantHomAt_comp, e.inv_hom_id, constantHomAt_id] }

/-- For a finitely generated source, a constant presheaf isomorphism is given by a locally
constant family of additive equivalences. -/
def constantIsoValues [AddGroup.FG M] (e : constant S M ≅ constant S N) :
    LocallyConstant S (M ≃+ N) := by
  refine ⟨constantIsoAt e, IsLocallyConstant.iff_isOpen_fiber_apply.mpr fun x => ?_⟩
  obtain ⟨A, hA, hfin⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG M)
  have hgen (y : S) : constantIsoAt e y = constantIsoAt e x ↔
      ∀ a ∈ A, constantHomAt e.hom y a = constantHomAt e.hom x a := by
    constructor
    · intro h a ha
      exact DFunLike.congr_fun h a
    · intro h
      apply AddEquiv.ext
      intro a
      let K := (constantHomAt e.hom y).eqLocus (constantHomAt e.hom x)
      have hAK : A ⊆ K := fun a ha => h a ha
      have hk : (⊤ : AddSubgroup M) ≤ K := by
        rw [← hA]
        exact (AddSubgroup.closure_le K).mpr hAK
      exact hk (show a ∈ (⊤ : AddSubgroup M) from trivial)
  have hs : (constantIsoAt e ⁻¹' {constantIsoAt e x}) =
      ⋂ a : A, {y : S | constantHomAt e.hom y a = constantHomAt e.hom x a} := by
    ext y
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq,
      Subtype.forall] using hgen y
  rw [hs]
  have : Finite A := hfin
  exact isOpen_iInter_of_finite fun a =>
    (constantSections S N (Over.mk (𝟙 S)) (e.hom.app _ (constSection _ (a : M)))).2.isOpen_fiber _

private def applyValues (f : LocallyConstant S (M →+ N)) (V : Over S) :
    LocallyConstant V.left M →+ LocallyConstant V.left N where
  toFun a := ⟨fun x => f (V.hom x) (a x),
    (f.isLocallyConstant.comp_continuous V.hom.continuous).comp₂ a.isLocallyConstant
      (fun g m => g m)⟩
  map_zero' := by
    apply LocallyConstant.ext
    intro x
    exact map_zero (f (V.hom x))
  map_add' a b := by
    apply LocallyConstant.ext
    intro x
    exact map_add (f (V.hom x)) (a x) (b x)

private def constantHomOfValuesApp (f : LocallyConstant S (M →+ N)) (V : Over S) :
    (constant S M).obj (op V) ⟶ (constant S N).obj (op V) where
  hom' := (constantSections S N V).symm.toAddMonoidHom.comp
    ((applyValues f V).comp (constantSections S M V).toAddMonoidHom)

private theorem constantHomOfValuesApp_eval (f : LocallyConstant S (M →+ N)) (V : Over S)
    (a : (constant S M).obj (op V)) (x : V.left) :
    constantSections S N V (constantHomOfValuesApp f V a) x =
      f (V.hom x) (constantSections S M V a x) := by
  change (constantSections S N V) ((constantSections S N V).symm
    (applyValues f V (constantSections S M V a))) x = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- A locally constant family of additive homomorphisms acts on every scheme over the base. -/
def constantHomOfValues (f : LocallyConstant S (M →+ N)) : constant S M ⟶ constant S N where
  app V := constantHomOfValuesApp f V.unop
  naturality {V W} a := by
    ext z
    apply (constantSections S N W.unop).injective
    apply LocallyConstant.ext
    intro x
    change constantSections S N W.unop
      (constantHomOfValuesApp f W.unop ((constant S M).map a.unop.op z)) x =
      constantSections S N W.unop ((constant S N).map a.unop.op
        (constantHomOfValuesApp f V.unop z)) x
    rw [constantHomOfValuesApp_eval, constantSections_map, constantSections_map,
      constantHomOfValuesApp_eval]
    rw [← Scheme.Hom.comp_apply, Over.w a.unop]

/-- Formula for the action on a test scheme of a locally constant family. -/
@[simp] theorem constantHomOfValues_app (f : LocallyConstant S (M →+ N)) (V : Over S)
    (a : (constant S M).obj (op V)) (x : V.left) :
    constantSections S N V ((constantHomOfValues f).app (op V) a) x =
      f (V.hom x) (constantSections S M V a x) := constantHomOfValuesApp_eval f V a x

/-- A locally constant family of additive equivalences induces a constant presheaf isomorphism. -/
def constantIsoOfValues (f : LocallyConstant S (M ≃+ N)) : constant S M ≅ constant S N where
  hom := constantHomOfValues (f.map AddEquiv.toAddMonoidHom)
  inv := constantHomOfValues (f.map fun e => e.symm.toAddMonoidHom)
  hom_inv_id := by
    ext V a
    apply (constantSections S M V.unop).injective
    apply LocallyConstant.ext
    intro x
    change constantSections S M V.unop
        ((constantHomOfValues (f.map fun e => e.symm.toAddMonoidHom)).app (op V.unop)
          ((constantHomOfValues (f.map AddEquiv.toAddMonoidHom)).app (op V.unop) a)) x = _
    rw [constantHomOfValues_app, constantHomOfValues_app]
    exact (f (V.unop.hom x)).symm_apply_apply _
  inv_hom_id := by
    ext V a
    apply (constantSections S N V.unop).injective
    apply LocallyConstant.ext
    intro x
    change constantSections S N V.unop
        ((constantHomOfValues (f.map AddEquiv.toAddMonoidHom)).app (op V.unop)
          ((constantHomOfValues (f.map fun e => e.symm.toAddMonoidHom)).app (op V.unop) a)) x = _
    rw [constantHomOfValues_app, constantHomOfValues_app]
    exact (f (V.unop.hom x)).apply_symm_apply _

/-- The family extracted from an isomorphism recovers that isomorphism. -/
theorem constantIsoOfValues_constantIsoValues [AddGroup.FG M]
    (e : constant S M ≅ constant S N) : constantIsoOfValues (constantIsoValues e) = e := by
  apply Iso.ext
  ext V a
  apply (constantSections S N V.unop).injective
  apply LocallyConstant.ext
  intro x
  change constantSections S N V.unop
      ((constantHomOfValues ((constantIsoValues e).map AddEquiv.toAddMonoidHom)).app
        (op V.unop) a) x = _
  rw [constantHomOfValues_app, constantHomAt_app]
  rfl

/-- Evaluation recovers the locally constant family defining an isomorphism. -/
theorem constantIsoValues_constantIsoOfValues [AddGroup.FG M]
    (f : LocallyConstant S (M ≃+ N)) : constantIsoValues (constantIsoOfValues f) = f := by
  apply LocallyConstant.ext
  intro x
  apply AddEquiv.ext
  intro m
  change constantSections S N (Over.mk (𝟙 S))
    ((constantHomOfValues (f.map AddEquiv.toAddMonoidHom)).app (op (Over.mk (𝟙 S)))
      (constSection _ m)) x = f x m
  rw [constantHomOfValues_app, constSection_eval]
  rfl

end Langlands.AlgebraicGeometry.EtaleLocalSystem
