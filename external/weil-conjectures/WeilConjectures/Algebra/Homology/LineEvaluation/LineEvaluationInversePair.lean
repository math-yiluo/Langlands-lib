/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Specified evaluation and inverse tensor pair for a sheaf line

Source: Stacks Project, Modules on Sites, Tags 0B8Q and 0B8N.
(blueprint: lem-pur-sheaf-line-evaluation-inverse-pair)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.LineEvaluation

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})

/-- The module category already defined on the given ringed site.
Source: Stacks 03DD (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev Modules := ringedSiteModules.{max uC vC r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The existing internal Hom dual to the coefficient unit.
Source: Stacks 0B8Q (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev dual (P : Modules.{uC, vC, r} R) : Modules.{uC, vC, r} R :=
  homObj (R := R) P (𝟙_ (Modules.{uC, vC, r} R))

/-- The image of a pure tensor under the sheafification unit and tensor comparison.
Source: Stacks 03EK (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
def pureTensor (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- Reassociation, evaluation of the last two factors, and the right unitor.
Source: Stacks 0B8N (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
def cancellation (P Q : Modules.{uC, vC, r} R) (e : P ⊗ Q ≅ 𝟙_ (Modules.{uC, vC, r} R)) :
    tensorRight P ⋙ tensorRight Q ≅ 𝟭 (Modules.{uC, vC, r} R) :=
  (tensorRightTensor P Q).symm ≪≫ (tensoringRight (Modules.{uC, vC, r} R)).mapIso e ≪≫
    rightUnitorNatIso (Modules.{uC, vC, r} R)

/-- Global ring sections, acting componentwise on module morphisms.
Source: Stacks 04TT (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev scalars := RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)

/-- The existing sectionwise scalar action, with no chosen linear structure.
Source: Stacks 04TT (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
instance coefficientLinear : Linear (scalars.{uC, vC, r} R) (Modules.{uC, vC, r} R) :=
  homLinear R.obj ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] cochainModulesMonoidal

private abbrev ringSheaf :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

private abbrev unitDual (P : Modules.{uC, vC, r} R) : Modules.{uC, vC, r} R :=
  homObj (R := R) P (unit (ringSheaf.{uC, vC, r} R))

private noncomputable def adj :
    PresheafOfModules.sheafification (𝟙 (ringSheaf.{uC, vC, r} R).obj) ⊣
      forget (ringSheaf.{uC, vC, r} R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf.{uC, vC, r} R).obj)

@[instance_reducible]
private noncomputable def forgetLax : (forget (ringSheaf.{uC, vC, r} R)).LaxMonoidal :=
  (adj.{uC, vC, r} R).rightAdjointLaxMonoidal

private theorem forget_mu (M N : Modules.{uC, vC, r} R) :
    let := forgetLax.{uC, vC, r} R
    Functor.LaxMonoidal.μ (forget (ringSheaf.{uC, vC, r} R)) M N =
      (adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val := by
  let := forgetLax.{uC, vC, r} R
  change (adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫
    (forget (ringSheaf.{uC, vC, r} R)).map
      (Functor.OplaxMonoidal.δ
        (PresheafOfModules.sheafification (𝟙 (ringSheaf.{uC, vC, r} R).obj)) M.val N.val ≫
        ((adj.{uC, vC, r} R).counit.app M ⊗ₘ (adj.{uC, vC, r} R).counit.app N)) = _
  simp only [tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
    Functor.Monoidal.μIso_inv, tensorIso_hom, Iso.app_hom, asIso_hom]
  dsimp only [forget, Functor.map_comp, adj, ringSheaf]

attribute [local irreducible] tensorObjIsoSheafification

private noncomputable def pureBilin (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ) :
    M.val.obj U →ₗ[R.obj.obj U] N.val.obj U →ₗ[R.obj.obj U] (M ⊗ N).val.obj U :=
  TensorProduct.curry (((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫
    (tensorObjIsoSheafification M N).inv.val).app U).hom

private theorem forget_epsilon :
    letI := forgetLax.{uC, vC, r} R
    Functor.LaxMonoidal.ε (forget (ringSheaf.{uC, vC, r} R)) = 𝟙 _ := by
  let := forgetLax.{uC, vC, r} R
  change (adj.{uC, vC, r} R).unit.app _ ≫
    (forget (ringSheaf.{uC, vC, r} R)).map
      ((adj.{uC, vC, r} R).counit.app (unit (ringSheaf.{uC, vC, r} R))) = 𝟙 _
  exact (adj.{uC, vC, r} R).right_triangle_components (unit (ringSheaf.{uC, vC, r} R))

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

private theorem pure_smul_left (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{uC, vC, r} R M N U (a • x) y = a • pureTensor.{uC, vC, r} R M N U x y := by
  exact (pureBilin.{uC, vC, r} R M N U).map_smul₂ a x y

private theorem pure_smul_right (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{uC, vC, r} R M N U x (a • y) = a • pureTensor.{uC, vC, r} R M N U x y := by
  exact (pureBilin.{uC, vC, r} R M N U x).map_smul a y

private theorem pure_hom_ext (M N H : Modules.{uC, vC, r} R)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ U x y, f.val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      g.val.app U (pureTensor.{uC, vC, r} R M N U x y)) : f = g := by
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply ((adj.{uC, vC, r} R).homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem pure_map {M M' N N' : Modules.{uC, vC, r} R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R M' N' U (f.val.app U x) (g.val.app U y) := by
  exact CategoryTheory.CochainPullback.moduleTmul_map f g U x y

private theorem pure_assoc (M N H : Modules.{uC, vC, r} R)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) :
    (α_ M N H).hom.val.app U
      (pureTensor.{uC, vC, r} R (M ⊗ N) H U (pureTensor.{uC, vC, r} R M N U x y) z) =
        pureTensor.{uC, vC, r} R M (N ⊗ H) U x (pureTensor.{uC, vC, r} R N H U y z) := by
  exact CategoryTheory.CochainPullback.moduleTmul_associator M N H U x y z

private theorem pure_right_unitor (M : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (a : R.obj.obj U) :
    (ρ_ M).hom.val.app U (pureTensor.{uC, vC, r} R M (unit (ringSheaf.{uC, vC, r} R)) U x a) =
      a • x := by
  let := forgetLax.{uC, vC, r} R
  have h := Functor.LaxMonoidal.right_unitality (forget (ringSheaf.{uC, vC, r} R)) M
  rw [forget_epsilon.{uC, vC, r}, whiskerLeft_id, Category.id_comp, forget_mu.{uC, vC, r}] at h
  exact (congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] a)) h).symm

private theorem pure_braiding (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (β_ M N).hom.val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R N M U y x := by
  exact CategoryTheory.CochainPullback.moduleTmul_braiding M N U x y

private noncomputable def evalLinear (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ) :
    (unitDual.{uC, vC, r} R P).val.obj U →ₗ[R.obj.obj U]
      P.val.obj U →ₗ[R.obj.obj U] R.obj.obj U where
  toFun phi := (phi.app (op (Over.mk (𝟙 U.unop)))).hom
  map_add' _ _ := rfl
  map_smul' a phi := by
    ext x
    change R.obj.map (𝟙 U.unop).op a •
      (phi.app (op (Over.mk (𝟙 U.unop))) x) = a • _
    rw [op_id, R.obj.map_id]
    rfl

omit [EssentiallySmall.{max uC vC r} C] in
private theorem eval_restrict (P : Modules.{uC, vC, r} R) {U V : Cᵒᵖ}
    (f : U ⟶ V) (phi : (unitDual.{uC, vC, r} R P).val.obj U) (x : P.val.obj U) :
    evalLinear.{uC, vC, r} R P V ((unitDual.{uC, vC, r} R P).val.map f phi) (P.val.map f x) =
      R.obj.map f (evalLinear.{uC, vC, r} R P U phi x) := by
  change phi.app (op (Over.mk (𝟙 V.unop ≫ f.unop))) (P.val.map f x) = _
  refine (PresheafOfModules.restrictOver_hom_app_congr phi (Category.id_comp _) _).trans ?_
  exact PresheafOfModules.naturality_apply phi
    (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op x

private noncomputable def evalPresheaf (P : Modules.{uC, vC, r} R) :
    P.val ⊗ (unitDual.{uC, vC, r} R P).val ⟶ (unit (ringSheaf.{uC, vC, r} R)).val where
  app U := ModuleCat.ofHom (X := (P.val ⊗ (unitDual.{uC, vC, r} R P).val).obj U)
    (Y := (unit (ringSheaf.{uC, vC, r} R)).val.obj U)
    (TensorProduct.lift (evalLinear.{uC, vC, r} R P U).flip)
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x phi
    exact eval_restrict.{uC, vC, r} R P f phi x

private noncomputable def evaluation (P : Modules.{uC, vC, r} R) :
    P ⊗ unitDual.{uC, vC, r} R P ⟶ unit (ringSheaf.{uC, vC, r} R) :=
  (tensorObjIsoSheafification P (unitDual.{uC, vC, r} R P)).hom ≫
    ((adj.{uC, vC, r} R).homEquiv
    (P.val ⊗ (unitDual.{uC, vC, r} R P).val) (unit (ringSheaf.{uC, vC, r} R))).symm
      (evalPresheaf.{uC, vC, r} R P)

private theorem evaluation_pure (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U) :
    (evaluation.{uC, vC, r} R P).val.app U
      (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U x phi) =
        phi.app (op (Over.mk (𝟙 U.unop))) x := by
  let A := P.val ⊗ (unitDual.{uC, vC, r} R P).val
  let H := unit (ringSheaf.{uC, vC, r} R)
  let k := ((adj.{uC, vC, r} R).homEquiv A H).symm (evalPresheaf.{uC, vC, r} R P)
  let t := ((adj.{uC, vC, r} R).unit.app A).app U (x ⊗ₜ[R.obj.obj U] phi)
  let e := tensorObjIsoSheafification P (unitDual.{uC, vC, r} R P)
  have h := ((adj.{uC, vC, r} R).homEquiv A H).apply_symm_apply
    (evalPresheaf.{uC, vC, r} R P)
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun m ↦ m.app U (x ⊗ₜ[R.obj.obj U] phi)) h
  have hi := congrArg (fun m ↦ m.val.app U t) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U t) = t at hi
  change k.val.app U (e.hom.val.app U (e.inv.val.app U t)) = _
  rw [hi]
  exact hh

attribute [local irreducible] evaluation pureTensor

omit [EssentiallySmall.{max uC vC r} C] in
private theorem chart_basis (P : Modules.{uC, vC, r} R) (W : C)
    (e : P.over W ≅ unit ((ringSheaf.{uC, vC, r} R).over W)) :
    ∃ p : P.val.obj (op W), ∃ phi : (unitDual.{uC, vC, r} R P).val.obj (op W),
      p = e.inv.val.app (op (Over.mk (𝟙 W))) (1 : R.obj.obj (op W)) ∧
      phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)) ∧
      ∀ (V : Over W) (x : P.val.obj (op V.left)),
        ∃ a : R.obj.obj (op V.left), x = a •
          (show P.val.obj (op V.left) from P.val.map V.hom.op p) := by
  let p : P.val.obj (op W) := e.inv.val.app (op (Over.mk (𝟙 W))) (1 : R.obj.obj (op W))
  refine ⟨p, e.hom.val, rfl, ?_, ?_⟩
  · exact congrArg (fun k ↦ k.val.app (op (Over.mk (𝟙 W))) (1 : R.obj.obj (op W))) e.inv_hom_id
  · intro V x
    refine ⟨e.hom.val.app (op V) x, ?_⟩
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 W)).op (1 : R.obj.obj (op W))
    have hp : P.val.map V.hom.op p = e.inv.val.app (op V) (1 : R.obj.obj (op V.left)) := by
      exact hn.symm.trans (congrArg (e.inv.val.app (op V)) (R.obj.map V.hom.op).hom.map_one)
    rw [hp]
    have h := congrArg (fun k ↦ k.val.app (op V) x) e.hom_inv_id
    change e.inv.val.app (op V) (e.hom.val.app (op V) x) = x at h
    calc
      x = e.inv.val.app (op V) (e.hom.val.app (op V) x) := h.symm
      _ = (show R.obj.obj (op V.left) from e.hom.val.app (op V) x) •
          (show P.val.obj (op V.left) from
            e.inv.val.app (op V) (1 : R.obj.obj (op V.left))) := by
        simpa only [smul_eq_mul, mul_one] using
          (e.inv.val.app (op V)).hom.map_smul (e.hom.val.app (op V) x)
            (1 : R.obj.obj (op V.left))

omit [EssentiallySmall.{max uC vC r} C] in
private theorem basis_eval_bijective (P : Modules.{uC, vC, r} R) {W : C}
    (p : P.val.obj (op W)) (phi : (unitDual.{uC, vC, r} R P).val.obj (op W))
    (hphi : phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)))
    (hgen : ∀ (V : Over W) (x : P.val.obj (op V.left)),
      ∃ a : R.obj.obj (op V.left), x = a • (show P.val.obj (op V.left) from P.val.map V.hom.op p)) :
    Function.Bijective (fun q : (unitDual.{uC, vC, r} R P).val.obj (op W) ↦
      q.app (op (Over.mk (𝟙 W))) p) := by
  change Function.Bijective (fun q ↦ evalLinear.{uC, vC, r} R P (op W) q p)
  refine ⟨?_, fun a ↦ ⟨a • phi, ?_⟩⟩
  · intro q q' hq
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := hgen V.unop x
    have h0 : q.app V (P.val.map V.unop.hom.op p) =
        q'.app V (P.val.map V.unop.hom.op p) := by
      have hqV := PresheafOfModules.naturality_apply q
        (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op p
      have hqV' := PresheafOfModules.naturality_apply q'
        (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op p
      exact hqV.trans ((congrArg ((unit (ringSheaf.{uC, vC, r} R)).val.map
        V.unop.hom.op) hq).trans hqV'.symm)
    change q.app V (a • _) = q'.app V (a • _)
    rw [map_smul, map_smul, h0]
  · change evalLinear.{uC, vC, r} R P (op W) (a • phi) p = a
    erw [map_smul, LinearMap.smul_apply]
    change a • (phi.app (op (Over.mk (𝟙 W))) p) = a
    rw [hphi]
    exact mul_one a

omit [EssentiallySmall.{max uC vC r} C] in
private theorem eval_bijective (P : Modules.{uC, vC, r} R) {W : C}
    (p : P.val.obj (op W)) (phi : (unitDual.{uC, vC, r} R P).val.obj (op W))
    (hphi : phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)))
    (hgen : ∀ (V : Over W) (x : P.val.obj (op V.left)),
      ∃ a : R.obj.obj (op V.left), x = a • (show P.val.obj (op V.left) from P.val.map V.hom.op p)) :
    Function.Bijective ((evalPresheaf.{uC, vC, r} R P).app (op W)) := by
  refine TensorProduct.lift_bijective_of_forall_eq_smul
    (evalLinear.{uC, vC, r} R P (op W)).flip p (fun x ↦ ?_)
    (basis_eval_bijective.{uC, vC, r} R P p phi hphi hgen)
  obtain ⟨a, ha⟩ := hgen (Over.mk (𝟙 W)) x
  refine ⟨a, ?_⟩
  change x = a • (show P.val.obj (op W) from P.val.map (𝟙 W).op p) at ha
  simpa only [op_id, PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply] using ha

private noncomputable def dualChartMap (P : Modules.{uC, vC, r} R) (W : C)
    (e : P.over W ≅ unit ((ringSheaf.{uC, vC, r} R).over W)) :
    (unitDual.{uC, vC, r} R P).over W ⟶ unit ((ringSheaf.{uC, vC, r} R).over W) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := ((unitDual.{uC, vC, r} R P).over W).val.obj V)
        (Y := (unit ((ringSheaf.{uC, vC, r} R).over W)).val.obj V)
        ((evalLinear.{uC, vC, r} R P (op V.unop.left)).flip
          (e.inv.val.app V (1 : R.obj.obj (op V.unop.left))))
      naturality := by
        intro V V' f
        ext phi
        let p := e.inv.val.app V (1 : R.obj.obj (op V.unop.left))
        have hp : P.val.map f.unop.left.op p =
            e.inv.val.app V' (1 : R.obj.obj (op V'.unop.left)) := by
          have h := PresheafOfModules.naturality_apply e.inv.val f
            (1 : R.obj.obj (op V.unop.left))
          exact h.symm.trans (congrArg (e.inv.val.app V')
            (R.obj.map f.unop.left.op).hom.map_one)
        change evalLinear.{uC, vC, r} R P (op V'.unop.left)
            ((unitDual.{uC, vC, r} R P).val.map f.unop.left.op phi)
            (e.inv.val.app V' (1 : R.obj.obj (op V'.unop.left))) = _
        rw [← hp]
        exact eval_restrict.{uC, vC, r} R P f.unop.left.op phi p }

attribute [local irreducible] dualChartMap

omit [EssentiallySmall.{max uC vC r} C] in
private theorem dualChart_isIso (P : Modules.{uC, vC, r} R) (W : C)
    (e : P.over W ≅ unit ((ringSheaf.{uC, vC, r} R).over W)) :
    IsIso (dualChartMap.{uC, vC, r} R P W e) := by
  rw [← isIso_iff_of_reflects_iso _ (forget ((ringSheaf.{uC, vC, r} R).over W)),
    ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).2
  obtain ⟨p, phi, rfl, hp, hg⟩ := chart_basis.{uC, vC, r} R P W e
  let pV : P.val.obj (op V.unop.left) :=
    e.inv.val.app V (1 : R.obj.obj (op V.unop.left))
  have hpV : P.val.map V.unop.hom.op
      (e.inv.val.app (op (Over.mk (𝟙 W))) (1 : R.obj.obj (op W))) = pV := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op
      (1 : R.obj.obj (op W))
    exact hn.symm.trans (congrArg (e.inv.val.app V)
      (R.obj.map V.unop.hom.op).hom.map_one)
  have hphi : evalLinear.{uC, vC, r} R P (op V.unop.left)
      ((unitDual.{uC, vC, r} R P).val.map V.unop.hom.op phi) pV = 1 := by
    rw [← hpV, eval_restrict.{uC, vC, r}]
    change R.obj.map V.unop.hom.op
      (phi.app (op (Over.mk (𝟙 W))) _) = 1
    rw [hp]
    exact (R.obj.map V.unop.hom.op).hom.map_one
  have hgen (T : Over V.unop.left) (x : P.val.obj (op T.left)) :
      ∃ a : R.obj.obj (op T.left), x = a •
        (show P.val.obj (op T.left) from P.val.map T.hom.op pV) := by
    obtain ⟨a, ha⟩ := hg (Over.mk (T.hom ≫ V.unop.hom)) x
    refine ⟨a, ?_⟩
    rw [← hpV]
    change x = a • (show P.val.obj (op T.left) from
      P.val.map (T.hom ≫ V.unop.hom).op _) at ha
    simpa only [op_comp, PresheafOfModules.map_comp_apply] using ha
  unfold dualChartMap
  exact basis_eval_bijective.{uC, vC, r} R P pV
    ((unitDual.{uC, vC, r} R P).val.map V.unop.hom.op phi) hphi hgen

private theorem evaluation_isIso (P : Modules.{uC, vC, r} R)
    (hP : ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit ((ringSheaf.{uC, vC, r} R).over V))) :
    IsIso (evaluation.{uC, vC, r} R P) := by
  let q := evalPresheaf.{uC, vC, r} R P
  have localbij {U V : C} (f : V ⟶ U)
      (e : P.over V ≅ unit ((ringSheaf.{uC, vC, r} R).over V)) :
      Function.Bijective (q.app (op V)) := by
    obtain ⟨p, phi, _, hp, hg⟩ := chart_basis.{uC, vC, r} R P V e
    exact eval_bijective.{uC, vC, r} R P p phi hp hg
  have : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map q) :=
    ⟨fun {U} x y h ↦ by
      obtain ⟨s, hs, he⟩ := hP U.unop
      apply J.superset_covering _ hs
      intro V f hf
      obtain ⟨e⟩ := he V f hf
      apply (localbij f e).1
      change q.app (op V) ((P.val ⊗ (unitDual.{uC, vC, r} R P).val).map f.op x) =
        q.app (op V) ((P.val ⊗ (unitDual.{uC, vC, r} R P).val).map f.op y)
      rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
      exact congrArg (_ : _ → _) h⟩
  have : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map q) :=
    ⟨fun {U} x ↦ by
      obtain ⟨s, hs, he⟩ := hP U
      apply J.superset_covering _ hs
      intro V f hf
      obtain ⟨e⟩ := he V f hf
      exact (localbij f e).2 _⟩
  have hw : (J.W.inverseImage (PresheafOfModules.toPresheaf _)) q := by
    rw [MorphismProperty.inverseImage_iff]
    exact (J.W_iff_isLocallyBijective _).mpr ⟨inferInstance, inferInstance⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (ringSheaf.{uC, vC, r} R).obj)] at hw
  have : IsIso ((PresheafOfModules.sheafification (𝟙 (ringSheaf.{uC, vC, r} R).obj)).map q) := hw
  unfold evaluation
  rw [Adjunction.homEquiv_counit]
  infer_instance

private noncomputable local instance (M : Modules.{uC, vC, r} R) (U : Cᵒᵖ) :
    SMul ((unit (ringSheaf.{uC, vC, r} R)).val.obj U) (M.val.obj U) :=
  inferInstanceAs (SMul (R.obj.obj U) (M.val.obj U))

private theorem cancellation_pure (P Q M : Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit (ringSheaf.{uC, vC, r} R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (p : P.val.obj U) (q : Q.val.obj U) :
    ((cancellation.{uC, vC, r} R P Q e).hom.app M).val.app U
      (pureTensor.{uC, vC, r} R (M ⊗ P) Q U (pureTensor.{uC, vC, r} R M P U x p) q) =
        e.hom.val.app U (pureTensor.{uC, vC, r} R P Q U p q) • x := by
  change (ρ_ M).hom.val.app U
    ((M ◁ e.hom).val.app U ((α_ M P Q).hom.val.app U _)) = _
  rw [pure_assoc.{uC, vC, r}]
  have hm := pure_map.{uC, vC, r} R (𝟙 M) e.hom U x (pureTensor.{uC, vC, r} R P Q U p q)
  rw [id_tensorHom] at hm
  rw [hm]
  exact pure_right_unitor.{uC, vC, r} R M U x _

attribute [local irreducible] cancellation

private theorem cancellation_inv_pure (P Q M : Modules.{uC, vC, r} R)
    (e : P ⊗ Q ≅ unit (ringSheaf.{uC, vC, r} R)) (U : Cᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U)
    (hp : e.hom.val.app U (pureTensor.{uC, vC, r} R P Q U p q) = (1 : R.obj.obj U))
    (x : M.val.obj U) :
    ((cancellation.{uC, vC, r} R P Q e).inv.app M).val.app U x =
      pureTensor.{uC, vC, r} R (M ⊗ P) Q U (pureTensor.{uC, vC, r} R M P U x p) q := by
  have he : Function.Injective (((cancellation.{uC, vC, r} R P Q e).hom.app M).val.app U) :=
    ((SheafOfModules.evaluation (ringSheaf.{uC, vC, r} R) U).mapIso
      ((cancellation.{uC, vC, r} R P Q e).app M)).toLinearEquiv.injective
  apply he
  have hi := congrArg (fun k ↦ k.val.app U x) ((cancellation.{uC, vC, r} R P Q e).inv_hom_id_app M)
  change ((cancellation.{uC, vC, r} R P Q e).hom.app M).val.app U
    (((cancellation.{uC, vC, r} R P Q e).inv.app M).val.app U x) = x at hi
  rw [hi, cancellation_pure.{uC, vC, r}, hp, one_smul]

private theorem tensor_linear (P : Modules.{uC, vC, r} R) :
    (tensorRight P).Linear (scalars.{uC, vC, r} R) := by
  constructor
  intro M N f a
  apply pure_hom_ext.{uC, vC, r} R M P (N ⊗ P)
  intro U x p
  have hm := pure_map.{uC, vC, r} R (a • f) (𝟙 P) U x p
  have hn := pure_map.{uC, vC, r} R f (𝟙 P) U x p
  rw [tensorHom_id] at hm hn
  change ((tensorRight P).map (a • f)).val.app U (pureTensor.{uC, vC, r} R M P U x p) = _ at hm
  erw [hm]
  change pureTensor.{uC, vC, r} R N P U (a.1 U • f.val.app U x) p =
    a.1 U • ((f ▷ P).val.app U (pureTensor.{uC, vC, r} R M P U x p))
  rw [hn, pure_smul_left.{uC, vC, r}]
  rfl

private theorem pure_restrict (M N : Modules.{uC, vC, r} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.map f (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R M N V (M.val.map f x) (N.val.map f y) := by
  let z := x ⊗ₜ[R.obj.obj U] y
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val f
      (((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val)).app U z)
  have hu := PresheafOfModules.naturality_apply
    ((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val)) f z
  unfold pureTensor
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

omit [EssentiallySmall.{max uC vC r} C] in
private theorem section_ext (M : Modules.{uC, vC, r} R) {U : Cᵒᵖ} (x y : M.val.obj U)
    (s : Sieve U.unop) (hs : s ∈ J U.unop)
    (h : ∀ V (f : V ⟶ U.unop), s f → M.val.map f.op x = M.val.map f.op y) : x = y := by
  have hM := Presheaf.isSheaf_comp_of_isSheaf J _ (CategoryTheory.forget AddCommGrpCat) M.isSheaf
  exact (((isSheaf_iff_isSheaf_of_type J _).mp hM).isSeparated _ hs).ext h

private noncomputable def siteRightIso (P : Modules.{uC, vC, r} R) :
    tensorRight P ≅ siteSheafTensorRight P :=
  (siteSheafTensorRightIso R P).symm

private theorem eval_scaled (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (p : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U)
    (hp : phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U))
    (a b : R.obj.obj U) :
    (evaluation.{uC, vC, r} R P).val.app U
      (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U (a • p) (b • phi)) = a * b := by
  rw [evaluation_pure.{uC, vC, r}]
  change evalLinear.{uC, vC, r} R P U (b • phi) (a • p) = _
  rw [(evalLinear.{uC, vC, r} R P U (b • phi)).map_smul]
  erw [(evalLinear.{uC, vC, r} R P U).map_smul, LinearMap.smul_apply]
  change a * (b * evalLinear.{uC, vC, r} R P U phi p) = _
  rw [show evalLinear.{uC, vC, r} R P U phi p = 1 from hp, mul_one]

private theorem pure_units (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (u : (R.obj.obj U)ˣ) :
    pureTensor.{uC, vC, r} R M N U ((u : R.obj.obj U) • x)
        ((↑(u⁻¹) : R.obj.obj U) • y) = pureTensor.{uC, vC, r} R M N U x y := by
  rw [pure_smul_left.{uC, vC, r}, pure_smul_right.{uC, vC, r}, smul_smul, Units.mul_inv, one_smul]

private theorem pure_units_nested (M N H : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) (u : (R.obj.obj U)ˣ) :
    pureTensor.{uC, vC, r} R (M ⊗ N) H U
        (pureTensor.{uC, vC, r} R M N U x ((u : R.obj.obj U) • y))
        ((↑(u⁻¹) : R.obj.obj U) • z) =
      pureTensor.{uC, vC, r} R (M ⊗ N) H U (pureTensor.{uC, vC, r} R M N U x y) z := by
  rw [pure_smul_right.{uC, vC, r} R M N U, pure_units.{uC, vC, r}]

omit [EssentiallySmall.{max uC vC r} C] in
private theorem local_generators (P : Modules.{uC, vC, r} R) (W : C)
    (e : P.over W ≅ unit ((ringSheaf.{uC, vC, r} R).over W)) :
    ∃ p : P.val.obj (op W), ∃ phi : (unitDual.{uC, vC, r} R P).val.obj (op W),
      phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)) ∧
      (∀ x : P.val.obj (op W), ∃ a : R.obj.obj (op W), x = a • p) ∧
      (∀ q : (unitDual.{uC, vC, r} R P).val.obj (op W), ∃ a : R.obj.obj (op W), q = a • phi) := by
  obtain ⟨p, phi, _, hp, hg⟩ := chart_basis.{uC, vC, r} R P W e
  refine ⟨p, phi, hp, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hg (Over.mk (𝟙 W)) x
    refine ⟨a, ?_⟩
    change x = a • (show P.val.obj (op W) from P.val.map (𝟙 W).op p) at ha
    simpa only [op_id, PresheafOfModules.map_id,
      ModuleCat.restrictScalarsId'_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply] using ha
  · intro q
    refine ⟨q.app (op (Over.mk (𝟙 W))) p, ?_⟩
    apply (basis_eval_bijective.{uC, vC, r} R P p phi hp hg).1
    change evalLinear.{uC, vC, r} R P (op W) q p =
      evalLinear.{uC, vC, r} R P (op W) (evalLinear.{uC, vC, r} R P (op W) q p • phi) p
    rw [map_smul, LinearMap.smul_apply]
    change evalLinear.{uC, vC, r} R P (op W) q p =
      evalLinear.{uC, vC, r} R P (op W) q p *
        evalLinear.{uC, vC, r} R P (op W) phi p
    rw [show evalLinear.{uC, vC, r} R P (op W) phi p = 1 from hp, mul_one]

private theorem tensor_triangles (P : Modules.{uC, vC, r} R)
    (hP : ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit ((ringSheaf.{uC, vC, r} R).over V)))
    (e : P ⊗ unitDual.{uC, vC, r} R P ≅ unit (ringSheaf.{uC, vC, r} R))
    (he : e.hom = evaluation.{uC, vC, r} R P) :
    let a := cancellation.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) e
    let b := cancellation.{uC, vC, r} R (unitDual.{uC, vC, r} R P) P
      ((β_ (unitDual.{uC, vC, r} R P) P) ≪≫ e)
    (∀ M : Modules.{uC, vC, r} R, (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _) ∧
    (∀ M : Modules.{uC, vC, r} R, a.inv.app (M ⊗ unitDual.{uC, vC, r} R P) ≫
      (tensorRight (unitDual.{uC, vC, r} R P)).map (b.hom.app M) = 𝟙 _) := by
  dsimp only
  let Q := unitDual.{uC, vC, r} R P
  let a := cancellation.{uC, vC, r} R P Q e
  let e' : Q ⊗ P ≅ unit (ringSheaf.{uC, vC, r} R) := (β_ Q P) ≪≫ e
  let b := cancellation.{uC, vC, r} R Q P e'
  have eval' (U : Cᵒᵖ) (p : P.val.obj U) (phi : Q.val.obj U) :
      e'.hom.val.app U (pureTensor.{uC, vC, r} R Q P U phi p) =
        phi.app (op (Over.mk (𝟙 U.unop))) p := by
    change e.hom.val.app U ((β_ Q P).hom.val.app U _) = _
    rw [pure_braiding.{uC, vC, r}, he, evaluation_pure.{uC, vC, r}]
  have hfirst (M : Modules.{uC, vC, r} R) :
      (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _ := by
    let t := (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P)
    apply pure_hom_ext.{uC, vC, r} R M P (M ⊗ P)
    intro U x y
    obtain ⟨s, hs, hc⟩ := hP U.unop
    apply section_ext.{uC, vC, r} R (M ⊗ P) _ _ s hs
    intro V f hf
    change (M ⊗ P).val.map f.op (t.val.app U _) = _
    erw [← PresheafOfModules.naturality_apply t.val f.op]
    change t.val.app (op V)
      ((M ⊗ P).val.map f.op (pureTensor.{uC, vC, r} R M P U x y)) =
      (M ⊗ P).val.map f.op (pureTensor.{uC, vC, r} R M P U x y)
    rw [pure_restrict.{uC, vC, r}]
    obtain ⟨chart⟩ := hc V f hf
    obtain ⟨p, phi, hp, hgen, _⟩ := local_generators.{uC, vC, r} R P V chart
    obtain ⟨c, hy⟩ := hgen (P.val.map f.op y)
    rw [hy]
    let xV : M.val.obj (op V) := M.val.map f.op x
    change (b.hom.app (M ⊗ P)).val.app (op V)
      ((a.inv.app M ▷ P).val.app (op V)
        (pureTensor.{uC, vC, r} R M P (op V) xV (c • p))) =
      pureTensor.{uC, vC, r} R M P (op V) xV (c • p)
    have hm := pure_map.{uC, vC, r} R (a.inv.app M) (𝟙 P) (op V) xV (c • p)
    rw [tensorHom_id] at hm
    simp only [id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hm
    refine (congrArg ((b.hom.app (M ⊗ P)).val.app (op V)) hm).trans ?_
    have ehp : e.hom.val.app (op V)
        (pureTensor.{uC, vC, r} R P Q (op V) p phi) = (1 : R.obj.obj (op V)) := by
      rw [he, evaluation_pure.{uC, vC, r}]
      exact hp
    rw [cancellation_inv_pure.{uC, vC, r} R P Q M e (op V) p phi ehp]
    erw [cancellation_pure.{uC, vC, r} R Q P (M ⊗ P) e', eval']
    have hp' : evalLinear.{uC, vC, r} R P (op V) phi (c • p) = c := by
      exact ((evalLinear.{uC, vC, r} R P (op V) phi).map_smul c p).trans
        ((congrArg (fun z : R.obj.obj (op V) ↦ c * z) hp).trans (mul_one c))
    change evalLinear.{uC, vC, r} R P (op V) phi (c • p) •
      pureTensor.{uC, vC, r} R M P (op V) xV p = _
    exact (congrArg (fun z : R.obj.obj (op V) ↦
      z • pureTensor.{uC, vC, r} R M P (op V) xV p) hp').trans
      (pure_smul_right.{uC, vC, r} R M P (op V) c xV p).symm
  let equiv : Modules.{uC, vC, r} R ≌ Modules.{uC, vC, r} R :=
    ⟨tensorRight P, tensorRight Q, a.symm, b, hfirst⟩
  exact ⟨hfirst, equiv.unit_inverse_comp⟩

private theorem evaluation_inverse_pair_impl (P : Modules.{uC, vC, r} R)
    (hP : ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))) :
    (∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty ((unitDual.{uC, vC, r} R P).over V ≅ unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))) ∧
    (tensorRight P).Additive ∧ (tensorRight (unitDual.{uC, vC, r} R P)).Additive ∧
    PreservesFiniteLimits (tensorRight P) ∧ PreservesFiniteColimits (tensorRight P) ∧
    PreservesFiniteLimits (tensorRight (unitDual.{uC, vC, r} R P)) ∧
    PreservesFiniteColimits (tensorRight (unitDual.{uC, vC, r} R P)) ∧
    IsFlatOnSite (R := R) P ∧ IsFlatOnSite (R := R) (unitDual.{uC, vC, r} R P) ∧
    (tensorRight P).Linear (scalars.{uC, vC, r} R) ∧
    (tensorRight (unitDual.{uC, vC, r} R P)).Linear (scalars.{uC, vC, r} R) ∧
    ∃ e : P ⊗ unitDual.{uC, vC, r} R P ≅ unit (ringSheaf.{uC, vC, r} R),
      (∀ (U : Cᵒᵖ) (x : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U),
        e.hom.val.app U (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U x phi) =
          phi.app (op (Over.mk (𝟙 U.unop))) x) ∧
      (∀ (U : Cᵒᵖ) (p : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U),
        phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U) →
        (∀ a b : R.obj.obj U,
          e.hom.val.app U
            (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U (a • p) (b • phi)) =
              a * b) ∧
        (∀ a : R.obj.obj U, e.inv.val.app U a =
          pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U (a • p) phi) ∧
        (∀ (u : (R.obj.obj U)ˣ) (a : R.obj.obj U),
          pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U
              (a • ((u : R.obj.obj U) • p)) ((↑(u⁻¹) : R.obj.obj U) • phi) =
            pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U (a • p) phi)) ∧
      ∃ a : tensorRight P ⋙ tensorRight (unitDual.{uC, vC, r} R P) ≅ 𝟭 _,
      ∃ b : tensorRight (unitDual.{uC, vC, r} R P) ⋙ tensorRight P ≅ 𝟭 _,
        a = cancellation.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) e ∧
        b = cancellation.{uC, vC, r} R (unitDual.{uC, vC, r} R P) P
          ((β_ (unitDual.{uC, vC, r} R P) P) ≪≫ e) ∧
        (∀ M : Modules.{uC, vC, r} R,
          (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _) ∧
        (∀ M : Modules.{uC, vC, r} R,
          a.inv.app (M ⊗ unitDual.{uC, vC, r} R P) ≫
            (tensorRight (unitDual.{uC, vC, r} R P)).map (b.hom.app M) = 𝟙 _) ∧
        (∀ (M : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
            (p : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U),
          phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U) →
          (∀ (x : M.val.obj U) (c d : R.obj.obj U),
            (a.hom.app M).val.app U
                (pureTensor.{uC, vC, r} R (M ⊗ P) (unitDual.{uC, vC, r} R P) U
                  (pureTensor.{uC, vC, r} R M P U x (c • p)) (d • phi)) = (c * d) • x) ∧
          (∀ x : M.val.obj U,
            (a.inv.app M).val.app U x =
              pureTensor.{uC, vC, r} R (M ⊗ P) (unitDual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x p) phi) ∧
          (∀ (x : M.val.obj U) (c d : R.obj.obj U),
            (b.hom.app M).val.app U
                (pureTensor.{uC, vC, r} R (M ⊗ unitDual.{uC, vC, r} R P) P U
                  (pureTensor.{uC, vC, r} R M (unitDual.{uC, vC, r} R P) U x (d • phi))
                  (c • p)) = (c * d) • x) ∧
          (∀ x : M.val.obj U,
            (b.inv.app M).val.app U x =
              pureTensor.{uC, vC, r} R (M ⊗ unitDual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (unitDual.{uC, vC, r} R P) U x phi) p) ∧
          (∀ (u : (R.obj.obj U)ˣ) (x : M.val.obj U),
            pureTensor.{uC, vC, r} R (M ⊗ P) (unitDual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x ((u : R.obj.obj U) • p))
                ((↑(u⁻¹) : R.obj.obj U) • phi) =
              pureTensor.{uC, vC, r} R (M ⊗ P) (unitDual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x p) phi) ∧
          (∀ (u : (R.obj.obj U)ˣ) (x : M.val.obj U),
            pureTensor.{uC, vC, r} R (M ⊗ unitDual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (unitDual.{uC, vC, r} R P) U x
                  ((↑(u⁻¹) : R.obj.obj U) • phi)) ((u : R.obj.obj U) • p) =
              pureTensor.{uC, vC, r} R (M ⊗ unitDual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (unitDual.{uC, vC, r} R P) U x phi) p)) := by
  have := evaluation_isIso.{uC, vC, r} R P hP
  let Q := unitDual.{uC, vC, r} R P
  let e : P ⊗ Q ≅ unit (ringSheaf.{uC, vC, r} R) := asIso (evaluation.{uC, vC, r} R P)
  let e' : Q ⊗ P ≅ unit (ringSheaf.{uC, vC, r} R) := (β_ Q P) ≪≫ e
  let a := cancellation.{uC, vC, r} R P Q e
  let b := cancellation.{uC, vC, r} R Q P e'
  let equiv : Modules.{uC, vC, r} R ≌ Modules.{uC, vC, r} R :=
    ⟨tensorRight P, tensorRight Q, a.symm, b,
      (tensor_triangles.{uC, vC, r} R P hP e rfl).1⟩
  have : (tensorRight P).IsEquivalence := equiv.isEquivalence_functor
  have : (tensorRight Q).IsEquivalence := equiv.isEquivalence_inverse
  have hpLim : PreservesFiniteLimits (tensorRight P) := inferInstance
  have hpColim : PreservesFiniteColimits (tensorRight P) := inferInstance
  have hqLim : PreservesFiniteLimits (tensorRight Q) := inferInstance
  have hqColim : PreservesFiniteColimits (tensorRight Q) := inferInstance
  have flat (L : Modules.{uC, vC, r} R)
      (hl : PreservesFiniteLimits (tensorRight L))
      (hc : PreservesFiniteColimits (tensorRight L)) : IsFlatOnSite (R := R) L := by
    exact (ObjectProperty.prop_of_iso (CategoryTheory.exactFunctor _ _)
      (siteRightIso.{uC, vC, r} R L) ⟨hl, hc⟩)
  refine ⟨?_, inferInstance, inferInstance, hpLim, hpColim, hqLim, hqColim,
    flat P hpLim hpColim, flat Q hqLim hqColim, tensor_linear.{uC, vC, r} R P,
    tensor_linear.{uC, vC, r} R Q, e, ?_, ?_, a, b,
    rfl, rfl, ?_, ?_, ?_⟩
  · intro U
    obtain ⟨s, hs, hc⟩ := hP U
    refine ⟨s, hs, ?_⟩
    intro V f hf
    obtain ⟨chart⟩ := hc V f hf
    have := dualChart_isIso.{uC, vC, r} R P V chart
    exact ⟨asIso (dualChartMap.{uC, vC, r} R P V chart)⟩
  · exact evaluation_pure.{uC, vC, r} R P
  · intro U p phi hp
    refine ⟨eval_scaled.{uC, vC, r} R P U p phi hp, ?_, ?_⟩
    · intro c
      have hi : Function.Injective (e.hom.val.app U) :=
        ((SheafOfModules.evaluation (ringSheaf.{uC, vC, r} R) U).mapIso e).toLinearEquiv.injective
      apply hi
      have h := congrArg (fun k ↦ k.val.app U c) e.inv_hom_id
      change e.hom.val.app U (e.inv.val.app U c) = c at h
      refine h.trans ?_
      change c = (evaluation.{uC, vC, r} R P).val.app U (pureTensor.{uC, vC, r} R P Q U (c • p) phi)
      erw [evaluation_pure.{uC, vC, r}, map_smul, hp]
      exact (mul_one c).symm
    · intro u c
      have h : c • ((u : R.obj.obj U) • p) = (u : R.obj.obj U) • (c • p) :=
        smul_comm c (u : R.obj.obj U) p
      rw [h]
      exact pure_units.{uC, vC, r} R P Q U (c • p) phi u
  · exact (tensor_triangles.{uC, vC, r} R P hP e rfl).1
  · exact (tensor_triangles.{uC, vC, r} R P hP e rfl).2
  · intro M U p phi hp
    have he : e.hom.val.app U (pureTensor.{uC, vC, r} R P Q U p phi) = (1 : R.obj.obj U) := by
      exact (evaluation_pure.{uC, vC, r} R P U p phi).trans hp
    have he' : e'.hom.val.app U (pureTensor.{uC, vC, r} R Q P U phi p) = (1 : R.obj.obj U) := by
      change e.hom.val.app U ((β_ Q P).hom.val.app U _) = _
      rw [pure_braiding.{uC, vC, r}]
      exact he
    refine ⟨?_, cancellation_inv_pure.{uC, vC, r} R P Q M e U p phi he, ?_,
      cancellation_inv_pure.{uC, vC, r} R Q P M e' U phi p he', ?_, ?_⟩
    · intro x c d
      erw [cancellation_pure.{uC, vC, r}]
      change (evaluation.{uC, vC, r} R P).val.app U
        (pureTensor.{uC, vC, r} R P Q U (c • p) (d • phi)) • x = _
      erw [eval_scaled.{uC, vC, r} R P U p phi hp]
    · intro x c d
      erw [cancellation_pure.{uC, vC, r}]
      change e.hom.val.app U ((β_ Q P).hom.val.app U
        (pureTensor.{uC, vC, r} R Q P U (d • phi) (c • p))) • x = _
      rw [pure_braiding.{uC, vC, r}]
      change (evaluation.{uC, vC, r} R P).val.app U
        (pureTensor.{uC, vC, r} R P Q U (c • p) (d • phi)) • x = _
      erw [eval_scaled.{uC, vC, r} R P U p phi hp]
    · intro u x
      exact pure_units_nested.{uC, vC, r} R M P Q U x p phi u
    · intro u x
      simpa only [inv_inv] using pure_units_nested.{uC, vC, r} R M Q P U x phi p u⁻¹

/-- A locally trivial line and its internal dual have the specified evaluation and
inverse tensor equivalences. The equations characterize evaluation on images of pure
presheaf tensors; the local equations hold for every normalized section pair. The
natural isomorphisms are explicitly the reassociation/evaluation/unitor composites.
Linearity over global sections implies the asserted B-linearity by restriction along
any ring homomorphism B → Γ(R); all displayed components are R-module morphisms.

Source: Stacks Project, Modules on Sites, Tags 0B8Q and 0B8N.
(blueprint: lem-pur-sheaf-line-evaluation-inverse-pair)

Proof plan:
1. On each trivializing slice write P = Rp. Restricting internal Hom is
   relocalization, so evaluation at p identifies the dual with R, with basis phi
   satisfying phi(p) = 1. Changing p to up changes phi to u⁻¹phi.
2. Construct the sectionwise bilinear evaluation as a map of presheaf tensors.
   The sheafification adjunction and the canonical tensor comparison induce the
   sheaf evaluation map, with its asserted value on every pure tensor.
3. On a trivializing slice, evaluation on the basis identifies dual sections
   with scalars, and tensor evaluation is bijective. Thus presheaf evaluation is
   locally bijective. Sheafification inverts it, proving evaluation is an
   isomorphism without choosing or gluing an inverse separately.
4. Reassociate, evaluate the last factors, and apply the right unitor. Naturality
   of tensor and the constraints gives the two natural isomorphisms a and b.
5. Their local inverses insert p tensor phi, respectively phi tensor p.
   Balancing proves the four local formulas and their invariance under basis change.
6. Evaluate the first triangle on x tensor cp. It gives the original tensor.
   Pure-tensor extensionality and separatedness make this equation global.
   With this triangle, the specified maps define an equivalence; the general
   second triangle of an equivalence gives the other required equation.
7. Thus the functors are inverse additive equivalences. Equivalences preserve
   limits and colimits; hence they are exact and both factors are flat.
8. Sectionwise tensoring commutes with addition and scalar multiplication on maps.
   Evaluation, constraints and their inverses are module morphisms, so their
   components are linear over every B acting through R.
-/
theorem evaluation_inverse_pair (P : Modules.{uC, vC, r} R)
    (hP : ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty (P.over V ≅ unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))) :
    (∀ U : C, ∃ s : Sieve U, s ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), s f →
        Nonempty ((dual.{uC, vC, r} R P).over V ≅ unit
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))) ∧
    (tensorRight P).Additive ∧ (tensorRight (dual.{uC, vC, r} R P)).Additive ∧
    PreservesFiniteLimits (tensorRight P) ∧ PreservesFiniteColimits (tensorRight P) ∧
    PreservesFiniteLimits (tensorRight (dual.{uC, vC, r} R P)) ∧
    PreservesFiniteColimits (tensorRight (dual.{uC, vC, r} R P)) ∧
    IsFlatOnSite (R := R) P ∧ IsFlatOnSite (R := R) (dual.{uC, vC, r} R P) ∧
    (tensorRight P).Linear (scalars.{uC, vC, r} R) ∧
    (tensorRight (dual.{uC, vC, r} R P)).Linear (scalars.{uC, vC, r} R) ∧
    ∃ e : P ⊗ dual.{uC, vC, r} R P ≅ 𝟙_ (Modules.{uC, vC, r} R),
      (∀ (U : Cᵒᵖ) (x : P.val.obj U) (phi : (dual.{uC, vC, r} R P).val.obj U),
        e.hom.val.app U (pureTensor.{uC, vC, r} R P (dual.{uC, vC, r} R P) U x phi) =
          phi.app (op (Over.mk (𝟙 U.unop))) x) ∧
      (∀ (U : Cᵒᵖ) (p : P.val.obj U) (phi : (dual.{uC, vC, r} R P).val.obj U),
        phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U) →
        (∀ a b : R.obj.obj U,
          e.hom.val.app U
            (pureTensor.{uC, vC, r} R P (dual.{uC, vC, r} R P) U (a • p) (b • phi)) =
              a * b) ∧
        (∀ a : R.obj.obj U, e.inv.val.app U a =
          pureTensor.{uC, vC, r} R P (dual.{uC, vC, r} R P) U (a • p) phi) ∧
        (∀ (u : (R.obj.obj U)ˣ) (a : R.obj.obj U),
          pureTensor.{uC, vC, r} R P (dual.{uC, vC, r} R P) U
              (a • ((u : R.obj.obj U) • p)) ((↑(u⁻¹) : R.obj.obj U) • phi) =
            pureTensor.{uC, vC, r} R P (dual.{uC, vC, r} R P) U (a • p) phi)) ∧
      ∃ a : tensorRight P ⋙ tensorRight (dual.{uC, vC, r} R P) ≅ 𝟭 _,
      ∃ b : tensorRight (dual.{uC, vC, r} R P) ⋙ tensorRight P ≅ 𝟭 _,
        a = cancellation.{uC, vC, r} R P (dual.{uC, vC, r} R P) e ∧
        b = cancellation.{uC, vC, r} R (dual.{uC, vC, r} R P) P
          ((β_ (dual.{uC, vC, r} R P) P) ≪≫ e) ∧
        (∀ M : Modules.{uC, vC, r} R,
          (tensorRight P).map (a.inv.app M) ≫ b.hom.app (M ⊗ P) = 𝟙 _) ∧
        (∀ M : Modules.{uC, vC, r} R,
          a.inv.app (M ⊗ dual.{uC, vC, r} R P) ≫
            (tensorRight (dual.{uC, vC, r} R P)).map (b.hom.app M) = 𝟙 _) ∧
        (∀ (M : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
            (p : P.val.obj U) (phi : (dual.{uC, vC, r} R P).val.obj U),
          phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U) →
          (∀ (x : M.val.obj U) (c d : R.obj.obj U),
            (a.hom.app M).val.app U
                (pureTensor.{uC, vC, r} R (M ⊗ P) (dual.{uC, vC, r} R P) U
                  (pureTensor.{uC, vC, r} R M P U x (c • p)) (d • phi)) = (c * d) • x) ∧
          (∀ x : M.val.obj U,
            (a.inv.app M).val.app U x =
              pureTensor.{uC, vC, r} R (M ⊗ P) (dual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x p) phi) ∧
          (∀ (x : M.val.obj U) (c d : R.obj.obj U),
            (b.hom.app M).val.app U
                (pureTensor.{uC, vC, r} R (M ⊗ dual.{uC, vC, r} R P) P U
                  (pureTensor.{uC, vC, r} R M (dual.{uC, vC, r} R P) U x (d • phi))
                  (c • p)) = (c * d) • x) ∧
          (∀ x : M.val.obj U,
            (b.inv.app M).val.app U x =
              pureTensor.{uC, vC, r} R (M ⊗ dual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (dual.{uC, vC, r} R P) U x phi) p) ∧
          (∀ (u : (R.obj.obj U)ˣ) (x : M.val.obj U),
            pureTensor.{uC, vC, r} R (M ⊗ P) (dual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x ((u : R.obj.obj U) • p))
                ((↑(u⁻¹) : R.obj.obj U) • phi) =
              pureTensor.{uC, vC, r} R (M ⊗ P) (dual.{uC, vC, r} R P) U
                (pureTensor.{uC, vC, r} R M P U x p) phi) ∧
          (∀ (u : (R.obj.obj U)ˣ) (x : M.val.obj U),
            pureTensor.{uC, vC, r} R (M ⊗ dual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (dual.{uC, vC, r} R P) U x
                  ((↑(u⁻¹) : R.obj.obj U) • phi)) ((u : R.obj.obj U) • p) =
              pureTensor.{uC, vC, r} R (M ⊗ dual.{uC, vC, r} R P) P U
                (pureTensor.{uC, vC, r} R M (dual.{uC, vC, r} R P) U x phi) p)) := by
  exact evaluation_inverse_pair_impl.{uC, vC, r} R P hP

end SheafOfModules.LineEvaluation
