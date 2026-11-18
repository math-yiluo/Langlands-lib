import Langlands.GroupScheme.RelativeUnipotent.DisjointFreeModuleReconstruction

/-! # Actual linear module comparisons between natural point charts -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

open NaturalModuleTransformations

variable {S : Scheme.{u}} (V : GroupScheme S) (M : S.Modules)

/-- Natural charts of the original represented group into the sections of one
actual module sheaf, on all scheme tests. -/
structure ModulePointCharts where
  equiv : ∀ T : Over S, (T ⟶ V.X) ≃*
    Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M))
  natural : ∀ (T W : Over S) (b : W ⟶ T) (x : T ⟶ V.X),
    (equiv W (b ≫ x)).toAdd = sectionPullback M b (equiv T x).toAdd

namespace ModulePointCharts

variable {V M} {N P : S.Modules}
  (C : ModulePointCharts V M) (D : ModulePointCharts V N)

/-- Change the actual module sections by retaining the same original group
point in both charts. -/
def transition (T : Over S) :
    GlobalSections ((Scheme.Modules.pullback T.hom).obj M) ≃+
      GlobalSections ((Scheme.Modules.pullback T.hom).obj N) where
  toFun x := (D.equiv T ((C.equiv T).symm (Multiplicative.ofAdd x))).toAdd
  invFun x := (C.equiv T ((D.equiv T).symm (Multiplicative.ofAdd x))).toAdd
  left_inv x := by
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
  right_inv x := by
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]
  map_add' x y := by
    change (D.equiv T ((C.equiv T).symm
      (Multiplicative.ofAdd x * Multiplicative.ofAdd y))).toAdd = _
    rw [map_mul, map_mul, toAdd_mul]

lemma transition_point (T : Over S) (x : T ⟶ V.X) :
    C.transition D T (C.equiv T x).toAdd = (D.equiv T x).toAdd := by
  simp only [transition, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    ofAdd_toAdd, MulEquiv.symm_apply_apply]

lemma transition_reverse (T : Over S)
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    D.transition C T (C.transition D T x) = x := by
  simp only [transition, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    ofAdd_toAdd, MulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- The original point identity gives naturality of the additive section
transition for the canonical section pullbacks. -/
lemma transition_natural (T W : Over S) (b : W ⟶ T)
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    C.transition D W (sectionPullback M b x) =
      sectionPullback N b (C.transition D T x) := by
  let z := (C.equiv T).symm (Multiplicative.ofAdd x)
  have hz : C.equiv T z = Multiplicative.ofAdd x :=
    (C.equiv T).apply_symm_apply _
  have hs : C.equiv W (b ≫ z) = Multiplicative.ofAdd (sectionPullback M b x) := by
    apply Multiplicative.toAdd.injective
    rw [C.natural, hz]
    rfl
  change (D.equiv W ((C.equiv W).symm
    (Multiplicative.ofAdd (sectionPullback M b x)))).toAdd = _
  rw [← hs, MulEquiv.symm_apply_apply, D.natural]
  rfl

/-- Scalar preservation for the actual transition on every scheme test. -/
def IsLinear : Prop :=
  ∀ (T : Over S) (r : Γ(T.left, ⊤))
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)),
    C.transition D T (r • x) = r • C.transition D T x

lemma IsLinear.symm (h : C.IsLinear D) : D.IsLinear C := by
  intro T r x
  apply (C.transition D T).injective
  rw [transition_reverse, h, transition_reverse]

/-- Linear actual point transitions define natural linear section transformations. -/
def transformation (h : C.IsLinear D) : Transformation M N where
  app T := { (C.transition D T).toAddMonoidHom with map_smul' := h T }
  natural := C.transition_natural D

/-- The actual module isomorphism implementing the original point comparison. -/
def moduleIso (Q : DisjointFreePresentation M) (Q' : DisjointFreePresentation N)
    (h : C.IsLinear D) : M ≅ N :=
  Q.reconstructIso Q' (C.transformation D h) (D.transformation C (IsLinear.symm C D h))
    (C.transition_reverse D) (D.transition_reverse C)

/-- The actual reconstructed module isomorphism has the original point action
on every scheme test. -/
lemma moduleIso_point (Q : DisjointFreePresentation M) (Q' : DisjointFreePresentation N)
    (h : C.IsLinear D) (T : Over S) (x : T ⟶ V.X) :
    ((Scheme.Modules.pullback T.hom).map (C.moduleIso D Q Q' h).hom).app ⊤
        (C.equiv T x).toAdd = (D.equiv T x).toAdd := by
  change ((Scheme.Modules.pullback T.hom).map (Q.reconstruct (C.transformation D h))).app ⊤
    (C.equiv T x).toAdd = _
  rw [DisjointFreePresentation.reconstruct_apply]
  exact C.transition_point D T x

/-- Original point compatibility determines an actual module morphism uniquely. -/
lemma compatible_hom_ext (Q : DisjointFreePresentation M) (f g : M ⟶ N)
    (hf : ∀ (T : Over S) (x : T ⟶ V.X),
      ((Scheme.Modules.pullback T.hom).map f).app ⊤ (C.equiv T x).toAdd =
        (D.equiv T x).toAdd)
    (hg : ∀ (T : Over S) (x : T ⟶ V.X),
      ((Scheme.Modules.pullback T.hom).map g).app ⊤ (C.equiv T x).toAdd =
        (D.equiv T x).toAdd) : f = g := by
  apply Q.hom_ext
  intro T x
  let z := (C.equiv T).symm (Multiplicative.ofAdd x)
  have hz : (C.equiv T z).toAdd = x :=
    congrArg Multiplicative.toAdd ((C.equiv T).apply_symm_apply _)
  simpa only [hz] using (hf T z).trans (hg T z).symm

end ModulePointCharts
end Langlands.GroupScheme.RelativeUnipotent
