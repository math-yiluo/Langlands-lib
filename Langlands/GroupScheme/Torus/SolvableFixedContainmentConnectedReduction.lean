import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedStatement
import Langlands.GroupScheme.Rational.SemigroupBaseChange
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.BaseChangeReflection

/-! # Algebraic-closure reduction for connected invariant solvable subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

set_option backward.isDefEq.respectTransparency false in
/-- All-refinement fixed subgroup functors commute with arbitrary base change. -/
theorem fixedSubgroup_baseChange {B B' : Scheme.{u}} {S H : GroupScheme B}
    (c : AutomorphicAction S H) (b : B' ⟶ B) :
    (c.baseChange b).fixedSubgroup = c.fixedSubgroup.baseChange b := by
  ext T x
  rw [SubgroupFunctor.mem_baseChange, mem_fixedSubgroup_iff_universal,
    mem_fixedSubgroup_iff_universal]
  let e := Dynamic.mapTensorPullbackIso b T S.X
  have hfst : e.hom ≫ fst _ S.X ≫ baseChangePointsEquiv b H T x =
      baseChangePointsEquiv b H _ (fst T ((GroupScheme.baseChange b).obj S).X ≫ x) := by
    rw [baseChangePointsEquiv_naturality, Dynamic.mapTensorPullbackIso_hom_fst_assoc]
    rfl
  have hsnd : e.hom ≫ snd _ S.X = baseChangePointsEquiv b S _ (snd T _) := by
    apply Over.OverMorphism.ext
    rw [Dynamic.mapTensorPullbackIso_hom_snd_left, baseChangePointsEquiv_left]
    rfl
  constructor
  · intro hx
    apply (cancel_epi e.hom).mp
    rw [c.naturality, hsnd, hfst, ← baseChangePointsEquiv_act, hx]
  · intro hx
    apply (baseChangePointsEquiv b H _).injective
    rw [baseChangePointsEquiv_act, ← hsnd, ← hfst, ← c.naturality, hx]

end AutomorphicAction

namespace Torus

/-- The connected invariant-subgroup assertion restricted to algebraically closed fields. -/
def SolvableFixedContainmentConnectedAlgClosedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))),
    Smooth H.X.hom → IsAffineHom H.X.hom → ConnectedSpace H.X.left →
    RelativeRoot.IsSolvableScheme H →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus S.toGrp →
      ∀ (c : AutomorphicAction S.toGrp H) (F : SubgroupFunctor H),
        c.IsStable F → c.fixedSubgroup ≤ F →
        ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (q : C ⟶ H),
          F.IsRepresentedBy q → IsClosedSubgroup q → Smooth C.X.hom →
          ConnectedSpace C.X.left

/-- It suffices to prove the connected invariant-subgroup assertion over algebraically
closed fields of the same universe. -/
theorem solvableFixedContainmentConnected_of_algClosed :
    SolvableFixedContainmentConnectedAlgClosedStatement.{u} →
      SolvableFixedContainmentConnectedStatement.{u} := by
  intro h k _ H hHs hHa hHc hHsol S hS c F hF hfixed C q hq hqc hCs
  let b := toAlgebraicClosure k
  let Hbar := (GroupScheme.baseChange b).obj H
  let Sbar := (CommGroupScheme.baseChange b).obj S
  let Cbar := (GroupScheme.baseChange b).obj C
  let : Smooth H.X.hom := hHs
  let : IsAffineHom H.X.hom := hHa
  let : ConnectedSpace H.X.left := hHc
  let : Smooth C.X.hom := hCs
  have hHbars : Smooth Hbar.X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  have hHbara : IsAffineHom Hbar.X.hom := by
    change IsAffineHom (pullback.snd H.X.hom b)
    infer_instance
  have hHbarc : ConnectedSpace Hbar.X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have hCbars : Smooth Cbar.X.hom := by
    change Smooth (pullback.snd C.X.hom b)
    infer_instance
  have hfixedbar : (c.baseChange b).fixedSubgroup ≤ F.baseChange b := by
    rw [AutomorphicAction.fixedSubgroup_baseChange]
    intro T x hx
    exact hfixed _ hx
  have hCbarc : ConnectedSpace Cbar.X.left :=
    h (AlgebraicClosure k) Hbar hHbars hHbara hHbarc (hHsol.baseChange b)
      Sbar (hS.baseChange b) (c.baseChange b) (F.baseChange b)
      (hF.baseChange b) hfixedbar Cbar ((GroupScheme.baseChange b).map q)
      (hq.baseChange b) (hqc.baseChange b) hCbars
  let : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  let : ConnectedSpace (pullback C.X.hom b : Scheme.{u}) := hCbarc
  exact (inferInstance : Surjective (pullback.fst C.X.hom b)).surj.connectedSpace
    (pullback.fst C.X.hom b).continuous

end Torus
end Langlands.GroupScheme
