/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import all WeilConjectures.AlgebraicGeometry.PerfectInternalHomPullbackIsIso
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization

/-! # Perfect internal-Hom pullback with no module localization choice
Source: Stacks Project, cohomology.tex, Tags 08I3 and 0FPC.
(blueprint: lem-sc-mixed-perfect-internal-hom-pullback-isIso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private noncomputable def mixedTensorHomCore (S : Scheme.{u}) (K : schemeDerivedCategory S) :
    Adjunction.CoreHomEquiv (tensorRight K)
      ((Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S) S.sheaf)).obj (op K)) := by
  let e := schemeDerivedTensorHomEquiv S
  have he : IsCanonicalDerivedTensorHom S e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom S)
  exact
    { homEquiv := fun A L ↦ (e A K L).symm
      homEquiv_naturality_left_symm := by
        intro A' A L a h
        change e A' K L (a ≫ h) = (a ▷ K) ≫ e A K L h
        have hn := he.1 A A' K K L L a (𝟙 K) (𝟙 L) h
        erw [op_id, ← CategoryTheory.prod_id', CategoryTheory.Functor.map_id,
          Category.comp_id, tensorHom_id, Category.comp_id] at hn
        exact hn
      homEquiv_naturality_right := by
        intro A L L' h c
        apply (e A K L').injective
        change e A K L' ((e A K L').symm (h ≫ c)) =
          e A K L' ((e A K L).symm h ≫
            (derivedInternalHom (Opens.grothendieckTopology S)
              S.sheaf).map (𝟙 (op K), c))
        simpa only [op_id, id_tensorHom_id, Category.comp_id,
          Category.id_comp, Equiv.apply_symm_apply] using
          (he.1 A A K K L L' (𝟙 A) (𝟙 K) c ((e A K L).symm h)).symm }

/-- The evaluation-mate map on sheaf internal Hom is invertible for perfect M.
It uses no global sections or scalar extension and assumes no flatness or qcqs.
Source: Stacks Project, cohomology.tex, Remark 08I3 and Example 0FPC.
(blueprint: lem-sc-mixed-perfect-internal-hom-pullback-isIso).

Proof: locally resolve M by a bounded complex of finite projective modules. The
canonical tensor-Hom equivalence computes evaluation on this representative.
RHom(M,N) is N tensored with the finite-projective dual of M, even for unbounded
N. Termwise pullback preserves finite-projective duals and their evaluation.
The canonical tensor pullback comparison, normalized to the shared derived
counit, identifies pullback of this tensor with tensor of the pulled-back factors.
Consequently the displayed adjunct is the finite-projective tensor-Hom
isomorphism on every such neighbourhood. Compatibility with restriction and
cohomology shows it is globally invertible. Equivalently, transport the perfect
dual's exact evaluation/coevaluation pairing through strong monoidal pullback;
the triangle identities identify its adjunct with this map. Applying the
injective tensor-Hom equivalence checks the equality: both evaluations are
pullback of evaluation preceded by the inverse canonical tensor comparison.
For M=0 or an empty source the map is the unique isomorphism between zero objects. -/
theorem mixedPerfect_internalHom_pullback_isIso
    {T X : Scheme.{u}} (g : T ⟶ X)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M N : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M) :
    IsIso
      (((schemeDerivedTensorHomEquiv T)
        ((derivedPullback g).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N)))
        ((derivedPullback g).obj M) ((derivedPullback g).obj N)).symm
        ((mixedHomTensorPullbackIso g).inv.app
            ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N), M) ≫
          (derivedPullback g).map
            ((schemeDerivedTensorHomEquiv X)
              ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N))
              M N (𝟙 _)))) := by
  classical
  have hadj := (scheme_derivedInternalHom_adjunction X).choose_spec.choose_spec.choose_spec
  let P : schemeDerivedQCohCategory X :=
    ⟨M, schemeDerivedQCohProperty_of_isPerfect X M hM⟩
  have hdual := perfect_rhom_tensor_comparison X P P hM _ hadj.1 _ hadj.2.2.2
  let D := hdual.choose
  let p := hdual.choose_spec.choose_spec.choose_spec.2.2.choose_spec.2.2.2.choose_spec.2.2
    |>.choose_spec.2.2.1.choose
  let : ExactPairing M D.obj := p
  let t := mixedHomTensorPullbackIso g
  have ht : IsCanonicalPullbackTensorComparison g (fun A B ↦ t.hom.app (A, B)) :=
    Classical.choose_spec (exists_mixedHomTensorPullbackIso g)
  have hm' := canonicalPullbackTensor_monoidal_realization g _ ht
  let m := hm'.choose
  have hm := hm'.choose_spec
  let := m.toMonoidal
  have htensor (A B : schemeDerivedCategory X) :
      t.inv.app (A, B) = Functor.LaxMonoidal.μ (derivedPullback g) A B := by
    have he : (m.μIso A B).symm = t.app (A, B) := Iso.ext (hm A B)
    exact (congrArg Iso.inv he).symm
  let b := Adjunction.mkOfHomEquiv (mixedTensorHomCore X M)
  let c := Adjunction.mkOfHomEquiv (mixedTensorHomCore T ((derivedPullback g).obj M))
  have hb : b.counit.app N =
      schemeDerivedTensorHomEquiv X
        ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N))
        M N (𝟙 _) := by
    rw [← b.homEquiv_symm_id]
    simp only [b, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have h := monoidal_adjunct_isIso (derivedPullback g) M D.obj N _ _ b c
  simp only [c, Adjunction.mkOfHomEquiv_homEquiv] at h
  change IsIso ((schemeDerivedTensorHomEquiv T _ _ _).symm
    (Functor.LaxMonoidal.μ (derivedPullback g) _ _ ≫
      (derivedPullback g).map (b.counit.app N))) at h
  let H := (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op M, N)
  let ev := schemeDerivedTensorHomEquiv X H M N (𝟙 H)
  have heq : Functor.LaxMonoidal.μ (derivedPullback g) H M ≫
      (derivedPullback g).map (b.counit.app N) =
      t.inv.app (H, M) ≫ (derivedPullback g).map ev :=
    congrArg₂ (fun a q ↦ a ≫ q) (htensor H M).symm
      (congrArg (derivedPullback g).map hb)
  exact (congrArg (fun q ↦ IsIso
    ((schemeDerivedTensorHomEquiv T ((derivedPullback g).obj H)
      ((derivedPullback g).obj M) ((derivedPullback g).obj N)).symm q)) heq).mp h

end AlgebraicGeometry
