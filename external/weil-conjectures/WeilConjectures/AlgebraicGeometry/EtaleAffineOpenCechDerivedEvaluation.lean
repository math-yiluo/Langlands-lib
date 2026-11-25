/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluationSucc
import WeilConjectures.Topology.OpenCechZerothHomology

/-! # The affine-open Čech edge comparison for étale sheaves

Source: Stacks Project, Tag 03AZ, specialized to an acyclic affine-open covering,
and Tag 03P2, separated-case proof.
(blueprint: lem-sc-etale-affine-open-cech-derived-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An étale sheaf acyclic on affine objects is computed on a separated scheme by
its sections on a finite affine open covering.
Source: Stacks Project, Tag 03AZ (the Čech-to-cohomology spectral sequence), and
Tag 03P2, separated-case proof.
(blueprint: lem-sc-etale-affine-open-cech-derived-evaluation).

Proof: The functor i sends each open to its open subscheme over X, by hi. Cover
preservation sends the open cover U to an étale cover of i(top). Finite-limit
preservation identifies each nonempty product of the i(U_j), over this terminal
object, with i of the corresponding intersection. Separatedness makes each such
finite intersection affine. The hypothesis hvan therefore kills every positive
cohomology group on these products. Apply the Čech-to-derived spectral sequence
03AZ. Its positive rows are zero, while its zero row is the sections complex:
right-derived evaluation in degree zero agrees naturally with evaluation since
evaluation is left exact. From page E2 onward every differential entering or
leaving the zero row is zero. The finite abutment filtration in degree q has just
one possibly nonzero successive quotient, at (q,0), giving an isomorphism from derived evaluation at
i(top) to degree-q homology of that row. The product comparisons commute with
projections and hence with all face maps, so the row identifies with the Čech
complex on opens of i.op followed by G.obj. This proves the displayed isomorphism.
For q=0 this is ordinary sheaf gluing. The empty cover of an empty scheme gives
zero on both sides and is included in the same argument. -/
theorem nonempty_rightDerived_etale_affineOpenCech
    (X : Scheme.{u}) [X.IsSeparated]
    (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hvan : ∀ (W : X.Etale), IsAffine W.left → ∀ (q : ℕ), 0 < q →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op W)).rightDerived q).obj G))
    (q : ℕ) :
    Nonempty ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op (i.obj ⊤))).rightDerived q).obj G)
        ≅ ((cechComplexFunctor U).obj (i.op ⋙ G.obj)).homology q) := by
  cases q with
  | zero =>
    let : RepresentablyFlat i := flat_of_preservesFiniteLimits i
    let : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
      (i.isContinuous_iff_coverPreserving).2 hc
    let F : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} :=
      ⟨i.op ⋙ G.obj, i.op_comp_isSheaf_of_isSheaf _ _ _ G.property⟩
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (i.obj ⊤))
    obtain ⟨e⟩ := TopCat.Sheaf.nonempty_openCech_zerothHomology U hcover F
    exact ⟨E.rightDerivedZeroIsoSelf.app G ≪≫ e⟩
  | succ n =>
    exact nonempty_rightDerived_etale_affineOpenCech_succ X i hi hc ht U hU hcover G hvan n

end AlgebraicGeometry.Scheme
