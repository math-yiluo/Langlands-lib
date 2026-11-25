/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedBar.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedScalarAction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PullbackComparisonOfAcyclic
public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionScalarAcyclic
public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionAbelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZeroUnit
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedScalarInvariants
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionInvariants
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

/-! # Derived restriction calculus for internal condensed actions

Source: main-20261015 direct-images proof, paragraph (3), formal derived-restriction
infrastructure (blueprint: def-sfb-condensed-derived-invariants).
The source records this auxiliary infrastructure as agent-formulated, with a reference wanted.
No assertion that underived continuous cochains compute derived invariants is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The given additive category of internal actions is abelian, for arbitrary topological G.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: use the action-site presentation and the internal/sectionwise module equivalence.
Kernels and sheafified cokernels carry the induced action; normality and finite products
are computed on underlying internal modules. -/
theorem actionAbelianData : Nonempty (ActionAbelian A G) := by
  exact ActionSite.actionAbelian_nonempty A G

/-- Abelian-category structure on the existing action category; its data fields are
propositions, so this selects no unspecified mathematical object.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance actionAbelian : ActionAbelian A G := Classical.choice (actionAbelianData A G)

/-- The action-site presentation transports the generator, colimits and AB5.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the action-site module equivalence preserves all limits and colimits; apply the
Grothendieck abelian theorem for modules on a small ringed site. -/
@[instance] theorem actionGrothendieck : IsGrothendieckAbelian.{u + 1} (Equivariant A G) := by
  exact ActionSite.isGrothendieckAbelian A G

/-- Forgetting the action creates kernels and cokernels and detects exactness.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the equivariance equation restricts to kernels and descends to sheafified cokernels.
The forgetful functor is faithful and detects zero; exactness is therefore detected. -/
theorem forgetExact :
    PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) ∧
    PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) ∧
    (∀ S : ShortComplex (Equivariant A G),
      S.Exact ↔ (S.map (CondensedBar.forgetAction (A := A) (G := G))).Exact) := by
  exact ActionSite.forgetAction_exact A G

private theorem forgetReflects (A : CondensedBar.Ring.{u}) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (CondensedBar.forgetAction (A := A) (G := G)).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso f.val := hf
    let i := inv f.val
    have hi : Profinite.CondensedAction.Equivariant N M i := by
      intro S g x
      have hf (y : Profinite.CondensedAction.sectionModule A.toMon N.module S) :
          (f.val.hom.hom.app (op S)).hom ((i.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.inv_hom_id f.val)) (op S)) y
      have hg (y : Profinite.CondensedAction.sectionModule A.toMon M.module S) :
          (i.hom.hom.app (op S)).hom ((f.val.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.hom_inv_id f.val)) (op S)) y
      have h := congrArg (fun y ↦ (i.hom.hom.app (op S)).hom y)
        (f.property S g ((i.hom.hom.app (op S)).hom x))
      rw [hg, hf] at h
      exact h.symm
    exact ⟨⟨⟨i, hi⟩, Subtype.ext (IsIso.hom_inv_id f.val),
      Subtype.ext (IsIso.inv_hom_id f.val)⟩⟩

/-- Existence of the normalized invariant-submodule adjunction already specified by the
recorded action-module definition. Its universal property determines it up to the unique
isomorphism commuting with its inclusion.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: fully fixed sections form submodules stable under restriction and gluing. Restrict
codomains of maps from trivial actions; composition with the inclusion is the inverse. -/
theorem invariantsExist : Nonempty (Invariants A G) :=
  Profinite.CondensedAction.nonempty_invariants

/-- Trivial action is additive and exact on the underlying modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: it leaves objects and maps unchanged and preserves the induced kernels and cokernels. -/
@[instance] theorem trivialAdditive : (trivial (R := A.toMon) (P := G)).Additive := by
  exact ⟨by intros; rfl⟩

/-- Exactness of trivial action, on kernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying kernel with trivial action is the equivariant kernel. -/
@[instance] theorem trivialLimits :
    PreservesFiniteLimits (trivial (R := A.toMon) (P := G)) := by
  let U := CondensedBar.forgetAction (A := A) (G := G)
  have : U.ReflectsIsomorphisms := forgetReflects A G
  have : PreservesFiniteLimits U := (forgetExact A G).1
  have : PreservesFiniteLimits (trivial (R := A.toMon) (P := G) ⋙ U) :=
    show PreservesFiniteLimits (𝟭 (Modules A)) from inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

/-- Exactness of trivial action, on cokernels.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: the underlying sheafified cokernel retains trivial action. -/
@[instance] theorem trivialColimits :
    PreservesFiniteColimits (trivial (R := A.toMon) (P := G)) := by
  let U := CondensedBar.forgetAction (A := A) (G := G)
  have : U.ReflectsIsomorphisms := forgetReflects A G
  have : PreservesFiniteColimits U := (forgetExact A G).2.1
  have : PreservesFiniteColimits (trivial (R := A.toMon) (P := G) ⋙ U) :=
    show PreservesFiniteColimits (𝟭 (Modules A)) from inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

variable {A G} {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of actions along a continuous group map is additive.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition changes no underlying map, hence preserves sums. -/
@[instance] theorem restrictionAdditive (v : H →ₜ* G) :
    (inflate (R := A.toMon) v).Additive := by
  exact ⟨by intros; rfl⟩

/-- Restriction is left exact, with the induced action on the same kernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with the kernel construction. -/
@[instance] theorem restrictionLimits (v : H →ₜ* G) :
    PreservesFiniteLimits (inflate (R := A.toMon) v) := by
  let U := CondensedBar.forgetAction (A := A) (G := H)
  have : U.ReflectsIsomorphisms := forgetReflects A H
  have : PreservesFiniteLimits U := (forgetExact A H).1
  have : PreservesFiniteLimits (inflate (R := A.toMon) v ⋙ U) :=
    show PreservesFiniteLimits (CondensedBar.forgetAction (A := A) (G := G)) from
      (forgetExact A G).1
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

/-- Restriction is right exact, with the induced action on the same cokernel.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: precomposition of the action commutes with sheafified cokernels. -/
@[instance] theorem restrictionColimits (v : H →ₜ* G) :
    PreservesFiniteColimits (inflate (R := A.toMon) v) := by
  let U := CondensedBar.forgetAction (A := A) (G := H)
  have : U.ReflectsIsomorphisms := forgetReflects A H
  have : PreservesFiniteColimits U := (forgetExact A H).2.1
  have : PreservesFiniteColimits (inflate (R := A.toMon) v ⋙ U) :=
    show PreservesFiniteColimits (CondensedBar.forgetAction (A := A) (G := G)) from
      (forgetExact A G).2.1
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

section Derived
variable [HasDerivedCategory.{u + 1} (Modules A)]
  [HasDerivedCategory.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 1} (Equivariant A H)]

set_option linter.unusedSectionVars false in
/-- The invariant inclusion uniquely determines the underived restriction map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: a fully G-fixed section is H-fixed after precomposition. Restrict the codomain
using the normalized invariant inclusion, which is a monomorphism on every section. -/
theorem invariantRestrictionExist (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    ∃! b : V.functor ⟶ inflate (R := A.toMon) v ⋙ W.functor,
      ∀ N, b.app N ≫ W.inclusion.app ((inflate v).obj N) = V.inclusion.app N := by
  have hc (N : Equivariant A G) :
      (V.adjunction.counit.app N).val = V.inclusion.app N := by
    simpa only [Adjunction.homEquiv_symm_id, Category.id_comp] using
      V.untranspose (V.functor.obj N) N (𝟙 _)
  let b : V.functor ⟶ inflate (R := A.toMon) v ⋙ W.functor :=
    { app := fun N ↦ W.adjunction.homEquiv _ _
        ((inflate v).map (V.adjunction.counit.app N))
      naturality := fun {N N'} f ↦ by
        dsimp only [Functor.comp_map]
        rw [← W.adjunction.homEquiv_naturality_left]
        erw [← W.adjunction.homEquiv_naturality_right]
        apply congrArg (W.adjunction.homEquiv _ _)
        apply Subtype.ext
        exact congrArg (fun h ↦ h.val) (V.adjunction.counit.naturality f) }
  refine ⟨b, ?_, ?_⟩
  · intro N
    exact (W.transpose _ _ _).trans (hc N)
  · intro b' hb'
    apply NatTrans.ext
    funext N
    dsimp only [b]
    apply (W.adjunction.homEquiv _ _).symm.injective
    apply Subtype.ext
    rw [W.untranspose]
    erw [Equiv.symm_apply_apply]
    exact (hb' N).trans (hc N).symm

/-- The unique map into the invariant subsheaf; uniqueness fixes the actual arrow.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def invariantRestriction (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    V.functor ⟶ inflate (R := A.toMon) v ⋙ W.functor :=
  Classical.choose (invariantRestrictionExist V W v)

/-- Canonical total derived restriction, obtained by right deriving the fixed-section
inclusion along the exact restriction functor, not by assuming it preserves injectives.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def restriction (V : Invariants A G) (W : Invariants A H) (v : H →ₜ* G) :
    V.functor.rightDerivedFunctor ⟶
      (inflate (R := A.toMon) v).mapDerivedCategory ⋙ W.functor.rightDerivedFunctor :=
  Functor.rightDerivedPullback (inflate v) (invariantRestriction V W v)

end Derived

/-- Canonical invariants, selected by their fixed-section inclusion universal property.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def invariants (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Invariants A G := Classical.choice (invariantsExist A G)

/-- Ordinary unbounded right derived invariants, in the existing small-Hom localization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def derived (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Equivariant A G) ⥤
      DerivedCategory.{u + 1} (Modules A) := (invariants A G).functor.rightDerivedFunctor

/-- The exact trivial-action functor on ordinary derived categories.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def trivialDerived (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Modules A) ⥤
      DerivedCategory.{u + 1} (Equivariant A G) :=
  (trivial (R := A.toMon) (P := G)).mapDerivedCategory

/-- The canonical derived adjunction, with its actual resolution-normalized unit and counit.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def adjunction (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : trivialDerived A G ⊣ derived A G :=
  (invariants A G).adjunction.mapDerivedCategoryRightDerivedAdjunction

/-- The derived invariant functor has its canonical integer-shift structure.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance derivedShift : (derived A G).CommShift ℤ :=
  inferInstanceAs ((invariants A G).functor.rightDerivedFunctor.CommShift ℤ)

/-- Degree zero is the actual invariant functor, with the comparison induced by the
right-derived unit, not an arbitrarily chosen cohomology isomorphism.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: in an injective resolution, H⁰ of invariants is the kernel of the first invariant
differential, which is invariants of the original module by left exactness. -/
theorem degreeZero : ∃ e :
    (DerivedCategory.singleFunctor (Equivariant A G) 0 ⋙ derived A G) ⋙
      DerivedCategory.homologyFunctor (Modules A) 0 ≅ (invariants A G).functor,
    ∀ N, (DerivedCategory.homologyFunctor (Modules A) 0).map
      ((invariants A G).functor.rightDerivedFunctorUnitQ
        ((HomologicalComplex.single _ (.up ℤ) 0).obj N)) ≫ e.hom.app N =
      (DerivedCategory.homologyFunctor (Modules A) 0).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (invariants A G).functor
            (.up ℤ) 0).hom.app N)) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules A) 0).hom.app
          ((invariants A G).functor.obj N) := by
  have := (invariants A G).adjunction.isRightAdjoint
  exact Functor.exists_homologyZero_iso_rightDerivedFunctorUnitQ _

/-- The degree-zero identification fixed by the computation unit. That equation
uniquely determines this isomorphism, since the two comparison maps in degree zero
are invertible by left exactness.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def degreeZeroIso :
    (DerivedCategory.singleFunctor (Equivariant A G) 0 ⋙ derived A G) ⋙
      DerivedCategory.homologyFunctor (Modules A) 0 ≅ (invariants A G).functor :=
  Classical.choose (degreeZero (A := A) (G := G))

variable {A' : CondensedBar.Ring.{u}}

/-- The existing normalized scalar-action specification has a canonical realization.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: use the same underlying abelian sheaf and action, and restrict its scalar action
along the given ring map. The displayed underlying comparison is identity on sections. -/
theorem scalarActionExist (a : A ⟶ A') : Nonempty (ScalarAction a G) :=
  nonempty_scalarAction a G

/-- Scalar restriction on actions, fixed by its underlying module and section action.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarAction (a : A ⟶ A') : ScalarAction a G := Classical.choice (scalarActionExist a)

/-- Scalar restriction of actions is exact, without flatness of the ring map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: kernels and sheafified cokernels have the same underlying abelian sheaves before
and after restricting scalars; their induced group actions are unchanged. -/
theorem scalarExact (a : A ⟶ A') :
    PreservesFiniteLimits (scalarAction (G := G) a).functor ∧
    PreservesFiniteColimits (scalarAction (G := G) a).functor := by
  let U := CondensedBar.forgetAction (A := A) (G := G)
  have : U.ReflectsIsomorphisms := forgetReflects A G
  have : PreservesFiniteLimits U := (forgetExact A G).1
  have : PreservesFiniteColimits U := (forgetExact A G).2.1
  have : PreservesFiniteLimits (CondensedBar.forgetAction (A := A') (G := G)) :=
    (forgetExact A' G).1
  have : PreservesFiniteColimits (CondensedBar.forgetAction (A := A') (G := G)) :=
    (forgetExact A' G).2.1
  have : PreservesFiniteLimits ((scalarAction (G := G) a).functor ⋙ U) :=
    preservesFiniteLimits_of_natIso (scalarAction a).underlying.symm
  have : PreservesFiniteColimits ((scalarAction (G := G) a).functor ⋙ U) :=
    preservesFiniteColimits_of_natIso (scalarAction a).underlying.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- Exactness on kernels, from the preceding statement.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance scalarLimits (a : A ⟶ A') :
    PreservesFiniteLimits (scalarAction (G := G) a).functor := (scalarExact a).1

/-- Exactness on cokernels, from the preceding statement.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
instance scalarColimits (a : A ⟶ A') :
    PreservesFiniteColimits (scalarAction (G := G) a).functor := (scalarExact a).2

/-- Termwise scalar restriction on derived action modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarDerived (a : A ⟶ A') (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : DerivedCategory.{u + 1} (Equivariant A' G) ⥤
      DerivedCategory.{u + 1} (Equivariant A G) :=
  (scalarAction (G := G) a).functor.mapDerivedCategory

/-- Termwise scalar restriction on derived internal modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarBase (a : A ⟶ A') : DerivedCategory.{u + 1} (Modules A') ⥤
    DerivedCategory.{u + 1} (Modules A) := (Mod.comap a.hom.hom).mapDerivedCategory

/-- Scalar restriction and taking the fully fixed subsheaf commute canonically. The
normalization fixes this isomorphism on the actual invariant inclusions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: both sides consist of the same sections fixed after every profinite base change;
their inclusions identify the same submodule of the restricted underlying sheaf. -/
theorem scalarInvariantsExist (a : A ⟶ A') :
    ∃! e : (scalarAction (G := G) a).functor ⋙ (invariants A G).functor ≅
        (invariants A' G).functor ⋙ Mod.comap a.hom.hom,
      ∀ N, (invariants A G).inclusion.app ((scalarAction a).functor.obj N) ≫
          (scalarAction a).underlying.hom.app N =
        e.hom.app N ≫ (Mod.comap a.hom.hom).map ((invariants A' G).inclusion.app N) := by
  exact existsUnique_scalarInvariantsIso _ _ _

/-- The unique scalar/invariants comparison fixed by the invariant inclusions.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarInvariants (a : A ⟶ A') :
    (scalarAction (G := G) a).functor ⋙ (invariants A G).functor ≅
      (invariants A' G).functor ⋙ Mod.comap a.hom.hom :=
  Classical.choose (scalarInvariantsExist a)

/-- The scalar comparison is the unique derived transformation whose computation units
are the underived fixed-section identification, and is invertible for any ring map.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants).
Proof: view scalar restriction and invariants as direct images of the identity ringed
topos and the action projection. Their two composites are the same ringed direct image.
The canonical derived-composition comparisons give this isomorphism, compatibly with
computation units; uniqueness follows from the right-derived universal property. No
preservation of injectives by scalar restriction and no flatness is used. -/
theorem scalarComparisonExist (a : A ⟶ A') :
    ∃! d : scalarDerived a G ⋙ derived A G ≅ derived A' G ⋙ scalarBase a,
      ∀ K : CochainComplex (Equivariant A' G) ℤ,
        (invariants A G).functor.rightDerivedFunctorUnitQ
            (((scalarAction a).functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (derived A G).map ((scalarAction a).functor.mapDerivedCategoryFactors.inv.app K) ≫
          d.hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (scalarInvariants a) (.up ℤ)).hom.app K) ≫
          (Mod.comap a.hom.hom).mapDerivedCategoryFactors.inv.app
            (((invariants A' G).functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (scalarBase a).map ((invariants A' G).functor.rightDerivedFunctorUnitQ K) := by
  exact Functor.existsUnique_rightDerivedFunctor_comparison_of_acyclic _ _ _ _ _
    fun I _ J _ j _ ↦ scalarAction_quasiIso_invariants_map (scalarAction a) (invariants A G) I J j

/-- The unique derived coefficient isomorphism normalized by the computation units.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def scalarComparison (a : A ⟶ A') :
    scalarDerived a G ⋙ derived A G ≅ derived A' G ⋙ scalarBase a :=
  Classical.choose (scalarComparisonExist a)

/-- Coefficient map for any derived equivariant morphism. Modules enter via the ordinary
single-degree embedding; this formula also applies to every complex.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def coefficientMap (a : A ⟶ A') {N : DerivedCategory.{u + 1} (Equivariant A G)}
    {N' : DerivedCategory.{u + 1} (Equivariant A' G)}
    (f : N ⟶ (scalarDerived a G).obj N') :
    (derived A G).obj N ⟶ (scalarBase a).obj ((derived A' G).obj N') :=
  (derived A G).map f ≫ (scalarComparison a).hom.app N'

/-- The canonical coefficient restriction to a subgroup, with degree-zero trivial
coefficients retained as the original regular module.
Source: paragraph (3) (blueprint: def-sfb-condensed-derived-invariants). -/
def regularTrivial (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  (trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)

end CategoryTheory.CondensedDerivedRestriction
