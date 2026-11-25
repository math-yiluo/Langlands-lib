/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Perfect complexes are pseudo-coherent and locally of finite Tor dimension
Source: literature/stacks-project/cohomology.tex, Lemma 08CQ, implication (1) => (2)
(blueprint: lem-pc-perfect-pseudo-coherent-locally-finite-tor).
-/

@[expose] public section

universe uP wP
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits MonoidalCategory in
/-- Exact open restriction, transported from the localized site, computes open pullback. -/
private theorem open_model_iso (X : Scheme.{uP}) (U : X.Opens)
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex
      (SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor.{uP}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((derivedPullback U.ι).obj E ≅ DerivedCategory.Q.obj
      ((((Modules.overEquiv U).functor).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let A : SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace) :=
    (Modules.overEquiv U).functor
  let R := SheafOfModules.overFunctor.{uP} (moduleRings X.toRingedSpace) U
  have : A.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (R ⋙ A) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ A) := comp_preservesFiniteColimits _ _
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    (derivedPullback_spec U.ι)
  have h : F = Modules.tensorPullback U.ι :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let T : SheafOfModules.{uP} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace) :=
    Modules.tensorPullback U.ι
  let η : T ≅ Modules.restrictFunctor U.ι :=
    (Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : R ⋙ A ≅ T := Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uP} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback U.ι ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι) ε
      T.mapDerivedCategoryFactorsh.hom W
  exact ⟨i.app E ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm.app E ≪≫
    (Functor.mapDerivedCategoryCompIso R A).symm.app E ≪≫ A.mapDerivedCategory.mapIso e ≪≫
      A.mapDerivedCategoryFactors.app K⟩

open CategoryTheory.Limits MonoidalCategory in
/-- Finite free module sheaves are flat. -/
private theorem flat_of_finiteFree (Y : Scheme.{uP})
    (M : SheafOfModules.{uP} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (e : M ≅ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{uP} (Fin m))) :
    SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{uP} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hf).2

open CategoryTheory.Limits MonoidalCategory in
/-- Tensor with a module in degree zero preserves the termwise vanishing interval. -/
private theorem tensor_homology_isZero_of_term_isZero (Y : Scheme.{uP})
    (P : CochainComplex (SheafOfModules.{uP} (moduleRings Y.toRingedSpace)) ℤ)
    (G : SheafOfModules.{uP} (moduleRings Y.toRingedSpace)) (n : ℤ)
    (hn : IsZero (P.X n)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    IsZero ((CochainComplex.mapBifunctor P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj G) (curriedTensor _)).homology n) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let T := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single _ (.up ℤ) 0).obj G) (curriedTensor _)
  let e := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) G P
  have hz : IsZero (T.X n) :=
    IsZero.of_iso ((tensorRight G).map_isZero hn)
      ((HomologicalComplex.eval _ (.up ℤ) n).mapIso e)
  exact (T.sc n).isZero_homology_of_isZero_X₂ hz

/-- A perfect complex is pseudo-coherent and locally has finite Tor dimension.
Source: literature/stacks-project/cohomology.tex, Lemma 08CQ, implication (1) => (2)
(blueprint: lem-pc-perfect-pseudo-coherent-locally-finite-tor).

Proof: refine a strictly perfect local model by affine opens and finite-free principal
opens (`lem-weil-pbc-finite-projective-standard-free-cover`); this gives the
bounded-above finite-free models required for pseudo-coherence.
This uses `lemma-coherent-base-change-invertible-sheaves--1` and `def-pur-pseudo-coherent-complex`.
The same bounded model is termwise flat and K-flat by the bounded-above-flat K-flat
lemma (`lem-pc-bounded-above-flat-kflat`), and its tensor with any module is bounded
in one common finite interval.
-/
theorem perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension (X : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    IsPseudoCoherent X E ∧ HasLocallyFiniteTorDimension X E := by
  constructor
  · intro x
    obtain ⟨V, hxV, K, hK, hEK⟩ := hE x
    obtain ⟨U, hxU, _, _, P, ⟨a, b, hb⟩, hf, e⟩ :=
      exists_finiteFree_refinement_of_isStrictlyPerfect X E V K hK hEK x hxV
    exact ⟨U, hxU, P, ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩, hf, e⟩
  · intro x
    obtain ⟨V, hxV, L, hL, hEL⟩ := hE x
    obtain ⟨U, hxU, _, _, K, ⟨a, b, hb⟩, hf, ⟨e⟩⟩ :=
      exists_finiteFree_refinement_of_isStrictlyPerfect X E V L hL hEL x hxV
    let A : SheafOfModules.{uP} ((moduleRings X.toRingedSpace).over U) ⥤
        SheafOfModules.{uP} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
    have : A.Additive := Functor.additive_of_preserves_binary_products _
    let P := (A.mapHomologicalComplex (.up ℤ)).obj K
    have hbounded : ∀ n : ℤ, n < a ∨ b < n → CategoryTheory.Limits.IsZero (P.X n) :=
      fun n hn ↦ A.map_isZero (hb n hn)
    have hflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
      intro n
      obtain ⟨r, ⟨er⟩⟩ := hf n
      let ef : A.obj (SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{uP} (Fin r))) ≅
          SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
            (ULift.{uP} (Fin r)) :=
        (asIso (CategoryTheory.Limits.sigmaComparison A (fun _ : ULift.{uP} (Fin r) ↦
          SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
        CategoryTheory.Limits.Sigma.mapIso
          (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
      exact flat_of_finiteFree U.toScheme (P.X n) r (A.mapIso er ≪≫ ef)
    have hP := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      U.toScheme.toRingedSpace P ⟨b, fun n hn ↦ hbounded n (Or.inr hn)⟩ hflat
    obtain ⟨eP⟩ := open_model_iso X U E K e
    refine ⟨U, hxU, min a b, b, min_le_right _ _, ?_⟩
    intro G n hn
    have hn' : n < a ∨ b < n := hn.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id
    exact ⟨P, hP, ⟨eP.symm⟩,
      tensor_homology_isZero_of_term_isZero U.toScheme P G n (hbounded n hn')⟩

end AlgebraicGeometry.Scheme
