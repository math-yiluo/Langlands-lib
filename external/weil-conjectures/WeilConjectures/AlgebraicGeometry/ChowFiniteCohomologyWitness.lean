/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmple
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.ChowTwistFiniteCohomology
import WeilConjectures.AlgebraicGeometry.BirationalLinePushforwardGenericStalk
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.Algebra.Module.TransferInstance

/-! # A Chow module with finite cohomology and generic rank one

Source: Stacks Project, Proposition 30.19.1, Tag 02O5, Chow construction.
(blueprint: lem-pc-v3-chow-finite-cohomology-witness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- The Chow construction supplies one coherent module with finite cohomology on each
integral closed support, with its generic stalk the one-dimensional residue-field module.

Source: Stacks Project, Proposition 30.19.1, Tag 02O5, the construction following the
short exact sequence argument, label `proposition-proper-pushforward-coherent`.
(blueprint: lem-pc-v3-chow-finite-cohomology-witness)

Proof: The proper source and its closed subscheme W are Noetherian. Apply Chow's lemma
 to W over T, obtaining a projective modification π : W' → W that is an isomorphism over
 a dense open. The projective embedding gives an invertible module L relatively ample
 for both π and W' → T. Choose a common power killing both positive higher direct images,
 and put G = i_* π_* L^n. Projective-space cohomology finiteness on affine opens of W
 proves coherence of π_* L^n; use this independent projective argument, not the general
 proper coherence theorem. Closed pushforward preserves coherence. The Leray comparison
 and affine-base cohomology identify H^q(G) with H^q(W', L^n), which is finite by the
 projective-space theorem, with scalars induced by f.appTop. On the dense open π is an
 isomorphism, so the generic stalk is a line over the function field of W. Closed
 immersion identifies this field with the residue field at i(η); the scalar action is
 the quotient action and the maximal ideal annihilates it. The support is contained
 in i(W) by closed pushforward and contains its generic point. Coherence makes it closed,
 so it equals i(W). No ideal on W or induction hypothesis is needed for this module. -/
theorem exists_chow_finite_cohomology_witness {X T : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W] :
    ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
        ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G, a • v = 0) ∧
      (∃ inst : Module (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
        (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
          (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
            (i.base (genericPoint W))).obj G),
          a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
        Module.finrank (X.residueField (i.base (genericPoint W)))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
          = 1) ∧
      (∀ q : ℕ,
        letI : Module Γ(T, ⊤) (G.H q) := Module.compHom _ f.appTop.hom
        Module.Finite Γ(T, ⊤) (G.H q)) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsNoetherian T := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let g := i ≫ f
  let Y := ChowModification g
  let π : Y ⟶ W := ChowModification.modificationMap g
  let N := ChowModification.index g
  let j : Y ⟶ ProjectiveSpace N T := ChowModification.toProjectiveSpace g
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let L := (pullback j).obj
    ((pullback (ProjectiveSpace.toProjInt N T)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
  obtain ⟨n, hcoh, hfinite⟩ := exists_chow_twist_finite_cohomology f i π N j
    (ChowModification.toProjectiveSpace_over g)
  let F := (pushforward π).obj (L.tensorPow n)
  let G := (pushforward i).obj F
  obtain ⟨U, hU, hπ⟩ := ChowModification.exists_dense_isIso_restrict g
  have : IsIso (π ∣_ U) := hπ
  have : L.IsInvertible := by
    dsimp only [L]
    infer_instance
  have : (L.tensorPow n).IsInvertible := IsInvertible.tensorPow L n
  obtain ⟨e, he⟩ := birational_line_pushforward_generic_stalk i π U hU (L.tensorPow n)
  have hgen : ¬ Subsingleton (G.presheaf.stalk (i.base (genericPoint W))) := by
    intro hz
    have : Subsingleton (X.residueField (i.base (genericPoint W))) :=
      e.toEquiv.subsingleton_congr.mp hz
    exact (zero_ne_one : (0 : X.residueField (i.base (genericPoint W))) ≠ 1)
      (Subsingleton.elim _ _)
  have htypes := (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hcoh
  have : G.IsQuasicoherent := htypes.1
  have : G.IsFiniteType := htypes.2
  have hclosed := (finite_type_module_support_closed X G).2.2.2
  have hstalk := closedImmersion_pushforward_stalks i i.isClosedEmbedding F
  have hsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base := by
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hn
      exact hx (hstalk.1 x hn)
    · rintro x ⟨w, rfl⟩
      exact ((genericPoint_specializes w).map i.continuous).mem_closed hclosed hgen
  have hann : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0 := by
    intro a ha v
    apply e.injective
    rw [he, e.map_zero]
    have hz : (X.residue (i.base (genericPoint W))) a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    rw [hz, zero_mul]
  let inst := e.module (X.residueField (i.base (genericPoint W)))
  have hcompat : ∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
      (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G),
      a • v = (X.residue (i.base (genericPoint W))) a • v := by
    intro a v
    apply e.injective
    rw [he]
    exact (e.linearEquiv (X.residueField (i.base (genericPoint W)))).map_smul _ v |>.symm
  have hrank : Module.finrank (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G) = 1 := by
    exact (e.linearEquiv (X.residueField (i.base (genericPoint W)))).finrank_eq.trans
      (Module.finrank_self _)
  exact ⟨G, hcoh, hsupp, hann, ⟨inst, hcompat, hrank⟩, hfinite⟩

end AlgebraicGeometry.Scheme.Modules
