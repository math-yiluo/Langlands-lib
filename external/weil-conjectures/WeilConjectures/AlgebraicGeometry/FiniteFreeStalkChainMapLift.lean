/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapLiftLocal
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapLiftRestrict

/-! # Local extension of one map between bounded finite free complexes

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix extension argument, expanded
in lem-pc-finite-free-stalk-chain-map-pair-lift, proof steps 1--3.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- One prescribed stalk chain map extends, using the canonical comparison, to every
sufficiently small neighbourhood.

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix extension argument, as
expanded in lem-pc-finite-free-stalk-chain-map-pair-lift, proof steps 1--3.
(blueprint: lem-pc-finite-free-stalk-chain-map-lift)

Proof: Choose finite bases of the nonzero terms of P and Q. Their bounded supports
leave finitely many possibly nonzero components of f. Under pullback of a finite
free module, each component is a matrix over the local ring. Represent its entries
by sections near y and intersect the finitely many neighbourhoods. The differences
of the two sides of every chain equation are finite matrices with zero germs.
Shrink again by the germ equality criterion to make all these entries zero.
The resulting matrices, together with the unique maps involving zero terms, define
one chain map on an open U containing y. Its stalk image is the conjugate of f
by the canonical comparison `stalkRestrictionComplexIso` on P and Q.
For each V contained in U restrict this chain map along the inclusion V -> U.
Conjugate by the restriction-composition isomorphism to obtain a map between
P restricted to V and Q restricted to V. The comparison isomorphisms for U and V
commute with this restriction: replace restriction by pullback, use associativity
of pullback composition and the equality of both composite maps with the map
from the stalk. Thus its stalk image is the same conjugate of f for V.
Zero ranks, zero complexes, and empty support intervals need no matrix entries;
their maps and equations are the unique ones involving zero objects. -/
theorem exists_restrict_chainMap_of_stalk_eventually
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (f : ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P ⟶
      ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q) :
    ∃ (U : Y.Opens), y ∈ U ∧ ∀ (V : Y.Opens) (hyV : y ∈ V), V ≤ U →
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let eP := (stalkRestrictionComplexIso V y hyV).app P
      let eQ := (stalkRestrictionComplexIso V y hyV).app Q
      ∃ (fV : R.obj P ⟶ R.obj Q), S.map fV = eP.hom ≫ f ≫ eQ.inv := by
  obtain ⟨U, hyU, fU, hU⟩ := exists_chainMap_of_stalk_local
    P Q a b c e hPa hPb hQc hQe hPfree hQfree y f
  exact ⟨U, hyU, restrict_chainMap_of_stalk_local P Q y U hyU f fU hU⟩

end AlgebraicGeometry.Scheme.Modules
