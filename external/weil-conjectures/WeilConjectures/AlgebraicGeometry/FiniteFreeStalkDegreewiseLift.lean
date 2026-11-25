/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftCore
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkDegreewiseLocal

/-! # Extending degreewise stalk maps

Source: the finite matrix extension argument of lemma-coherent-base-change-invertible-sheaves--3,
expanded in lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A family of degreewise stalk maps extends, without imposing chain equations.

Source: lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2, expanding the
finite matrix extension argument of lemma-coherent-base-change-invertible-sheaves--3.

Proof: Choose the finite free bases of every nonzero term of P and Q. Pullback
preserves these finite free sheaves, so a component t n between nonzero terms
is a finite matrix over the stalk ring O_{Y,y}. Only degrees in the intersection
of [a,b] and [c,e] can have a nonzero component. Represent each of their finitely
many entries by a structure-sheaf section on a neighbourhood of y, and intersect
these neighbourhoods. Restrict the chosen sections and bases to this intersection U
and define g n by the represented matrix. If either term is zero, use the unique
map instead. The comparison stalkRestrictionComplexIso is the termwise comparison
of restriction with pullback along the open inclusion and composition with the
stalk map. Under it each represented section maps to its prescribed germ, giving
the asserted component equation. Empty support intersections or rank-zero terms
have no entries to extend; take U to be the whole scheme when the entry list is
empty. No differential-commutativity hypothesis is assumed or concluded.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift) -/
theorem exists_degreewise_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g : ∀ n : ℤ,
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      ∀ n : ℤ, (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by
  obtain ⟨U, hyU, hg⟩ := exists_degreewise_of_stalk_local_core P Q a b c e
    hPa hPb hQc hQe y t
    (exists_local_degreewise_of_stalk_local P Q hPfree hQfree y t)
  let g : ∀ n : ℤ,
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n :=
    fun n ↦ Classical.choose (hg n)
  refine ⟨U, hyU, g, ?_⟩
  intro n
  exact Classical.choose_spec (hg n)

end AlgebraicGeometry.Scheme.Modules
