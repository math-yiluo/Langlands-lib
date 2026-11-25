/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ModuleSubobjectGenericConstancy
import WeilConjectures.AlgebraicGeometry.ConstructibleClosedGenericCriterion

/-!
# Constructibility of module subsheaves over Noetherian rings

Source: Stacks Project, Proposition 09BH (3), proof of (3), and Lemma 095E.
This is the coefficient-hypothesis step of the curve devissage proof, without any
cohomology conclusion (blueprint: lem-weil-pbc-constructible-module-subobject-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of a constructible module sheaf is constructible on a Noetherian scheme,
with coefficients in any Noetherian commutative ring.
Source: Stacks Project, Proposition 09BH (3), proof of (3), and Lemma 095E
(blueprint: lem-weil-pbc-constructible-module-subobject-noetherian).

Proof:
1. The monomorphism identifies its source with a subsheaf of its constructible target.
Work by Noetherian induction on closed
subsets of X. Pullback is exact, so the same inclusion holds on every closed subset.
Near a generic point of each irreducible component, restrict to a locally constant
stratum for the middle term and choose an etale trivialization. Remove the other
components of this etale neighbourhood. The middle term is now the constant sheaf
of a finitely generated module M on an irreducible scheme.
2. The geometric generic stalk of the subsheaf is a submodule N of M. Since the ring
is Noetherian, N has finitely many generators. Represent these generators by sections
on a common pointed etale neighbourhood. The sections' images are the fixed constant
sections of M, hence their two pullbacks agree; monicity makes their lifts agree.
Etale descent glues each lift over the open image of the neighbourhood. Shrink to
this open: the constant N is contained in the subsheaf. There are no additional
sections locally, since membership in a subsheaf of a constant sheaf is open and any
nonempty open of an irreducible scheme meets its generic point. This identifies the
subsheaf with constant N. Descent gives a finite locally constant subsheaf on a
nonempty open of each original component.
3. Remove these opens and apply induction to the proper closed complement. The
result is a finite locally closed stratification with finite locally constant
restrictions of the first term. Its parts are constructible because X is Noetherian,
so this is the existing predicate IsConstructibleSheaf.
The argument uses finite generation, not finiteness of the ring or its modules, and
also applies to the empty scheme, the zero sheaf and monomorphisms of constant sheaves. -/
theorem constructible_of_mono_noetherian
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsConstructibleSheaf G] :
    IsConstructibleSheaf F := by
  apply constructible_of_closed_generic F
  intro Z i hi hZ
  have : IsClosedImmersion i := hi
  have : IsNoetherian Z := hZ
  have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G) :=
    IsConstructibleSheaf.upperStar i G
  exact exists_dense_open_of_mono_noetherian
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).map φ)

end AlgebraicGeometry.Scheme
