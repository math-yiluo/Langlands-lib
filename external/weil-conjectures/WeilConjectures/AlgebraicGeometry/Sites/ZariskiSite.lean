/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Topology.Sheaves.GrothendieckVanishing
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The small Zariski site of a scheme and Grothendieck vanishing

The small Zariski site `X_Zar` of a scheme `X` is the category `X.Opens` of open subsets of `X`
with jointly surjective families of open immersions as coverings
(`AlgebraicGeometry.Scheme.smallZariskiTopology`); its sheaves are the sheaves on the underlying
topological space. The cohomology `Hᵠ(X_Zar, F)` of an abelian sheaf `F` is
`AlgebraicGeometry.Scheme.zariskiH`, Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`
group `Extᵠ(ℤ, F)`, i.e. the `q`-th right derived functor of `F ↦ F(X)`.

* Flasque sheaves are Mathlib's `TopCat.Sheaf.IsFlasque`.
* Flasque sheaves are acyclic: `TopCat.Sheaf.IsFlasque.subsingleton_H`.
* Cohomology commutes with filtered colimits on a noetherian space:
  `TopCat.Sheaf.preservesColimitsOfShape_functorH`.
* Grothendieck vanishing: `TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt`, and
  `AlgebraicGeometry.Scheme.subsingleton_zariskiH_of_topologicalKrullDim_lt` for schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The small Zariski site.

The small Zariski site `X_Zar` of a scheme `X`: its objects are the open subschemes of `X`
(the category `X.Opens`), its morphisms the inclusions, and its coverings the jointly surjective
families of open subschemes. Abelian sheaves on `X_Zar` are the abelian sheaves on the
underlying topological space of `X`. -/
abbrev smallZariskiTopology (X : Scheme.{u}) : GrothendieckTopology X.Opens :=
  Opens.grothendieckTopology X

/-- Zariski sheaf cohomology.

The Zariski cohomology `Hᵠ(X_Zar, F)` of an abelian sheaf `F` on the small Zariski site of `X`:
the group `Extᵠ(ℤ, F)` in the category of abelian sheaves on `X_Zar`
(`CategoryTheory.Sheaf.H`), which is the `q`-th right derived functor of the global sections
functor `F ↦ F(X)`. -/
abbrev zariskiH {X : Scheme.{u}} (F : Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) (q : ℕ) :
    Type u :=
  Sheaf.H F q

/-- The Zariski dimension bound, for schemes.

Let `X` be a noetherian scheme of dimension at most `d`. Then `Hᵠ(X_Zar, F) = 0` for every
abelian sheaf `F` on the small Zariski site of `X` and every `q > d`. This is Grothendieck
vanishing `TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt` on the underlying noetherian
quasi-sober space. -/
theorem subsingleton_zariskiH_of_topologicalKrullDim_lt {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) {q : ℕ}
    (hq : topologicalKrullDim X < q) : Subsingleton (zariskiH F q) :=
  have : NoetherianSpace X.toTopCat := inferInstanceAs (NoetherianSpace X)
  have : QuasiSober X.toTopCat := inferInstanceAs (QuasiSober X)
  TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt (X := X.toTopCat) F hq

end AlgebraicGeometry.Scheme
