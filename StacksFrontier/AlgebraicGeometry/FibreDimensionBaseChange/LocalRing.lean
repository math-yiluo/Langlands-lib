module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The local ring of a fibre after base change

Let `f : X ⟶ S` be locally of finite type and let

```
X' ---g'---> X
|            |
f'           f
v            v
S' ---g----> S
```

be a fibre product diagram. Fix `x' : X'` and write `x = g' x'`, `s' = f' x'` and
`s = g s' = f x`. The morphism of fibres `X'_{s'} ⟶ X_s` induced by the square is
`AlgebraicGeometry.fiberMap`; let `F` be its fibre over `x`. The dimension of the local ring of
`F` at `x'` measures exactly the dimension gained by the base change: it is the difference
`dim O_{X'_{s'}, x'} - dim O_{X_s, x}` and also the difference
`trdeg_{κ(s)} κ(x) - trdeg_{κ(s')} κ(x')`. In particular the local dimension of the fibre cannot
drop and the residue-field transcendence degree cannot grow. Moreover, with `s'`, `s` and `x`
given, the point `x'` above them can be chosen so that neither invariant changes.

Both differences are stated additively, Krull dimensions of rings taking values in `WithBot ℕ∞`
and transcendence degrees being compared through `Cardinal.toENat`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat` is the
  scheme-theoretic dimension formula for a flat morphism (Stacks Tag 00ON): the local dimension
  of the source is the local dimension of the target plus the local dimension of the fibre.
* `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_eq` and
  `AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_trdeg_eq` are the two equalities of
  **Stacks Tag 02FY part (2)**.
* `AlgebraicGeometry.ringKrullDim_stalk_fiber_le_of_baseChange` and
  `AlgebraicGeometry.trdeg_residueField_le_of_baseChange` are the two inequalities they imply.

## Implementation notes

The induced morphism of fibres is the pullback square of residue fields supplied by
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, so it is flat, being a base
change of the field extension `κ(s) ⟶ κ(s')`. Both fibres are locally Noetherian because `f` is
locally of finite type over a field, so the dimension formula for a flat local homomorphism of
Noetherian local rings applies to the stalk map, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk` identifies its closed fibre with the local ring
of the fibre. The passage to transcendence degrees uses the invariance of the *topological*
dimension of the fibre, which is part (1) of the same tag, together with the dimension formula
for a fibre at a point (Stacks Tag 02FX).

Points of successive fibres are named canonically by `AlgebraicGeometry.Scheme.Hom.asFiber`, so
no choice of a point of a fibre product is made.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Flat

/-- **Stacks Project, Tag 00ON.** For a flat morphism of locally Noetherian schemes, the
dimension of the local ring at a point is the dimension of the local ring at its image plus the
dimension of the local ring of the fibre through the point. -/
public theorem ringKrullDim_stalk_eq_add_ringKrullDim_stalk_fiber_of_flat {A B : Scheme.{u}}
    (φ : A ⟶ B) [Flat φ] [IsLocallyNoetherian A] [IsLocallyNoetherian B] (a : A) :
    ringKrullDim (A.presheaf.stalk a) =
      ringKrullDim (B.presheaf.stalk (φ a)) +
        ringKrullDim ((φ.fiber (φ a)).presheaf.stalk (φ.asFiber a)) := by
  let : Algebra ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a) :=
    (φ.stalkMap a).hom.toAlgebra
  have hflat : Module.Flat ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a) := by
    change (φ.stalkMap a).hom.Flat
    exact Flat.stalkMap φ a
  have : IsLocalHom
      (algebraMap ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a)) := by
    change IsLocalHom (φ.stalkMap a).hom
    infer_instance
  have hfibre : ringKrullDim
      (ClosedFibre ↥(B.presheaf.stalk (φ a)) ↥(A.presheaf.stalk a)) =
      ringKrullDim ((φ.fiber (φ a)).presheaf.stalk (φ.asFiber a)) :=
    ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk φ a)
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre _ _ hflat, hfibre]

end Flat

section BaseChange

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

end BaseChange

end AlgebraicGeometry

end
