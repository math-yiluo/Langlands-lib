# Natural forgetting from pointed polarized CM towers

Author: Worker 57.

This derived construction makes forgetting the actual polarization and Weil
level natural in the pointed base as well as in the Harris level. Its target
is the restriction of the existing joint normalized CM action presheaf,
followed by the constant-tower functor. No second action-class presheaf is
defined.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic
data, charts, positive auxiliary involution, normalized conjugated reflex
structure, torsion and Weil data, and explicit tensor/Picard/duality premises
are those of `HarrisTaylorCMPolarizedPointedPresheaf`. In particular, `E`, `F`
and `L` are the displayed universe-zero number fields, `D` is the actual
central simple unitary datum, the charts use the fixed Harris CM section,
and the field `Ω` is fixed. All source and target objects are actual schemes;
the tower values are the existing polarized rational-isomorphism classes,
with one representative satisfying the joint determinant and numerical
conditions.

For actual maps `b : T ⟶ S`, `p : S ⟶ Spec F` and `q : T ⟶ Spec F` with
`b ≫ p = q`, `actionClassBaseChangeAlong` aligns the existing
`actionClassBaseChange` with this triangle by equality elimination. It
requires `LieBaseChangeNaturalityStatement S`. Its `_val` theorem computes
the underlying class as exactly

```text
RationalAlgebraAction.pullbackClass b x.val.
```

`classTowerBaseChangeAlong_forgetCMAction` adds actual points
`s : Spec Ω ⟶ S` and `t : Spec Ω ⟶ T` with `t ≫ b = s`, their finite-fibre
witnesses, and the same quasi-separatedness, torsion-unit, finite-etale
roots-of-unity, ordered-pair additivity and constrained pullback-dual inputs
as the aligned polarized pullback. It proves the square

```text
aligned polarized pullback ≫ forget at (q,t)
  = forget at (p,s) ≫ constant tower on aligned action pullback.
```

Its proof eliminates the two commuting triangles and applies the existing
raw `classTowerBaseChange_forgetCMAction`. Thus both paths use the same
actual pulled-back abelian scheme and action; no desired comparison equation
is supplied as a premise.

`pointedBaseForgetToCM` sends an object of the admissible pointed category
to its actual `Over (Spec F)` object and sends an arrow to its actual
over-category arrow. Its identity and composition proofs are reflexivity.
All admissibility conditions remain those of the imported full subcategory:
quasi-separatedness; finite point fibres on finite-etale covers; invertible
positive torsion orders; finite and etale roots of unity; local Lie
base-change naturality; positive ordered-pair dual additivity; and
nonempty constrained dual-evaluation data for every actual abelian scheme.

For the following restriction, this module explicitly retains the existing
action presheaf's additional premise

```text
allNaturality : ∀ S : Scheme.{0}, LieBaseChangeNaturalityStatement S.
```

`pointedActionTowerPresheaf` is exactly the composite

```text
(pointedBaseForgetToCM).op
  ⋙ D.harrisTaylorCMActionPresheaf C allNaturality
  ⋙ Functor.const (HarrisLevel D).
```

The object formula identifies its value at `(S,p,s)` with the constant
tower on `D.HarrisTaylorCMActionClass C p`. The map-value formula identifies
every level component with actual rational-action class pullback along the
underlying scheme arrow. The point is forgotten in this target; it is
retained in the polarized source. Joint action classes still require one
actual representative with normalized determinant and prescribed geometric
dimension. No invariance of dimension under all rational isomorphisms is
asserted.

`pointedForgetCMAction X` is the existing `forgetCMActionNatTrans` at the
structure map and point of `X`. Its naturality in the Harris level, including
every Hecke transporter, is inherited from that actual construction.
`pointedForgetCMAction_naturality` proves naturality in a pointed base
arrow. It applies the aligned square above to the arrow's two actual
triangles, takes its level components and underlying subtype values, and
uses `actionClassBaseChangeAlong_val` to identify the target map with the
restricted action presheaf map. Subtype extensionality then proves the
desired square. Proof irrelevance identifies the local Lie-naturality
witness with the one used by the existing action presheaf.

`pointedForgetCMActionNatTrans` assembles these maps into a natural
transformation from `pointedClassTowerPresheaf` to
`pointedActionTowerPresheaf`, both valued in
`HarrisLevel D ⥤ Type 1`. Its component theorem is reflexivity.
The construction is therefore compatible with varying the actual base and
the original Harris level simultaneously.

Provenance is internal: equality elimination aligns the existing actual
action and polarized pullbacks; functor composition restricts the existing
joint CM action presheaf; its previously constructed forgetful maps supply
the components. Original arithmetic, geometry and normalization retain the
literature provenance of the imported paired modules. This pair makes no
new original-literature claim.

The result remains conditional on the named geometric premises and on
`allNaturality`. It does not prove these premises, remove the point from the
polarized source, construct the unpointed PEL moduli functor, prove
representability, define representing scheme levels, or supply canonical
models or coefficient descent.
