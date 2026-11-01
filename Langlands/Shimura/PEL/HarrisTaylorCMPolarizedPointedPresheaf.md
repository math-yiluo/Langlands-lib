# The actual pointed normalized CM polarized tower presheaf

Author: Worker 57.

This derived construction assembles the existing actual normalized CM
polarized class towers and their proved pullbacks into a contravariant
functor. Its base category is the full category of actual pointed schemes
over the CM field satisfying the explicit conditions below. Its values are
functors on the original Harris level and Hecke transporter category.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The fixed
arithmetic inputs are universe-zero fields: the totally real number field
`E`, its quadratic CM extension `F`, and the imaginary quadratic CM number
field `L` with its displayed algebra structure on `F`. The central simple
unitary datum is `D`, and the charts `C` use precisely
`harrisCMSection E (algebraMap L F) τ₀`. The field `Ω` is fixed and need not be
algebraically closed.

`PointedBase F Ω` is Mathlib's actual structured-arrow category

```text
StructuredArrow (Spec Ω) (Over.forget (Spec F)).
```

An object consists of an actual `Scheme.{0}` `S`, a structural map
`p : S ⟶ Spec F`, and a point `s : Spec Ω ⟶ S`. An arrow from
`(T, q, t)` to `(S, p, s)` is an actual scheme map `b : T ⟶ S`
satisfying `b ≫ p = q` and `t ≫ b = s`. These are the ordinary `Over` and
structured-arrow commuting triangles. Identities and composition come from
those categories.

`AdmissiblePointedBase` is a proposition on such an object, with the
following fields:

- The scheme is quasi-separated, and the displayed point has finite fibres
  on every object of its existing small finite-etale category `Cover`.
- Every positive torsion order indexed by `Index (fun _ => True)` is a unit
  in the ring of global sections.
- The actual roots-of-unity group scheme `mu S k.val` is finite and etale
  for each such index.
- `LieBaseChangeNaturalityStatement S` holds.
- The existing `PositivePairAdditivity` holds for the actual polarized
  actions with the positive auxiliary involution determined by `D` and `C`.
- For every actual abelian scheme `B` over `S`,
  `DualEvaluationData preservation stability B` is nonempty.

The last field supplies constrained dual construction inputs: an actual
dual scheme, its geometry, an inverse Poincare line bundle and evaluation
isomorphism, and dual endomorphism additivity. It specifies neither an
output polarized class nor a desired functoriality equation.
`AdmissiblePointedBaseCategory` is the `ObjectProperty.FullSubcategory`
of these objects. Its arrows have no further restrictions or supplied
pullback maps. The module exposes the quasi-separatedness, finiteness and
etaleness fields as instances. No flatness or reducedness assumption is
added.

The fixed construction parameters remain explicit: tensor pullback
comparison, composition, unit, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, Mumford bundle membership and universal
base change; dual base-change naturality and polarization stability; finite
Weil transition compatibility; the rational profinite-integer/finite-adele
comparison; and torsion finite etaleness. The admissible category itself
depends only on the parameters appearing in its displayed object conditions.

`pointedClassTower X` is the existing
`HarrisNumericalWeilLevel.isoClassTower` at the actual point `X.obj.hom`.
Its CM map is `X.obj.right.hom`; this same map determines the conjugated
normalized reflex structure `D.harrisTaylorReflexStructure C ...`.
There is no independent choice of reflex map. The tower retains the
existing numerical subtype of determinant-compatible polarized classes.
The joint image condition keeps one actual representative satisfying
the determinant, geometric dimension and central Lie trace together.
The imported normalized comparison identifies this with normalized
determinant and dimension on that representative. Dimension remains an
existential property of a representative. The level category is the
unchanged `HarrisLevel D`, including subgroup forgetting and Hecke
transporters.

For `f : Y ⟶ X`, `pointedPullbackDualData f` uses classical choice only on
`Y.property.dualExists` applied to the actual base change of the source
abelian scheme along `f.hom.right.left`. `pointedClassTowerPullback f`
then applies `classTowerBaseChangeAlong` to that underlying scheme map,
the actual source and target structure maps and points, and the two
commuting triangles. Its components are the existing actual polarized
pullbacks. Its naturality includes every arrow in the Harris level
category.

`pointedClassTowerPullback_id` is exactly the imported aligned identity
law. `pointedClassTowerPullback_comp` is exactly the imported aligned
composition law, with independently chosen constrained dual families for
the two arrows and their composite. Underlying category composition is
the composition used by that law; proof irrelevance identifies the
triangle and admissibility witnesses.

`pointedClassTowerPresheaf` has type

```text
AdmissiblePointedBaseCategory ... ᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1).
```

It sends `X` to `pointedClassTower X.unop`, and an opposite arrow `f`
to `pointedClassTowerPullback f.unop`. Its identity proof is the preceding
identity theorem, and its composition proof is the symmetric form of the
preceding contravariant composition theorem. Thus the values, maps and
both functor laws are constructed.

Provenance is internal: Mathlib's structured-arrow and full-subcategory
constructions organize the actual normalized polarized pullbacks from
`HarrisTaylorCMPolarizedAlignedBaseChange`. Arithmetic normalization,
polarizations, level structures, quotients and their literature
provenance remain those of the imported paired modules. This pair makes
no new original-literature claim.

This is a conditional pointed functor on the stated admissible category.
It does not establish these geometric premises on all schemes, remove
the chosen field-valued point, construct an unpointed polarized moduli
functor, or prove representability. Representing scheme levels, canonical
models and coefficient descent remain further constructions.
