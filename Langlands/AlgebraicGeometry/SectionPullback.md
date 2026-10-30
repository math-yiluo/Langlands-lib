# Actual section pullback and compatible-basis determinant transport

This internal derived module supplies section-level maps for Mathlib's actual
pullback of sheaves of modules on schemes. It connects adjunction-unit
naturality with the previously constructed determinant polynomial. It is a
prerequisite for transporting the Harris Lie determinant condition; it does not
assert that condition for an arbitrary abelian scheme.

## Actual sections and coherence

For schemes `X Y : Scheme.{u}`, a morphism `f : X ⟶ Y`, a module sheaf
`M : Y.Modules`, and any open `U : Y.Opens`, `sectionPullback f M U` is

```text
Γ(M,U) →ₛₗ[(f.app U).hom] Γ(f* M,f⁻¹ U).
```

The underlying function is the component on `U` of the unit of the actual
`pullbackPushforwardAdjunction f`. Its semilinearity is inherited from that
unit as a morphism of module presheaves. The opens need not be affine.

`sectionPullback_restrict` identifies restriction after pullback with pullback
after restriction, using the actual maps of opens and the actual module
presheaf restriction maps. This is naturality of the unit as a sheaf morphism.
`sectionPullback_naturality` intertwines every module-sheaf morphism with its
actual pulled-back morphism, by naturality of the adjunction unit in the module.

`sectionPullback_id` says that the canonical `pullbackId` comparison takes an
identity-pulled section back to the original section. It follows from the
adjunction conjugacy equation for that comparison. `sectionPullback_comp`
says that `pullbackComp` takes two successive section pullbacks to the section
pulled back along the composite. It is the componentwise form of the published
`pullbackPushforwardAdjunction_unit_comp` equation.

`sectionEndomorphism M U` evaluates an actual sheaf endomorphism on `U` as a
linear endomorphism over `Γ(Y,U)`. It is a unital ring homomorphism. The
multiplication convention agrees with the composition convention of
`CategoryTheory.End` and `Module.End`.

## Compatible finite bases

The first three results are general linear algebra, in
`Langlands.Shimura.HodgeDeterminant`. Let `g : R →+* S` be any homomorphism of
commutative rings, let `F : M →ₛₗ[g] N`, and let `b` and `c` be finite bases
with the same index type. Assume explicitly that `F (b i) = c i` for every
index `i`.

- `repr_semilinear_basis` identifies the coordinates of `F x` in `c` with
  `g` applied to the coordinates of `x` in `b`. Its proof expands `x` in `b`,
  applies semilinearity, and uses the coordinate values of the basis `c`.
- `toMatrix_semilinear_basis` says that if endomorphisms `a` and `a'`
  satisfy `F (a x) = a' (F x)` for every `x`, then the matrix of `a'` in `c`
  is the entrywise `g`-image of the matrix of `a` in `b`. The proof applies
  the coordinate formula to each basis vector.
- `polynomial_semilinear_basis` applies the same result to a finite family of
  intertwining endomorphisms. The universal determinant polynomial in the
  target equals the coefficientwise `g`-image of the source polynomial. The
  proof compares the universal matrices and uses that ring homomorphisms
  commute with determinants.

In `Langlands.Scheme.Modules`, `sectionPullback_toMatrix` and
`sectionPullback_determinant` specialize those formulas to the actual section
map, the coefficient map `(f.app U).hom`, and the actual pullbacks of sheaf
endomorphisms. The intertwining hypotheses are proved by
`sectionPullback_naturality`. They retain an explicit hypothesis that the given
source basis is carried to the given target basis. This module does not
construct that target basis from a sheaf trivialization, or assert that
arbitrary section modules commute with extension of scalars. It also does not
identify the pullback of an abelian scheme's Lie module with the Lie module
of its base change.

## Provenance and scope

These are internal consequences of the actual adjunction and the published
`HodgeDeterminantBaseChange` polynomial, rather than translations of an
additional literature theorem. The implementation imports the existing
pullback-unit composition proof in `ModuleLocalHomPullbackProofs` and reuses the
existing determinant definition. The published global-section construction
`Langlands.SchemeModule.pullbackSection` remains a separate API; the present
map works on every open and records semilinearity and the above compatibilities.

No flatness, reducedness, nontriviality, or domain hypothesis is used. Both
coefficient rings may have nilpotents. The generic ring, module, and finite
basis index universes are independent. The two schemes have the same arbitrary
universe `u`; the finite basis index and the finite family of endomorphisms may
have independent universes. All maps and displayed identities are constructed
or proved, with no unproved mathematical premise except the explicitly supplied
compatible bases and intertwining hypotheses of the generic formulas.
