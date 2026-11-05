# Character-linear kernel towers for actual triangular diagonal images

`Langlands.GroupScheme.TriangularDiagonalKernelTowerStatement.{u}` is a
Prop-valued statement definition. This module states the tower-existence
target and supplies no proof of it.

## Exact quantifiers and hypotheses

The universe `u` is arbitrary. Quantify over every field `k : Type u` and
put `R := CommRingCat.of k`, `B := Spec R`. Let `H : GroupScheme B` be any
actual group scheme with `LocallyOfFiniteType H.X.hom` and
`IsAffineHom H.X.hom`. These are conditions on its structural morphism to
`B`; affineness also gives quasi-compactness, so together they express the
affine finite-type convention for Milne's algebraic groups over a field.

For every natural number `N`, including zero, and every homomorphism

```text
j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
  (fun i => -(i.val : ℤ)),
```

assume `IsClosedSubgroup j`. Thus the underlying scheme map of `j` is a
closed immersion. Define

```text
L := GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ))
f : H ⟶ L := j ≫ GeneralLinear.blockLimitHom (Fin N) R
  (fun i => -(i.val : ℤ)).
```

The decreasing, pairwise distinct weights make the parabolic scheme the
upper triangular group and its Levi scheme the diagonal group. The existing
`GeneralLinear.pointsEquiv_blockLimitHom` identifies `blockLimitHom` on
every test scheme with the block diagonal projection, hence here with the
ordinary diagonal projection. The actual scheme kernel `kernel f` is the
intersection of `H` with the upper unitriangular group.

For every `Λ : Type u` with `AddCommGroup Λ` and `AddGroup.FG Λ`, define
`D := Diagonalizable.groupScheme R Λ`, an actual commutative group scheme.
Finite generation permits torsion; no freeness of `Λ` is assumed. For
every pair of actual homomorphisms `q : H ⟶ D.toGrp` and
`d : D.toGrp ⟶ L`, assume exactly

```text
IsClosedSubgroup d
q ≫ d = f
RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q.
```

The conclusion is

```text
LinearKernelTower.AdmitsTower D q.
```

Thus the conclusion concerns the supplied `q` and the supplied `D(Λ)`.
There is no existential replacement of this map by an unspecified quotient.
No smoothness, connectedness, reducedness, perfectness, characteristic or
algebraic-closure hypothesis is imposed. No series or section is assumed.

## Actual kernels and the all-test meaning

`kernel f` and `kernelι f` are the existing actual group-scheme kernel
and its inclusion, constructed by pullback along the target's unit.
`SubgroupFunctor.range (kernelι f)` is its image subgroup on every test
scheme over `B`. The supplied `IsFppfQuotient` hypothesis says that the
underlying scheme map of `q` is flat, surjective and locally of finite
presentation, and that

```text
SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range (kernelι f).
```

This is equality of subgroup functors on every test scheme, including
nonreduced tests. Scheme surjectivity does not require surjectivity of
`H(T) → D(T)` for every original test `T`. The factorization with the closed
immersion `d` and this fppf condition express the supplied actual diagonal
image, rather than just an image on field-valued points.

The conclusion reuses `LinearKernelTower.AdmitsTower` without modification:
there exists `n : ℕ` with `LinearKernelTower.HasTower D n q`. Unfolding that
predicate gives

```text
H = E₀ --p₀--> E₁ --p₁--> ⋯ --pₙ₋₁--> Eₙ,
qᵢ : Eᵢ ⟶ D.toGrp,
q₀ = q,  pᵢ ≫ qᵢ₊₁ = qᵢ.
```

Every stage is affine and locally of finite type over `B`. Each `pᵢ` is an
actual fppf quotient by its full actual kernel `Kᵢ := kernel pᵢ`, and
`IsCharacterLinearKernel D qᵢ pᵢ` holds. The latter supplies a closed
subgroup homomorphism `aᵢ : Kᵢ ⟶ VectorGroup.groupScheme R 1`, a character
`χᵢ : characterLattice D` and an action
`bᵢ : AutomorphicAction D.toGrp Kᵢ`. Writing `ιᵢ := kernelι pᵢ`, for
every `T : Over B`, `g : T ⟶ Eᵢ.X`, `x : T ⟶ Kᵢ.X` and
`t : T ⟶ D.X`, the two required equations are

```text
bᵢ.act (g ≫ qᵢ.hom.hom) x ≫ ιᵢ.hom.hom =
  g * (x ≫ ιᵢ.hom.hom) * g⁻¹
bᵢ.act t x ≫ aᵢ.hom.hom =
  (VectorGroup.weightAction (n := 1) χᵢ).act t (x ≫ aᵢ.hom.hom).
```

Conjugation at the current stage therefore factors through its structural
map to the fixed `D`, and the closed embedding of its kernel into `Ga` is
equivariant for a linear action through a character of `D`. These are
all-test equations on actual scheme kernels. Each kernel may be finite,
nonreduced or trivial; each character may be trivial.

At the terminal stage, `IsIso qₙ` is required for the actual structural
map `qₙ`. An abstract isomorphism between `Eₙ` and `D.toGrp` would not
suffice. Length zero is allowed and means `IsIso q` together with the
affine and local finite-type source conditions.

## Derived provenance and remaining obligations

The original is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field*, corrected reprint (2022), registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
Theorem 16.21 and its proof are on printed pp.330–331 (zero-based PDF
indices **340–341** in the registered file).

For a trigonalizable algebraic group over an arbitrary field, that theorem
provides a normal series
`H ⊃ H₀ ⊃ ⋯ ⊃ Hᵣ = 1`, with `H₀ = Hᵤ`. Its proof starts with the given
embedding in the upper triangular group, identifies `Hᵤ` with the
intersection with the upper unitriangular group, and intersects the standard
unitriangular filtration with `H`. Each factor `Hᵢ/Hᵢ₊₁` embeds as a closed
subgroup of `Ga`; conjugation factors through the diagonal image `H/Hᵤ`
and the embedding is equivariant for a linear action of that image on `Ga`.
The stronger smooth-factor refinement in Corollary 16.22 is not used.

The present assertion is an internal reformulation of this series for the
Library's actual triangular model and supplied factorization. Reorienting
the series gives

```text
H = H/Hᵣ → H/Hᵣ₋₁ → ⋯ → H/H₀ → D.
```

The transition `H/Hᵢ₊₁ → H/Hᵢ` has kernel `Hᵢ/Hᵢ₊₁`. Its conjugation
action must be descended to the current quotient and transported, with its
closed additive embedding, to the actual transition kernel. The supplied
fppf quotient identifies the induced terminal structural map `H/H₀ → D`
as an actual isomorphism. Constructing these quotients, proving their
geometric and fppf properties, and transporting the all-test actions are
steps required of a proof of this statement; they are not proved here.
Allowing duplicate trivial steps and zero length agrees with the existing
tower predicate.

Image existence is the separate `AffineHomImageStatement` obligation.
Presenting the closed diagonal image as some `D(Λ)` is the separate
`Diagonalizable.ClosedSubgroupPresentationStatement` obligation. Here `Λ`,
`q`, `d` and their image properties are already inputs. Tower existence is
the proposition stated in this module and remains to be proved. Section
existence is a further splitting obligation, with its own hypotheses and
proof; this statement asserts no section.

The [official 2022 errata](https://www.jmilne.org/math/Books/iagerrata2022.html),
read on 2026-11-04 and retained as
`milne-2022-algebraic-groups-errata-2026-11-04` (SHA256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`),
has no correction to Theorem 16.21 or printed pp.330–331.
