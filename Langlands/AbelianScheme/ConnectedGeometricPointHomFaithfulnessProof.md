# Homomorphisms of abelian schemes over a connected base are detected at one geometric point: proof

The module `Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessProof`
proves the theorem
`Langlands.AbelianScheme.connectedGeometricPointHomFaithfulness`, whose type is
exactly the proposition
`Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessStatement.{u}`
of the module `Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessStatement`.
For a connected locally noetherian scheme `S : Scheme.{u}` on which every
positive integer is a unit in `Γ(S, ⊤)`, an algebraically closed field `Ω`,
a morphism `s : Spec Ω ⟶ S`, abelian schemes `A B : AbelianScheme S` and a
homomorphism `f : A ⟶ B`, if `(baseChange s).map f = 0` then `f = 0`.

## Implemented proof

The proof has four steps. The geometric point is used only in the first
step. The unit hypothesis is used twice: in the first step, for the
torsion kernels, and in the second, to make every residue field have
characteristic zero.

### Step 1: `f` kills every torsion kernel over `S`

For `n > 0` let `kernelι (multiplication A.toGrp n)` be the inclusion of
the scheme kernel `A[n]` of multiplication by `n`. The first step proves
that `kernelι (multiplication A.toGrp n) ≫ groupHom f = 1` for every
`n > 0`.

The helper `levelMap_eq_zero_of_baseChange_eq_zero` proves the following.
Let `b : S' ⟶ S` be a morphism with `(baseChange b).map f = 0`, and let
`T` be any scheme over `S'`, viewed over `S` through `b`. Then the level map
`GroupScheme.Tate.levelMap` of `groupHom f` on the level-`n` points of `A`
over `T` is zero. Every such point is the image under the equivalence
`GroupScheme.Tate.levelBaseChange b` of a level-`n` point of the pullback
of `A`. The naturality lemma `GroupScheme.Tate.levelBaseChange_map` turns
the level map of `f` into the level map of the pulled-back homomorphism.
That homomorphism is `groupHom ((baseChange b).map f)` by definition, so it
is `groupHom 0`. The helper `levelMap_groupHom_zero` shows that the level
map of `groupHom 0` is zero: the underlying section of an image point is a
section followed by the unit morphism, which is the unit (`MonObj.comp_one`).
The level map is then compared through the injective map
`GroupScheme.Tate.toSection`.

Take `b = s` and `T = Spec Ω` over itself. Then `T`, viewed over `S`, is the
geometric point `𝟙 _ ≫ s`, and all level maps of `f` at this point vanish.
The published theorem
`Langlands.AbelianScheme.Tate.kernel_comp_eq_one_of_levelMap_eq_zero`, from
`Langlands.AbelianScheme.Tate.ConnectedTorsionDetection`, takes the
connected locally noetherian base, the unit `n`, and the published theorem
`Langlands.AbelianScheme.torsionFiniteEtale` (finite étaleness of `A[n]`).
From the vanishing of the level maps at this one geometric point it gives
`kernelι (multiplication A.toGrp n) ≫ groupHom f = 1`.

### Step 2: `f` vanishes after base change to every geometric point

Let `t : Spec K ⟶ S` be any morphism from the spectrum of an algebraically
closed field `K`.

The helper `charZero_of_isUnit_natCast` proves that `K` has characteristic
zero. The ring map `Γ(S, ⊤) → K` given by `t` on global sections, followed by
`Scheme.ΓSpecIso`, sends units to units. So the image of every positive
integer in `K` is a unit, hence nonzero, and `charZero_of_inj_zero` applies.

The helper `levelMap_eq_zero_of_kernel_comp_eq_one` proves the following.
If `kernelι (multiplication A.toGrp n) ≫ groupHom f = 1`, then the level map
of `groupHom f` on level-`n` points over any test scheme is zero. By
`GroupScheme.Tate.kernelLevelEquiv`, every level-`n` point comes from a
section `z` of the kernel. Its image has underlying section
`z ≫ kernelι _ ≫ groupHom f = z ≫ 1 = 1`.

The helper `baseChange_eq_zero_of_kernel_comp_eq_one` combines these with
two published results from `Langlands.AbelianScheme.Tate`.
`hom_eq_zero_of_dense_twoPowerTorsion` says that if the two-power torsion
locus of an abelian variety over `K` is dense, a homomorphism out of it whose
level maps at the levels `2 ^ m` all vanish is zero.
`fieldTwoPowerTorsionDensity` supplies the density, which requires `K` to be
algebraically closed of characteristic zero. To see that the level maps of
`(baseChange t).map f` at the rational points of `Spec K` vanish, the proof
applies the injective map `GroupScheme.Tate.levelBaseChange t` and the
naturality lemma `GroupScheme.Tate.levelBaseChange_map`. This reduces the
claim to the level maps of `f` over `Spec K`, viewed over `S` through `t`.
Those vanish by Step 1 and `levelMap_eq_zero_of_kernel_comp_eq_one` with
`n = 2 ^ m`. Hence `(baseChange t).map f = 0`.

### Step 3: `f` agrees pointwise with the zero homomorphism

The helper `hom_apply_eq_of_baseChange_eq_zero` proves the following. Let
`t : Spec K ⟶ S` be any morphism from the spectrum of a field `K` with
`(baseChange t).map f = 0`. Then every point `x` of `A` lying over the image
of a point `y` of `Spec K` satisfies `hom f x = η[B.X].left (A.X.hom x)`.
Let `T` be the fibre product `A ×_S Spec K`, viewed over `Spec K` through
the second projection. Its identity is a `T`-valued point of the pulled-back
`A`. Composing it with the pulled-back homomorphism gives the unit, because
that homomorphism is zero. The equivalence `GroupScheme.baseChangePointsEquiv`
is multiplicative, and `GroupScheme.baseChangePointsEquiv_comp` makes it
compatible with composition. Transporting the equation along it and taking
underlying scheme morphisms gives

```text
pullback.fst A.X.hom t ≫ hom f = pullback.snd A.X.hom t ≫ t ≫ η[B.X].left.
```

Mathlib's `Scheme.Pullback.exists_preimage_pullback` gives a point `z` of
the fibre product with first projection `x` and second projection `y`.
Evaluating both sides at `z` gives `hom f x = η[B.X].left (t y)`, and
`t y = A.X.hom x`.

In the main theorem, a point `x` of `A` is handled as follows. Let `κ` be the
residue field of `S` at `A.X.hom x` and let `K = AlgebraicClosure κ`. Put
`t = Spec.map (algebraMap κ K) ≫ S.fromSpecResidueField (A.X.hom x)`. Step 2
gives `(baseChange t).map f = 0`. The unique point `y` of `Spec K` maps to
`A.X.hom x` by `Scheme.fromSpecResidueField_apply`. Step 3 then gives
`hom f x = η[B.X].left (A.X.hom x)` for every point `x`.

### Step 4: from pointwise to global equality

The helper `unit_comp_hom` records that every homomorphism `g` preserves the
unit sections: `η[A.X].left ≫ hom g = η[B.X].left`. It follows from
`IsMonHom.one_hom`.

The structure morphism `A.X.hom` is smooth and proper with geometrically
connected fibres. The published theorem
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`, from
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`,
therefore gives `IsIso (A.X.hom.app U)` for every open `U` of `S`. The unit
section satisfies `η[A.X].left ≫ A.X.hom = 𝟙 S` (`Over.w`). By Step 3 and
`unit_comp_hom`, `hom f x = (η[A.X].left ≫ hom f) (A.X.hom x)` for every
point `x`. The published theorem
`Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions`, from
`Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof`, therefore
gives the equality of scheme morphisms

```text
hom f = A.X.hom ≫ η[A.X].left ≫ hom f = A.X.hom ≫ η[B.X].left.
```

The right-hand side is `hom 0` by definition. Extensionality for morphisms
in `Over S`, for group-object homomorphisms (`Grp.hom_ext`) and for the
`Additive` wrapper of the homomorphism group gives `f = 0`.

## Provenance

The statement's Markdown cites Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, third enlarged edition (1994), Chapter 6, §1,
Proposition 6.1 (the rigidity lemma, printed p. 115) and Corollary 6.2
(printed pp. 116–117). There, Corollary 6.2 applies Proposition 6.1, in its
case of a proper flat `p`, directly over the connected base to the pointwise
difference `f · g⁻¹` of its two maps `f, g : X → G`; for the present
statement these are the given homomorphism and the zero homomorphism. The
proof of Proposition 6.1 treats the one-point base and the Artinian
thickenings of a point as intermediate steps. The implemented proof does not
follow that argument. It is an internal derived route that uses the torsion
and global-functions results instead. Torsion vanishing is propagated from
one geometric fibre to every fibre through the
finite étale torsion kernels over the connected base, and the
characteristic-zero density of two-power torsion detects vanishing on each
geometric fibre. The section/global-functions factorization then turns
pointwise agreement into equality of scheme morphisms. The geometric inputs
are the published theorems named above; their own Markdown files give their
proofs and sources. The helpers in this module are formal calculations with
torsion points, base change and fibre products.
