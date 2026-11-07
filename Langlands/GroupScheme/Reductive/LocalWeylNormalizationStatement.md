# Weyl normalization of opposite root groups: rescaling and statements

Module `Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement`.

This module splits the Weyl normalization step of the Isomorphism Theorem over a reduced local
ring into a field-level statement and a ring-level statement. It also supplies the rescaling
endomorphisms of `𝔾ₐ` that both statements use. The module proves only the small lemmas about
rescaling, no theorem about reductive groups.

Notation is that of `LocalSplitCell`: `R` is a commutative ring, `G` a group scheme over
`Spec R`, `i : splitTorus (Spec R) I ⟶ G` a homomorphism from the coordinate split torus
`𝔾ₘ^I`, `Ga R` the additive group over `Spec R`, and `rootPoint u Z c` the point `u(c)`.

## Rescaling `𝔾ₐ`

- `baseScalar Z : R →+* Γ(Z, 𝒪_Z)` is the structure map of a scheme `Z` over `Spec R`.
  `appTop_baseScalar` says it is natural in `Z`.
- `gaCoord a` is the coordinate of a point `a : Z ⟶ 𝔾ₐ`.
- `scalePoints d Z` is the group homomorphism `x ↦ d x` on the points of `𝔾ₐ` over `Z`, and
  `scaleHom d : Ga R ⟶ Ga R` is the group-scheme endomorphism it defines, obtained from the
  Library's `homOfPoints`. `comp_scaleHom` computes it on points.
- `rootPoint_scaleHom`: `(v ∘ scaleHom d)(c) = v(d c)`.
- `hom_ext_rootPoint`: two maps out of `𝔾ₐ` with the same values `rootPoint` on every test
  scheme are equal.
- `scaleHom_comp_scaleHom` (`scaleHom d ≫ scaleHom e = scaleHom (e * d)`) and `scaleHom_one`.
- `scaleIso c` is the automorphism of `𝔾ₐ` given by a unit `c` of `R`; its `hom` is
  `scaleHom c`.
- `IsRootParametrization.scale`: if `v` is a root parametrization for the exponent vector `m`
  and `c` is a unit, then so is `scaleHom c ≫ v`. The represented subgroup is unchanged
  because `scaleHom c` is an isomorphism, a closed immersion stays one after composing with an
  isomorphism, and equivariance follows from `rootPoint_scaleHom` and commutativity.
- `baseScalar_map` and `baseChangeRoot_scaleHom`: base change to a field `k` with an
  `R`-algebra structure commutes with rescaling,
  `baseChangeRoot k (scaleHom d ≫ v) = scaleHom (algebraMap R k d) ≫ baseChangeRoot k v`.
  `baseChangeRoot` is the base change of root maps from `LocalSplitBigCellProof`.

## Statements (interfaces)

`FieldWeylNormalizationStatement` has these hypotheses:

- `G` is reductive with affine structure morphism;
- the base change of `i` to every residue field is a maximal torus
  (`IsFibrewiseMaximalTorus`);
- `P` is a fibrewise root datum for `(G, i)` (`IsFibrewiseRootDatumOf`);
- `a` is a root, `u` is a root parametrization for `P.root a` and `v` one for
  `P.root (P.reflectionPerm a a) = -P.root a`.

The conclusion: for every field `k` with an `R`-algebra structure, there is a nonzero `d : k`
such that, with `u_k = baseChangeRoot k u`, `v' = scaleHom d ≫ baseChangeRoot k v` and
`i_k = splitTorus.baseChangeHom G I i`,

1. on every test scheme `Z` over `Spec k`, the Library's rank-one relation
   `RootCell.RelationOver i_k a^∨ u_k v' Z` holds, with `a^∨` the cocharacter of
   `P.coroot a`. It says `u_k(X) v'(Y) = v'(Y/w) a^∨(w) u_k(X/w)` whenever `w = 1 + XY` is a
   unit;
2. the point `weylPoint u_k v' = v'(-1) u_k(1) v'(-1)` is a Weyl point for `P.reflection a`
   (`IsWeylPoint`): conjugation by it acts on the torus through the reflection `s_a`.

`LocalWeylNormalizationStatement` has the hypotheses of `LocalSplitRootGroupStatement`:

- `R` is local and reduced;
- `G` is reductive with affine structure morphism;
- `i` is a closed subgroup and is fibrewise a maximal torus;
- `P` is a fibrewise root datum for `(G, i)`, and `b` is a base of `P`.

The conclusion: for every simple root `a ∈ b.support` and every root parametrization `u` for
`P.root a`, there is a root parametrization `v` for `P.root (P.reflectionPerm a a)` such that
`weylPoint u v` is a Weyl point for `P.reflection a`.

The intended use: `LocalWeylNormalizationStatement` together with the existence of root
parametrizations for all roots gives the Library's `LocalSplitSimpleRootGroupStatement`, and
hence the reduced Isomorphism Theorem through
`localSplitReducedIsomorphismTheorem_of_simpleRootGroups`. The field statement is the input
for the ring statement: over `R[ε]`, the `a`-coordinate of `u(1) v(ε)` in the big cell is
`1 - c ε` for some `c` in `R`. On each field fibre the relation forces the image of `c` to be
`1/d`, so `c` is a unit because `R` is local. Then `v = scaleHom c⁻¹ ≫ v_0` works, which can be
checked on field points because `R` is reduced.

## Provenance

Source: Brian Conrad, *Reductive group schemes* (SGA3 summer school notes, 2014),
Cor. 5.1.9 (PDF pp. 140-141). For a root `a`, Conrad pairs `exp_a(X)` with `exp_{-a}` of the
dual section `X^{-1}` and shows that `w_a(X) = exp_a(X) exp_{-a}(-X^{-1}) exp_a(X)` normalizes
`T`, acting as the reflection `s_a` (part 1), with `w_{-a}(X^{-1}) = w_a(X)^{-1}` (part 4).
With `𝔾ₐ`-coordinates, the dual normalization of the pair `(u, v)` is what
`FieldWeylNormalizationStatement` asserts on field fibres. In `SL₂` with `u(X) = [[1, X], [0, 1]]` and `v(Y) = [[1, 0], [Y, 1]]` it
is the relation `u(X) v(Y) = v(Y/w) diag(w, 1/w) u(X/w)` with `w = 1 + XY`, and
`v(-1) u(1) v(-1) = [[0, 1], [-1, 0]]`.

The split of the normalization into a statement on field fibres and a statement over the ring
is internal to this formalization. Conrad proves Cor. 5.1.9 fppf-locally on the base through the
classification of semisimple-rank-one groups (Thm. 5.1.8). The route here instead rescales a
given `exp_{-a}` by a global unit computed in the big cell over `R[ε]`. The hypotheses
`[IsLocalRing R]` and `[IsReduced R]` come from the setting of
`LocalSplitReducedIsomorphismTheoremStatement`.
