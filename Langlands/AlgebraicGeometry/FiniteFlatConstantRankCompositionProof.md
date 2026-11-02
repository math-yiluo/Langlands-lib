# Constant native rank under finite flat composition

The theorem
`Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition.{u}` has full type
`Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionStatement.{u}`.
There are no additional outer hypotheses. It proves that for finite flat maps
`f : X ⟶ Y` and `q : Y ⟶ Z`, with `Z` locally noetherian and constant native
ranks `r` and `s`, the actual composite `f ≫ q` has native rank `r * s`.
The statement pair and its import closure are preserved.

The implemented proof calculates on the actual residue-field fibre at every
point of `Z`. It uses Mathlib's existing local module rank and scheme rank
comparisons throughout. All three helpers are private to this module.

## Restriction of scalars on a fibre

`finrank_restrictScalars_of_constant_rank` considers a field `k`, a
finite-dimensional commutative `k`-algebra `B`, and a finite flat `B`-module
`M`, with its compatible `k`-module structure. If `Module.rankAtStalk M p = r`
for every prime `p` of `B`, it proves

```text
Module.finrank k M = r * Module.finrank k B.
```

If `B` is a subsingleton ring, its unital module `M` is subsingleton too;
both `k`-dimensions are zero. This branch requires no prime of `B` and no
restriction on `r`.

Otherwise `IsArtinianRing.of_finite k B` makes `B` Artinian. Mathlib then
supplies finiteness of its maximal spectrum. For a maximal ideal `P`, the
quotient `B / P` is a field. Apply `Module.rankAtStalk_baseChange` at the
closed point of its spectrum: the rank of `(B / P) ⊗[B] M` equals the rank
of `M` at the image prime, hence equals `r`. Since this quotient module is
a vector space, `Module.rankAtStalk_eq_finrank_of_free` identifies that
rank with its dimension over `B / P`.

Thus the hypotheses of Mathlib's semilocal basis theorem
`Module.nonempty_basis_of_flat_of_finrank_eq` hold. It supplies an actual
basis of `M` over `B` indexed by `Fin r`. The proof infers freeness from
this basis, computes `Module.finrank B M = r`, and applies the free-module
tower law `Module.finrank_mul_finrank k B M`. Commuting the two natural
factors gives the displayed formula. This proves the required restriction
of scalars calculation rather than taking it as an input certificate.

## Native affine rank

`finrank_comp_spec_over_field` applies this calculation to ring maps
`k → B → C` with the corresponding finite flat hypotheses. It uses
`Spec.map_comp` for the actual composite and
`Scheme.Hom.finrank_SpecMap_eq_finrank` for the native rank comparisons.
The `algebraize` tactic introduces the algebra structures induced by these
ring maps, and the proof explicitly verifies their scalar tower. Finiteness
of `C` over `k` follows by transitivity. As `k` is a field, native local
module ranks of `B` and `C` over `k` equal their `k`-dimensions. The preceding
helper therefore yields

```text
(Spec.map f ≫ Spec.map q).finrank z = r * (Spec.map q).finrank z.
```

`finrank_comp_over_field` extends this to arbitrary finite flat scheme maps
`X → Y → Spec k`. Finiteness makes `Y` affine and then makes `X` affine.
The canonical `isoSpec` isomorphisms replace them by the spectra of their
coordinate rings, and `Spec.map_surjective` represents the transported
morphisms by ring maps. Finiteness and flatness pass to these transported
maps. Precomposition by an isomorphism preserves native rank by
`Scheme.Hom.finrank_comp_left_of_isIso`. For postcomposition on `f`, the
proof uses the Cartesian square with the inverse target isomorphism and
`Scheme.Hom.finrank_of_isPullback`. Thus the rank hypothesis on `f` gives
exactly the hypothesis of the affine helper. Cancelling the canonical
isomorphisms gives the same formula for the original field-valued schemes.

## Residue-field base change and the final target

For an arbitrary `z : Z`, set `k = Z.residueField z` and let
`b : Spec k ⟶ Z` be `Z.fromSpecResidueField z`. Form

```text
Y' = Y ×[Z] Spec k,     q' : Y' → Spec k,
X' = X ×[Y] Y',         f' : X' → Y'.
```

These are actual categorical pullbacks. The maps `f'` and `q'` remain
finite flat. `Scheme.Hom.finrank_pullback_snd` transfers the constant rank
`r` from `f` to `f'`. Pasting the two pullback squares vertically gives a
Cartesian square comparing `f' ≫ q'` with the actual composite `f ≫ q`.
Apply the field-valued helper at the closed point of `Spec k`. The same
native rank comparisons identify the two resulting ranks over `k` with
`(f ≫ q).finrank z` and `q.finrank z`. Finally
`Scheme.fromSpecResidueField_apply` identifies the image point with `z`,
and the rank hypothesis on `q` replaces the second rank by `s`.

No nonempty scheme, positive rank, surjective morphism, integral ring,
connectedness condition or chosen basis is assumed. The zero-algebra
branch covers empty intermediate fibres; rank zero over a nonzero fibre
algebra is also allowed by the basis theorem. An empty `Z` has no point
`z`, so the final assertion is vacuous. The locally noetherian hypothesis
remains exactly as in the named Library target. This fibrewise proof does
not need to use it, since it performs the finite-module calculation only
over finite-dimensional algebras over fields.

## Provenance

The geometric convention and composition-stability context are The Stacks
Project Authors, [Section 29.49, tag 02K9](https://stacks.math.columbia.edu/tag/02K9),
Definition 29.49.1 and Lemmas 29.49.2–29.49.3. The registered source is
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`, retained
as `02K9.html` in the literature directory named by the statement Markdown;
its registered folder content SHA256 is
`e416e1999a1cefab5de7c4d444e6a8dfc0a3da10dc3c842df6c57cb15bce8a72`.
Lemma 29.49.3 states stability under composition. Numerical multiplication
is a derived result, implemented here through Mathlib's proved semilocal
basis theorem, tower law and native base-change rank comparisons, without
an explicit decomposition into Artinian local factors. The proof does not
use the parent cohomology theorem or any suspended geometric development.
