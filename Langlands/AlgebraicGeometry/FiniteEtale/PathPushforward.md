# Pushforward of actual finite étale paths

Author: Worker 142.

This module pushes a given isomorphism of actual finite geometric-fibre functors
along an arbitrary scheme morphism. It uses the published finite étale pullback
functor and its canonical fibre comparisons. It proves the evaluation,
concatenation, reversal and loop formulas, a characterization using morphisms
of covers over the base morphism, and compatibility of fundamental-group
pushforward with path conjugation.

## Source and derived provenance

The conventions are those of Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary version built 2012-02-08, Chapter X §3, Definitions (10.25)–(10.26),
printed p.150 / PDF p.154, and (10.29)–(10.30), printed p.151 / PDF p.155.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The cited original passages were read. No corresponding source errata note
is present in the current Library.

The source defines finite étale covers and their geometric-fibre functors,
explains change of point using possibly different algebraically closed fields,
and induces a fundamental-group map by pullback of covers. This module is a
**derived** extension of the published `FiniteEtale.Pullback` construction:
whiskering an existing path by pullback and conjugating by the actual fibre
comparisons produces the pushed path. The source is cited for these geometric
conventions, not as printing these exact formulas or their more general
conditional hypotheses. The proofs below follow categorical composition,
pullback uniqueness and naturality.

## Inputs and construction

Let `b : S' ⟶ S` be a morphism in `Scheme.{u}`. Let `s : Spec Ω ⟶ S'` and
`t : Spec Ω' ⟶ S'` be field-valued points, with the fields in the same universe.
Their finite-fibre hypotheses are

```lean
hs : ∀ Y : Cover S', Finite (Fiber s Y)
ht : ∀ Y : Cover S', Finite (Fiber t Y)
```

and `hsb`, `htb` are the analogous hypotheses for `s ≫ b`, `t ≫ b` on `S`.
They retain the existing finite-set packaging; no Galois-category hypothesis
is introduced. The input path is exactly

```lean
p : fiberFunctor s hs ≅ fiberFunctor t ht
```

on the actual finite étale covers. If `e_s` and `e_t` are the published
`fiberFunctorPullbackIso` comparisons at these points, the definition is

```text
pathPushforward b hsb htb p =
  e_s ≪≫ Functor.isoWhiskerLeft (pullbackFunctor b) p ≪≫ e_t.symm.
```

Thus a lift `x` into a cover `Y` of `S` is pulled back to `Y ×_S S'`, acted on
by `p` there, and projected to `Y`. This constructs the output path from `b`
and `p`; it does not request a replacement path as additional data.

No connectedness, local noetherianity or algebraic closure is needed for this
conditional construction. Those conditions belong to geometric existence and
classification results. No path-existence theorem is asserted here. The two
endpoint fields may differ, and a third field is allowed for concatenation.

## Evaluation and path laws

`pathPushforward_apply` is the defining evaluation formula through
`pullbackFiberEquiv` and its inverse. `pathPushforward_apply_left` expresses
the resulting scheme morphism as the transported lift followed by
`pullback.fst Y.obj.hom b`. Both are definitional equalities.

`pullbackFiberEquiv_pathPushforward` states that the canonical endpoint fibre
bijections intertwine `p` and its pushforward. Its proof cancels the inverse
fibre bijection in the evaluation formula.

`pathPushforward_refl` proves preservation of the constant path.
`pathPushforward_trans` proves

```text
b_*(p ≪≫ q) = b_*p ≪≫ b_*q,
```

where `p ≪≫ q` means first `p`, then `q`, and all three finite-fibre witnesses
on `S` are explicit. `pathPushforward_symm` proves preservation of reversal.
The proofs use whiskering of identity, composition and reversal and cancel
adjacent fibre comparisons. These laws concern the input paths for a fixed
`b`; they are not assertions about successive scheme morphisms.

For a loop `g`, `pathPushforward_aut` identifies the pushed path with the
already defined `fundamentalGroupMap b s (s ≫ b) rfl hs hsb g`. It is exactly
the same conjugation of the pullback whiskering, with the orientation retained.

## Characterization by compatible cover morphisms

`pathPushforward_apply_left_of_comp` takes covers `Y` over `S`, `Y'` over `S'`,
a morphism `φ : Y'.obj.left ⟶ Y.obj.left` over `b`, and lifts `y` at `s` and
`x` at `s ≫ b` satisfying `y.left ≫ φ = x.left`. It proves

```text
(b_*p(x)).left = (p(y)).left ≫ φ.
```

Here being over `b` is exactly
`φ ≫ Y.obj.hom = Y'.obj.hom ≫ b`. The proof constructs the actual morphism
`Y' → Y ×_S S'` using the universal property of the pullback. Its composite
with `y` equals the pulled-back lift of `x`, by the two projections. Naturality
of `p.hom` for this cover morphism gives the claim after projection. This
characterization also applies when `φ` is not an isomorphism.

## Fundamental-group conjugation square

`fundamentalGroupMap_path_conjugation` proves, for `g ∈ π₁(S',s)`,

```text
b_*(Aut.autMulEquivOfIso p g) =
  Aut.autMulEquivOfIso (b_*p) (b_*g).
```

The left side uses the existing map at `t`, and the right side the existing
map at `s`. In function notation, path conjugation is `g ↦ p ∘ g ∘ p⁻¹`.
The proof expands the published fundamental-group map and the path
pushforward, applies isomorphism extensionality, and cancels consecutive
comparison morphisms. The groups and their actions remain the actual
finite-fibre-functor automorphism groups. No new monodromy action, Tate module,
Weil pairing or assertion of unpointed independence is introduced in this unit.
