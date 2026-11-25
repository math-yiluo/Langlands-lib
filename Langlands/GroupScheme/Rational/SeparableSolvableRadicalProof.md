# Solvable radicals under separable algebraic extension: proof

The theorem `Langlands.GroupScheme.separableAlgebraicSolvableRadical` proves the
unchanged published proposition
`Langlands.GroupScheme.SeparableAlgebraicSolvableRadicalStatement.{u}`
(module `Langlands.GroupScheme.Rational.SeparableSolvableRadicalStatement`) at an
arbitrary universe `u`, with no added hypothesis. The module also proves two
auxiliary theorems in the namespace `Langlands.GroupScheme.SeparableSolvableRadical`.
It uses the helper module `Langlands.GroupScheme.Rational.SolvableRadicalBaseChange`,
submitted with it, for the transport and reflection lemmas about
`IsSolvableRadical`.

The proof has the same structure as the published proof of the unipotent
analogue, `separableAlgebraicUnipotentRadical`
(`Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof`). The Galois
descent step uses the Library's general theorem for Galois-invariant closed
subgroups, `Descent.GaloisInvariantClosedSubgroup.exists_descent`.

Throughout, `k` is a field, `G` is a group scheme over `Spec k` with instances
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, and
`r : R ⟶ G` satisfies `IsSolvableRadical r`. For a field extension `k → L`, the
base change of `r` is
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map r`,
written `r_L`.

## Step 1: Galois extensions of any degree

`SeparableSolvableRadical.isSolvableRadical_baseChange_galois`: if `[IsGalois k L]`
(no finiteness assumed), then `r_L` is a solvable radical of `G_L` in the sense of
`IsSolvableRadical`.

Proof as implemented. Write `c : Spec L ⟶ Spec k`.

1. `G_L` is smooth and affine over `L` (pullback instances, after unfolding its
   structure map to `pullback.snd G.X.hom c`) and connected
   (`connectedSpace_baseChange_of_smooth_affine`). So `solvableRadicalExistence`
   gives a solvable radical `r' : R' ⟶ G_L` over `L`.
2. For every `σ : L ≃ₐ[k] L`, the Galois translate `radicalGaloisHom r' σ` has the
   same image as `r'` (`IsSolvableRadical.range_galoisTransport`, from the helper
   module). Since `r'` is a closed subgroup,
   `Descent.GaloisInvariantClosedSubgroup.exists_descent` yields a `k`-group `R₀`, a
   closed subgroup `j : R₀ ⟶ G` and an isomorphism `e : (R₀)_L ≅ R'` with
   `j_L = e.hom ≫ r'`.
3. `j` is a solvable radical over `k`: `j_L = e.hom ≫ r'` is a solvable radical over
   `L` (`IsSolvableRadical.precomp_iso`), and `IsSolvableRadical.of_baseChange`
   (helper module) reflects this along `k → L`, because `j` is closed.
4. `r` and `j` are both solvable radicals of `G`, so
   `IsSolvableRadical.iso` gives `f : R ≅ R₀` with `f.hom ≫ j = r`
   (`IsSolvableRadical.iso_hom_comp`, from
   `Langlands.GroupScheme.Rational.SolvableRadicalComparison`).
5. Hence `r_L = (f_L).hom ≫ j_L = (f_L ≪≫ e).hom ≫ r'`, by functoriality of base
   change and step 2. By `IsSolvableRadical.precomp_iso` this is a solvable radical
   over `L`.

## Step 2: separable algebraic extensions

`SeparableSolvableRadical.isSolvableRadical_baseChange`: if
`[Algebra.IsSeparable k K]`, then `r_K` is a solvable radical of `G_K`.

Proof as implemented. Let `L = SeparableClosure k`. Mathlib's `IsSepClosed.lift`
gives a `k`-algebra map `ι : K →ₐ[k] L`; give `L` the `K`-algebra structure
`ι.toRingHom.toAlgebra` (the `k`-algebra structure on `L` is Mathlib's own). Write
`b : Spec K ⟶ Spec k`, `d : Spec L ⟶ Spec K` and `c : Spec L ⟶ Spec k` for the
induced morphisms. Then `d ≫ b = c`, by `Spec.map_comp`,
`CommRingCat.ofHom_comp` and `ι.commutes`.

1. `L/k` is Galois (Mathlib's instance for a separable closure), so Step 1 shows
   that `(baseChange c).map r` is a solvable radical over `L`. Rewriting with
   `d ≫ b = c`, so is `(baseChange (d ≫ b)).map r`.
2. The naturality square `baseChangeCompIso_hom_naturality b d r` gives
   `(baseChange d).map ((baseChange b).map r) =
   (baseChangeCompIso b d R).symm.hom ≫ (baseChange (d ≫ b)).map r ≫
   (baseChangeCompIso b d G).hom`. The right side is a solvable radical over `L` by
   `IsSolvableRadical.comp_iso` (ambient isomorphism) followed by
   `IsSolvableRadical.precomp_iso` (source isomorphism).
3. So the base change along `K → L` of `r_K` is a solvable radical over `L`. `G_K`
   is affine over `K`, and `r_K` is a closed subgroup (`IsClosedSubgroup.baseChange`).
   Therefore `IsSolvableRadical.of_baseChange`, applied to the extension `K → L`,
   shows that `r_K` is a solvable radical of `G_K` over `K`.

## Step 3: the main theorem

`separableAlgebraicSolvableRadical` introduces `k`, `K`, the algebra and
separability instances, `G`, the three hypotheses `Smooth G.X.hom`,
`IsAffineHom G.X.hom`, `ConnectedSpace G.X.left`, and `r` with
`IsSolvableRadical r`. It installs the three hypotheses as local instances and
applies Step 2.

## Published inputs used

| Lean name | Module |
| --- | --- |
| `SeparableAlgebraicSolvableRadicalStatement` (target) | `Langlands.GroupScheme.Rational.SeparableSolvableRadicalStatement` |
| `IsSolvableRadical` | `Langlands.GroupScheme.Rational.LeviSubgroup` |
| `IsSolvableRadical.iso`, `IsSolvableRadical.iso_hom_comp` | `Langlands.GroupScheme.Rational.SolvableRadicalComparison` |
| `solvableRadicalExistence` | `Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof` |
| `Descent.GaloisInvariantClosedSubgroup.exists_descent` | `Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups` |
| `baseChangeCompIso_hom_naturality` | `Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction` |
| `baseChangeCompIso` | `Langlands.AbelianScheme.Tate.BaseChangeCoherence` |
| `IsClosedSubgroup.baseChange` | `Langlands.GroupScheme.SubgroupBaseChange` |
| `connectedSpace_baseChange_of_smooth_affine` | `Langlands.GroupScheme.GeometricConnectedness` |
| `algebraBaseMap` (an abbreviation, used in a `change`) | `Langlands.GroupScheme.Torus.LatticeGalois` |

From the helper module `Langlands.GroupScheme.Rational.SolvableRadicalBaseChange`:
`IsSolvableRadical.comp_iso`, `IsSolvableRadical.precomp_iso`,
`IsSolvableRadical.range_galoisTransport` and `IsSolvableRadical.of_baseChange`.

From Mathlib: `SeparableClosure`, `IsSepClosed.lift`, the `IsGalois` instance for a
separable closure, `Spec.map_comp` and `CommRingCat.ofHom_comp`.

The module sets `backward.isDefEq.respectTransparency false` and
`maxHeartbeats 800000`, as do the imported modules it relies on. The development
check reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is an internal deduction from the published results listed above and the
helper module. It changes neither the statement's Lean/Markdown pair nor anything
it imports.

The target derives from J. S. Milne, *Algebraic Groups* (2017), Proposition 19.1,
printed p. 397 (PDF p. 413), registered as `milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Milne treats a
Galois extension by descending `R(G_{k'})`, which is Galois-stable by uniqueness,
to a subgroup variety `H` of `G` (1.54) and using maximality to get `R(G) = H`.
Step 1 follows this argument. It uses the Library's descent theorem for
Galois-invariant closed subgroups (valid for Galois extensions of any degree, as
1.54(b) allows) and the uniqueness of radical images. Milne's printed proof
reduces to Galois extensions through the inclusion `R(G)_{k'} ⊆ R(G_{k'})`.
Step 2 instead reduces a separable algebraic `K/k` to a separable closure `L` of
`k`, as the statement's Markdown suggests ("For the later proof"). Where that note
compares `R(G)_K` and `R(G_K)` through the uniqueness of descent (1.54(a)), Step 2
reflects the radical predicate along `K → L` (`IsSolvableRadical.of_baseChange`).
