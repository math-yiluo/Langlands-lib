# Canonical base change of group-scheme kernels

For arbitrary schemes `S` and `S'`, any scheme morphism `b : S' ⟶ S`, and any
homomorphism `f : G ⟶ H` between actual group schemes `Grp (Over S)`, this module
constructs the group-object isomorphism

```text
kernelBaseChangeIso b f :
  (Over.pullback b).mapGrp.obj (kernel f) ≅
    kernel ((Over.pullback b).mapGrp.map f).
```

The construction uses the kernel and its point equivalence from
`Langlands.AbelianScheme.Kernel`. All public names are in
`Langlands.GroupScheme`. The base-change functor is Mathlib's actual scheme
pullback, with the cartesian monoidal structure on each slice category.
There are no commutativity, separatedness, flatness, finiteness, or field-base
hypotheses.

## Source and derived provenance

The original source is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary chapters, Definition (3.13) and its continuation,
printed pages 36–37 (PDF pages 40–41), and the base-change paragraph following
Definition (3.1), printed page 29 (PDF page 33). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
available as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
These pages were read directly; no source-specific errata note was present in
the available project notes.

The source defines the kernel by its cartesian square with the target unit,
identifies its points with kernels of group homomorphisms, and describes the
induced group structure under arbitrary base change. The explicit comparison
isomorphism, uniqueness, and compatibility laws here are derived consequences
of these constructions and the pullback universal property, rather than
separately numbered assertions attributed to the source.

## Construction and inclusion

The private helper `baseChange_preservesPullbacks` proves that
`(Over.pullback b).mapGrp` preserves pullbacks. After composing with the
forgetful functor from group objects, it is the composite of that forgetful
functor and `Over.pullback b`. The former creates limits and the latter is a
right adjoint, so the composite preserves pullbacks. Reflection of limits by
the forgetful functor then gives preservation for the group-object functor.

The private `baseChangeTrivialIso` is the strong monoidal functor's unit
comparison, oriented from the base change of the trivial group to the trivial
group over `S'`. Its compatibility with `kernelUnit` follows from uniqueness of
homomorphisms out of the trivial group.

`kernelBaseChangeIso` first uses `PreservesPullback.iso` to compare base change
of the defining pullback with the pullback of the mapped arrows. It then uses
`pullback.map` with identities on the source and target group objects and the
trivial-group comparison on the third vertex. All three maps are isomorphisms,
so the resulting pullback map is an isomorphism in `Grp (Over S')`.

`kernelBaseChangeIso_hom_ι` proves

```text
(kernelBaseChangeIso b f).hom ≫ kernelι ((Over.pullback b).mapGrp.map f) =
  (Over.pullback b).mapGrp.map (kernelι f).
```

This is the first-projection equation of the two pullback comparisons.
`kernelBaseChangeIso_inv_ι` gives the corresponding equation for the inverse.
`kernelBaseChangeIso_hom_unique` proves that any group-object morphism satisfying
the displayed inclusion equation equals the comparison's forward morphism.
The proof forgets to the slice category and cancels its monomorphic kernel
inclusion. Thus compatibility with inclusion characterizes the comparison.

## Points and compatibility

For every `T : Over S'`, `baseChangePointsEquiv b G T` is the multiplicative
equivalence

```text
(T ⟶ ((Over.pullback b).mapGrp.obj G).X) ≃*
  ((Over.map b).obj T ⟶ G.X).
```

Its underlying equivalence is the inverse of `Over.mapPullbackAdj b` on hom
sets. The scheme underlying a point `x` is sent to
`x.left ≫ pullback.fst G.X.hom b`; `baseChangePointsEquiv_left` records this
formula. Multiplication is preserved by the formula for multiplication on the
pullback group object: the two projections of the map into `G ×_S G` are the
projected input points. Pullback extensionality therefore identifies it with
their product. This proof does not commute any factors.

`baseChangePointsEquiv_comp` proves compatibility with every group-object
homomorphism by composition with the pullback projection.
`baseChangePointsEquiv_naturality` proves compatibility with every map of test
schemes `a : T' ⟶ T`, using the map `(Over.map b).map a` after forgetting the
extra base structure.

`baseChangeKernelPointsEquiv b f T` restricts this equivalence to the actual
`MonoidHom.ker` subgroups of the induced group homomorphisms from
`yonedaGrp.map f`. Its source is the pointwise kernel of the base-changed
homomorphism on `T`; its target is the pointwise kernel of `f` on
`(Over.map b).obj T`. Membership follows from compatibility with `f` and
preservation of the identity. The inverse follows from injectivity of the
target point equivalence. The inverse and multiplication laws are inherited
from `baseChangePointsEquiv`.
`baseChangeKernelPointsEquiv_naturality` gives its compatibility with
`kernelPointsRestrict` for every map of test schemes.

Finally, `kernelBaseChangeIso_points` proves the full comparison equation for
every point `x : T ⟶ ((Over.pullback b).mapGrp.obj (kernel f)).X`:

```text
baseChangeKernelPointsEquiv b f T
  (kernelPointsEquiv ((Over.pullback b).mapGrp.map f) T
    (x ≫ (kernelBaseChangeIso b f).hom.hom.hom))
  =
kernelPointsEquiv f ((Over.map b).obj T)
  (baseChangePointsEquiv b (kernel f) T x).
```

Thus the two paths from points of the base-changed kernel to the original
pointwise kernel agree: applying the comparison followed by the new-base
kernel identification, or applying pullback adjunction followed by the
original kernel identification. The proof uses subgroup extensionality,
compatibility of the point equivalence with `kernelι`, and the inclusion law
of `kernelBaseChangeIso`. It applies to every test scheme, not just
field-valued points.
