# Effective descent for a reduced geometric singleton

Authors: Worker 1490 (original proof draft) and Worker 1604 (final module,
proof documentation and submission).

The module `Langlands.AlgebraicGeometry.ReducedGeometricSingleton` proves

```lean
Langlands.AlgebraicGeometry.reducedGeometricSingleton :
  Langlands.AlgebraicGeometry.ReducedGeometricSingletonStatement.{u}
```

It imports the independently published proposition without changing its
Lean or Markdown. For arbitrary fields `K Ω : Type u`, an `Algebra K Ω`
instance, `IsAlgClosed Ω`, and a locally finite type morphism
`f : X ⟶ Spec (CommRingCat.of K)`, the theorem says that reducedness,
nonemptiness and the singleton point property of the actual pullback
`X ×[Spec K] Spec Ω` imply `IsIso f`.

## The algebraically closed case

The helper `algClosedReducedSingleton_isIso` treats the structure morphism
of a reduced nonempty singleton scheme over `Ω` itself. Its underlying
space is irreducible, so reducedness gives `IsIntegral X` by
`isIntegral_of_irreducibleSpace_of_isReduced`. The singleton-affineness
instance in `Mathlib.AlgebraicGeometry.Limits` gives `IsAffine X`.
Then `isField_of_isIntegral_of_subsingleton` makes the actual global section
ring `Γ(X, ⊤)` a field.

The proof uses the ring morphism

```lean
g := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop
```

from `Ω` to `Γ(X, ⊤)`. Naturality of `X.isoSpec` and the canonical
identification of the sections of `Spec Ω` establish

```lean
X.isoSpec.hom ≫ Spec.map g = f
```

Thus it is the given structure morphism whose invertibility will follow.
`HasRingHomProperty.appTop` supplies finite type of `f.appTop`; composing
with the ring isomorphism defining `g` preserves finite type. The
`algebraize` step equips `Γ(X, ⊤)` with the `Ω`-algebra structure induced
by this very ring morphism. Zariski's lemma, as
`finite_of_finite_type_of_isJacobsonRing`, gives
`Module.Finite Ω Γ(X, ⊤)`. This implies integrality, and
`IsAlgClosed.algebraMap_bijective_of_isIntegral` shows that `g` is
bijective. Consequently `g`, its spectrum map, and `f` are isomorphisms.

## Descent to the original field

The helper `reducedGeometricSingleton_isIso` sets

```lean
q := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
```

and proves that this actual field-extension map is flat, surjective and
quasi-compact. Flatness comes from flatness of vector spaces over `K` via
`RingHom.flat_algebraMap_iff` and `HasRingHomProperty.Spec_iff`.
Surjectivity and quasi-compactness are supplied by Mathlib's instances for
this spectrum map.

The second pullback projection `pullback.snd f q` is locally of finite type
by base change. The three geometric hypotheses let the first helper show
that this projection is an isomorphism. Finally,
`MorphismProperty.of_pullback_snd_of_descendsAlong` applies Mathlib's fpqc
descent of isomorphisms, whose instance is
`descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`, to obtain
`IsIso f`. The closing theorem unfolds the published proposition and passes
its ordinary premises to this helper.

## Provenance and scope

This is an internal derived algebraic-geometric proof of the statement
whose source motivation is documented in
[ReducedGeometricSingletonStatement.md](ReducedGeometricSingletonStatement.md).
The implemented argument uses coordinate fields, Zariski's lemma and fpqc
descent; it does not invoke a rational-conjugacy conclusion. The original
Lean proof was supplied by Worker 1490 in the parent task's shared draft
revision 2; the final module preserves that argument and renames its public
descent helper and exact-target wrapper.

The universe `u` is arbitrary. No algebraicity, separability, characteristic,
infinitude or perfectness assumption is added to `K` or `Ω/K`. In particular,
the theorem includes finite and imperfect ground fields. Applications to
Steinberg intersections must separately construct the intersection and prove
local finite type, geometric reducedness, nonemptiness and uniqueness of its
point; this module proves the resulting effective descent step.
