# Faithfully flat descent of line bundles with trivialized pullback

This module states two propositions about a morphism of schemes
`p : X ⟶ Y` in universe `u` that is affine (`IsAffineHom p`), flat (`Flat p`)
and surjective (`Surjective p`). These are Mathlib's morphism properties. Such a
`p` is quasi-compact, so the single morphism `{p}` is an fpqc covering of `Y`.
Neither proposition assumes finite presentation, finiteness, noetherianity,
reducedness or a section of `p`.

## Shared notation

For a module `M` on `Y`, a trivialization `α : p^* M ≅ O_X` and maps
`a b : U ⟶ X` with `h : a ≫ p = b ≫ p`, the published
`equalCompositeUnitAut p a b h α` (in `EqualCompositePullback`) is the
automorphism of `O_U` given by

```text
O_U ≅ a^* O_X ≅ a^* p^* M ≅ b^* p^* M ≅ b^* O_X ≅ O_U.
```

The outer isomorphisms are the canonical `pullbackUnitIso` identifications. The
next two are the pullbacks of `α⁻¹` and `α`. The middle one is
`equalCompositeIso p a b h M`: the canonical comparison through
`(a ≫ p)^* = (b ≫ p)^*`. The published `structureAutScalar`
(in `StructureUnitScalars`) sends an automorphism of the structure module
`O_U = SheafOfModules.unit U.ringCatSheaf` to its global unit in `Γ(U, ⊤)ˣ`.
`LineBundle Y` is the published full subcategory of module sheaves that are
locally free of rank one in the Zariski sense.

## `UnitCocycleDescentUniquenessStatement`

```text
∀ (X Y : Scheme.{u}) (p : X ⟶ Y), IsAffineHom p → Flat p → Surjective p →
  ∀ (L L' : LineBundle Y)
    (α : p^* L.obj ≅ O_X) (α' : p^* L'.obj ≅ O_X),
    (∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      structureAutScalar (equalCompositeUnitAut p a b h α) =
        structureAutScalar (equalCompositeUnitAut p a b h α')) →
    Nonempty (L ≅ L')
```

In Lean, `p^*` is `Scheme.Modules.pullback p` and `O_X` is
`SheafOfModules.unit X.ringCatSheaf`. In words: suppose two line bundles on `Y`
have trivialized pullbacks, and the two trivializations give the same scalar
on every pair of maps with equal composite to `Y`. Then the two line bundles are
isomorphic. The conclusion asks only for some isomorphism in `LineBundle Y`, an
isomorphism of the underlying module sheaves. It does not ask that the
isomorphism be compatible with `α` and `α'`.

## `UnitCocycleDescentEffectiveStatement`

```text
∀ (X Y : Scheme.{u}) (p : X ⟶ Y), IsAffineHom p → Flat p → Surjective p →
  ∀ (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ),
    (∀ (U V : Scheme.{u}) (q : V ⟶ U) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
        (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p),
      c V (q ≫ a) (q ≫ b) h' = Units.map q.appTop.hom.toMonoidHom (c U a b h)) →
    (∀ (U : Scheme.{u}) (a b d : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = d ≫ p)
        (h'' : a ≫ p = d ≫ p),
      c U a b h * c U b d h' = c U a d h'') →
    ∃ (L : LineBundle Y) (α : p^* L.obj ≅ O_X),
      ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
        structureAutScalar (equalCompositeUnitAut p a b h α) = c U a b h
```

The family `c` assigns a global unit on `U` to every scheme `U` in universe `u`
and every pair `a b : U ⟶ X` with equal composite to `Y`. It must satisfy two
conditions:

- Naturality: precomposing a pair with `q : V ⟶ U` pulls the unit back along
  `q.appTop : Γ(U, ⊤) ⟶ Γ(V, ⊤)`.
- Multiplicativity along triples `a, b, d`.

The conclusion is that some actual line bundle `L` on `Y` and some
trivialization `α` of its pullback have exactly these comparison scalars, on
every pair.

The published library already shows that comparison scalars satisfy both
conditions. Naturality follows from `equalCompositeUnitAut_precomp` and
`structureAutScalar_pullback`; multiplicativity follows from
`equalCompositeUnitAut_trans` and `structureAutScalar_trans`. So these are the
only constraints such a family can satisfy, and the effective statement says
that every family satisfying them arises this way.

## `UnitCocycleDescentStatements`

The entry proposition is the conjunction

```text
UnitCocycleDescentUniquenessStatement.{u} ∧ UnitCocycleDescentEffectiveStatement.{u}.
```

The two halves are separate obligations and may be proved separately.

## Relation to descent data

Let `pr₁ pr₂ : X ×_Y X ⟶ X` be the projections. By naturality, a family `c` as
above is determined by the single unit `u := c (X ×_Y X) pr₁ pr₂ _`, because
every pair `(a, b)` factors through `(pr₁, pr₂)` by `pullback.lift a b h`. The
multiplicativity condition, applied to the three projections of
`X ×_Y X ×_Y X`, is the cocycle identity for `u`. Multiplication by `u`
therefore defines a descent datum on `O_X` for the covering `{p}`. Conversely,
for a quasi-coherent `M` with a trivialization `α`, the canonical descent datum
on `p^* M` becomes, after transport through `α`, multiplication by the scalar
at `(pr₁, pr₂)`.

So, for line bundles with trivialized pullback, the two statements are the
effectivity and full faithfulness of descent along `{p}`.

## Sources and provenance

These are derived statements. They specialize fpqc descent of quasi-coherent
sheaves to the trivial module `O_X` with its descent data written as unit
cocycles:

- The Stacks Project, *Descent* (version ed88ff78), Proposition 5.2
  (Tag 023T), PDF p.18. For an fpqc covering, every descent datum on
  quasi-coherent sheaves is effective, and the functor from quasi-coherent
  sheaves to descent data is fully faithful. The affine case is Proposition
  3.9 (Tag 023N), PDF p.8.
- The same chapter, Lemma 7.6 (Tag 05B2), PDF p.22. A quasi-coherent sheaf
  whose pullback to an fpqc covering is finite locally free is finite locally
  free. Here the pullback is `O_X`, and `p` is surjective, so the descended
  sheaf has rank one everywhere. That makes it Zariski locally isomorphic to
  `O_Y`, i.e. an object of `LineBundle Y`.
- Edixhoven, van der Geer and Moonen, *Abelian Varieties* (preliminary
  version), Chapter VII, (7.2) and (7.3), printed pp.98–99 (PDF pp.102–103).
  This gives the application to quotients by group actions. There, liftings of
  an action to `O_X`, i.e. descent data on `O_X`, are described by unit-valued
  cocycles, and Proposition (7.2) is the descent of finite locally free modules
  along the quotient map.

The "all pairs" formulation is used because the published
`equalCompositeUnitAut` and `structureAutScalar` are stated for arbitrary pairs.
Downstream consumers can then compute scalars directly on kernel translations
of abelian-scheme families, without first identifying `X ×_Y X`.

## Proof obligations

This file supplies proposition definitions only. Separate proofs must establish
module-level faithfully flat descent along `p`, together with the comparison
between the scalar conditions above and descent data. No proof hole or
assumption is introduced here.
