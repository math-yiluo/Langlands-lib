# Trivial families and preservation of the dual origin

`homFamilyPullbackTrivialIso f T` specializes the actual comparison
of `RigidifiedTrivialPullback` to the commuting unit-section square
of an abelian-scheme homomorphism `f : A ⟶ B`. It gives an actual
rigidified isomorphism between the pulled-back trivial family on
`T ×_S B` and the trivial family on `T ×_S A`.
`homClassesPullback_trivial` descends this isomorphism to the
quotient of rigidified families. Under the explicit
`HomPicardZeroPullbackStatement` premise,
`homPicardZeroClassesPullback_trivial` gives the same equality in
the geometric Picard-zero subtype by subtype extensionality.

`picardZeroClassesPullback_trivial` proves the corresponding
parameter-pullback equality under the explicit
`PicardZeroPullbackStatement` premise. It again uses the actual
rigidified comparison, quotient equality and subtype
extensionality. Consequently `dualClassify_trivial` identifies the
classifier of the trivial family over any test scheme `T` with the
structure map `T ⟶ S` followed by `dualOrigin`. Its proof applies
the previously constructed classifier's pullback law and the
trivial-class equality, supplying the proved
`RigidifiedModule.pullbackCoherence`.

Finally, for chosen universal families `hA : HasDualScheme A` and
`hB : HasDualScheme B`, `dualSchemeMap_origin` proves

```text
dualOrigin B hB ≫ dualSchemeMap preservation f hA hB = dualOrigin A hA.
```

The proof applies the universal action of `dualSchemeMap` to the
trivial class over the base scheme, substitutes preservation of
that class, and reverses the resulting equality. Coherence is
supplied by the existing theorem; the remaining explicit
hypotheses are the two dual-existence propositions and
`HomPicardZeroPullbackStatement`. Parameter-pullback stability is
not a hypothesis of this last equality.

## Provenance and scope

This is derived from the actual rigidified pullback and universal
classification described in Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, paragraph (6.2), printed
p.88 (PDF p.92), and the actual dual-map construction already
specified in `DualSchemeMap`. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The comparison with the trivial rigidification is implemented by
the companion module, rather than imported as a source theorem.
All schemes and bundle isomorphisms are the existing actual ones.

These results hold over arbitrary bases with the stated premises.
They establish preservation of the distinguished section of the
chosen parameter scheme. They do not yet equip it with a group
law, prove it abelian, prove dual existence, or prove additivity
of the dual-map construction.
