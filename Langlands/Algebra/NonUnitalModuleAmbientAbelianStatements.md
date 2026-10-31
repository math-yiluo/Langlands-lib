# Ambient abelianness of original additive nonunital modules

Workers 6 and 633. Worker 6 prepared the shared draft; Worker 633 checked the
original passages, current corrections and complete Lean interface. This is an
internal derived statement of ambient abelianness for the published category of all original additive
nonunital actions, with its already published pointwise Hom groups.
The statement has no proof here and constructs no `Abelian` instance.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant original passages are the conventions at printed pages 5–6 /
PDF pages 11–12, I.1.2 printed page 7 / PDF page 13, A.VI.1 printed page 261 /
PDF page 267, and A.VI.2 property 6 printed page 262 / PDF page 268.
These passages were read directly. The supplementary 2010 errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF pages 18–19. The
[author's book and errata section](https://perso.pages.math.cnrs.fr/users/david.renard/)
was checked live on 30 October 2026: it is byte-identical to the registered
`renard-author-page-2026-10-26` snapshot. It links the corrected 2026 French
edition and separate 2010 errata; no separate 2026 errata link appears in that
section. The linked 2010 errata retain their registered fingerprint. These
older corrections do not replace the governing 2026 original.

The conventions permit nonunital rings and actions without a unit law even when the ring is unital. A.VI.1 lists the
ambient module category among the motivating abelian categories; property 6
describes the additive Hom groups and distributive composition.

The explicit existential formulation, equality of structures, and
integer-unitization implementation route are internal derived content. The
statement does not use the source's insufficient full-subcategory criterion.
The discrepancy and the need for finite-product closure are explained in the
current Library note `notes/renard/appendix-a-corrections.md`. The nondegenerate
subcategory in I.1.2 remains a separate obligation.

The complete target is

```lean
Langlands.Algebra.NonUnitalModuleAmbientAbelianStatement.{uA, uM} : Prop
```

Its body is

```lean
∀ (A : Type uA) [NonUnitalRing A],
  ∃ h : CategoryTheory.Abelian
      (Langlands.Algebra.NonUnitalModuleCat.{uA, uM} A),
    h.toPreadditive =
      Langlands.Algebra.NonUnitalModuleCat.preadditive.{uA, uM} A
```

The only quantified input is the arbitrary acting ring with its given
`NonUnitalRing` structure. The original objects, actions, morphisms, identity
and composition are those of `NonUnitalModuleCat`; they are not replaced.
The equality refers to the exact named pointwise `Preadditive` structure
imported from `Langlands.Algebra.NonUnitalModuleAdditive`. Since Mathlib's
`Abelian` is data containing a preadditive structure, existence alone would
not specify this agreement. No `Abelian`, `Preadditive`, finite-product
structure or categorical kernel/cokernel is taken as a hypothesis.

The acting-ring universe `uA` and carrier universe `uM` are independent.
The statement includes both unequal cases `(uA,uM) = (0,1)` and `(1,0)`,
without replacing carriers by types in `max uA uM`. It permits the zero ring,
zero carriers, and zero original actions on nonzero additive groups, including
over unital rings. There is no scalar field, idempotentedness, nondegeneracy,
nontriviality or finiteness assumption.

The published integer-unitization equivalence offers a route for a later
proof: transfer ordinary module-category abelianness while retaining the
published pointwise preadditive structure and finite products. This file
neither carries out nor assumes that transfer. A separate proof unit must
prove this exact public statement and supply the corresponding named
`Abelian` structure. Concrete kernel/cokernel formulas and selected-map
comparisons, images/coimages and exactness comparisons, nondegenerate closure
and abelianness, part-functor exactness, and complex-linear or tensor
comparisons remain separate obligations.
