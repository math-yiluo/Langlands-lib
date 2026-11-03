# Coefficient naturality of actual abelian-sheaf cohomology comparisons

Worker 368. This internal companion proves coefficient naturality of the
existing `AbelianSheafDerivedSections.HAddEquiv`. The topological space
`X : TopCat.{u}`, the abelian sheaves with section groups in universe `u`,
their morphism `f : F ⟶ G`, and the degree `n : ℕ` are arbitrary.
There is no separation, finiteness or geometric hypothesis.

All declarations are in
`Langlands.Cohomology.AbelianSheafDerivedSections`.
The source is Mathlib's actual `Sheaf.H.{u} F n`, defined as Ext from
the constant sheaf `ULift.{u} ℤ`. Its actual coefficient map is
`Sheaf.H.map f n`, which sends `a` to
`a.comp (Ext.mk₀ f) (add_zero n)`. The target is the existing
right-derived global-sections functor on the same sheaf category,
with its actual functor map.

`HAddEquiv_naturality X f n a` proves

```text
HAddEquiv X G n (Sheaf.H.map f n a)
  = ((globalSections X).rightDerived n).map f (HAddEquiv X F n a).
```

The equivalence here is the published one, without any change of
components or normalization. Its first factor is the existing
`ExtRightDerived.extAddEquivRightDerived (constantIntegers X) F n`;
its second is the component of `homRightDerivedIso X n`.
The proof expands precisely this composite, applies the published
`extAddEquivRightDerived_naturality` to the first factor, and evaluates
the naturality equation of `homRightDerivedIso` on the resulting element.

`HAddEquiv_symm_naturality X f n a` proves the inverse equation

```text
(HAddEquiv X G n).symm (((globalSections X).rightDerived n).map f a)
  = Sheaf.H.map f n ((HAddEquiv X F n).symm a).
```

It follows by applying the injective forward equivalence, using forward
naturality and cancelling each equivalence with its inverse.
Both equations include degree zero and every positive degree.

`HNatIso X n` assembles these same components into a natural isomorphism

```text
Sheaf.functorH (Opens.grothendieckTopology X) n
  ≅ (globalSections X).rightDerived n.
```

Both functors take values in `AddCommGrpCat.{u}`. The isomorphism is
constructed with `NatIso.ofComponents` and the proved forward equation.
`HNatIso_app` identifies its component at `F` with
`(HAddEquiv X F n).toAddCommGrpIso` by reflexive equality.

The provenance is an internal composition of the published
`AbelianSheafDerivedSections` and `ExtRightDerivedNaturality` constructions.
Mathlib's pinned `CategoryTheory/Sites/SheafCohomology/Basic.lean` supplies
the source, its coefficient maps and the actual `functorH`.
No new external theorem or additional axiom is assumed.
Scheme base change, compatibility with connecting homomorphisms,
module scalar actions and Picard representability remain separate
obligations.
