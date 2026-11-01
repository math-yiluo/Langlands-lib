# Proof of Renard A.III.3: object and functor isomorphism principles

The theorem
`Langlands.Renard.IsomorphismPrinciple.isomorphismPrincipleStatements`
proves exactly the published closed proposition
`Langlands.Renard.IsomorphismPrinciple.IsomorphismPrincipleStatements`,
imported from
`Langlands.CategoryTheory.Renard.IsomorphismPrincipleStatements`.
Its four universe parameters `vC`, `vM`, `uC`, `uM` remain independent.
The proof preserves the conjunction order: the object principle followed by
the functor principle. Every mathematical input is bound inside the imported
statement; the theorem has no additional hypothesis.

## Source and provenance

The source assertion is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.3, printed p.255 /
one-based PDF261, displays (A.III.3.1) and (A.III.3.2). Registered identifier:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read directly for this proof. As explained in the imported
statement's Markdown, both displayed Hom subscripts are printed C, although
the displayed objects and the surrounding prose put those Hom sets in M.
The proof uses exactly the published interpretation in M.

The supplementary older-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. Those two pages give no correction to this proposition
or its Hom subscripts. This observation concerns only the cited pages.

The implemented route uses Mathlib's actual categorical constructions
`CategoryTheory.Yoneda.ext` and `CategoryTheory.NatIso.ofComponents`, at the
project's Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The helper and the naturality calculation below are the present implementation
of the source assertion; they do not assert that the book prints this proof.

## Object principle

The private helper `isoOfHomEquiv` takes the given equivalences
`e Z : (Z ⟶ X) ≃ (Z ⟶ Y)` and their precomposition naturality. It passes their
forward maps, inverse maps, and two inverse identities to `Yoneda.ext`.
The required forward naturality is precisely the supplied equation

```text
e Z' (g ≫ f) = g ≫ e Z f.
```

Mathlib constructs an isomorphism of represented Hom functors and takes its
preimage under the fully faithful Yoneda embedding, producing an actual
`X ≅ Y`. Its forward morphism is definitionally `e X (𝟙 X)`.
The theorem `objectStatement` places this isomorphism in `Nonempty`.
No naturality of the inverse equivalences is added as an assumption.

## Functor principle

For each source object X, the same helper applied to `e X` and test-object
naturality `hZ X` gives an actual component isomorphism
`i X : F.obj X ≅ G.obj X`. Its forward morphism is

```text
α_X = e X (F.obj X) (𝟙 (F.obj X)).
```

For a source morphism `a : X ⟶ X'`, test-object naturality, applied to
`g = F.map a` and the identity of `F.obj X'`, gives

```text
F.map a ≫ α_X' = e X' (F.obj X) (F.map a).
```

Source-object naturality `hX`, applied to a and the identity of `F.obj X`,
then gives

```text
e X' (F.obj X) (F.map a) = α_X ≫ G.map a.
```

These two equalities prove exactly the naturality condition required by
`NatIso.ofComponents`. That construction supplies the natural inverse from
the component inverses and their isomorphism identities. The theorem
`functorStatement` therefore produces `Nonempty (F ≅ G)` in the actual
functor category, using both published naturality hypotheses.

## Aggregate and scope

The exported theorem `isomorphismPrincipleStatements` is the conjunction of
`objectStatement.{vM,uM}` and `functorStatement.{vC,vM,uC,uM}` at the exact
imported target. The proof needs arbitrary actual categories and functors only;
it imposes no smallness, nonemptiness, additive or finiteness restriction.
The statement pair and imported dependencies are unchanged.

This proof covers exactly the two A.III.3 clauses. Representability in A.III.2,
adjunctions, other Appendix A assertions and the remaining whole-book
obligations are outside its scope.
