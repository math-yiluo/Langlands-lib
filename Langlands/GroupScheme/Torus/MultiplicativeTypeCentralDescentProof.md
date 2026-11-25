# Proof: descent of central homomorphisms from groups of multiplicative type

This module proves the published statement
[`MultiplicativeTypeCentralDescentStatement`](MultiplicativeTypeCentralDescentStatement.md),
which is SGA 3, Exposé IX, Corollaire 5.4:

```lean
theorem multiplicativeTypeCentralDescent : MultiplicativeTypeCentralDescentStatement.{u}
```

in the namespace `Langlands.GroupScheme`, for every universe `u`, with no extra hypotheses.

Let `H` be an `S`-group of multiplicative type, and `G` a separated `S`-group that is locally
of finite presentation and quasi-compact. Let `π : S' ⟶ S` be either flat, quasi-compact and
surjective, or have a section, and have connected geometric fibres. Then every central
homomorphism `u' : H_{S'} ⟶ G_{S'}` is the base change of exactly one homomorphism
`u : H ⟶ G`.

## Proof

The proof is one line. It applies two results:

- `MultiplicativeTypeCentralDescent.descent_of_rigidity`, from the companion module
  [`MultiplicativeTypeCentralDescentReduction`](MultiplicativeTypeCentralDescentReduction.md).
  It proves `MultiplicativeTypeCentralRigidityStatement.{u} →
  MultiplicativeTypeCentralDescentStatement.{u}`, and that Markdown file explains the full
  argument. In outline: compare the two pullbacks `u''₁`, `u''₂` of `u'` to
  `S'' = S' ×_S S'` through their quotient `w = u''₁ · u''₂⁻¹`, which is a homomorphism because
  both are central. Rigidity (part 3) shows that the locus where `w` is trivial is open and
  closed. It contains the diagonal, so connectedness of the geometric fibres makes it all of
  `S''`. Hence `u''₁ = u''₂`, so `u'` is constant on the fibres of `H_{S'} ⟶ H`. Then `u'`
  descends along this effective epimorphism, either fpqc or split. Faithfulness of pullback
  along `π` gives that the descended map is a homomorphism and that it is unique.
- `multiplicativeTypeCentralRigidity`, the Library's published proof of
  [`MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md)
  (SGA 3, IX, 5.1–5.3), in the module `Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityProof`.

The route is SGA 3's proof of 5.4: p.50 of the Gille–Polo edition registered as
`sga3-expose-ix-gille-polo-2009`, which deduces 5.4 from 5.3. The descent step is carried out
directly for an effective epimorphism, not through SGA 3, IV 2.3.

The module compiles with no errors or warnings. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
