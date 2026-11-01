# Full-torus expansion for finite-type Whittaker representations

Author: Worker 78.

`Langlands.whittakerTypeAsymptotic` proves exactly the closed proposition
`Langlands.WhittakerTypeAsymptoticStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.AsymptoticStatement`.
The field and representation-carrier universes are independent. The target
and all its imported Lean/Markdown pairs remain unchanged.

The theorem retains every prime, p-adic field with its canonical topology,
and rank `n+1`, including rank one. The representation is admissible and
finitely generated over its group algebra, and its equivariant-functional
space is nonzero and one-dimensional. Reducible representations are allowed.
The additive character is continuous, nontrivial and unit-norm, with the
actual upper-unitriangular group and entrywise character of the target.

The finite family of continuous translation-finite functions on the full
diagonal torus is chosen before every equivariant functional and vector.
Each coefficient is an actual Schwartz–Bruhat function on the entire
additive `Fⁿ`, and the identity holds at every diagonal tuple, with no
restriction on its central coordinate.

## Implemented proof

The closing theorem applies `WhittakerFullTorus.of_lastEntryOne` to the
published `Langlands.whittakerLastEntryOneAsymptotic`. The latter proves
the entire closed `WhittakerLastEntryOneAsymptoticStatement.{uF,uV}`;
no reduced-expansion premise remains in the present theorem.

The helper module `FullTorusExtension` implements the passage to the full
torus. Divide every diagonal entry by the last entry, preserving all
consecutive-quotient roots and making the normalized last entry one.
Factor the original diagonal matrix as its scalar last entry times this
normalized diagonal matrix.

The published `Whittaker.coefficientCentralCharacter` supplies a single
continuous character `eta` acting on every Whittaker coefficient image.
The helper converts the target's spanning-functional hypothesis into that
theorem's linear-equivalence interface, and evaluates the coefficient law
at the identity to get the functional scalar law. Smoothness is supplied
by admissibility. This introduces no scalar-action hypothesis on the
original carrier and requires no unitary central character.

If `X` is the finite family from the reduced theorem, the full family is
its image under

```text
chi ↦ (a ↦ eta(a_last) * chi(normalize(a))).
```

This choice is made before the functional and vector. Published
`RankinSelberg.finiteFunctionClosure` proves continuity and translation
finiteness using the character, pullback and product clauses. The scalar
law and normalized reduced expansion give the full formula with the same
root-coordinate Schwartz–Bruhat coefficients. When transformed functions
coincide, the helper sums their coefficients over finite fibers. These
sums remain Schwartz–Bruhat, and a fiberwise-sum identity proves equality
without an injectivity assumption. The empty root-coordinate case `n=0`
is included by the same proof.

The paired `FullTorusExtension.md` gives the exact coordinate, topology,
functional-space and finite-sum adapters. Its reduction theorem's only
premise is discharged by the published reduced proof in the closing line.
The scalar coefficient law and finite-function closure are proved imports.
No unproved expansion, operator-span certificate or task status is assumed.

## Sources and derived scope

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212, registered
`jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`:
Proposition (2.2), its proof, Lemma (2.2.1), and Remark (2.2.5), printed
pp.181–183 (PDF14–16), were read during this task. The reduced theorem
implements the function-space expansion and its finite-type extension.
The extension to the full torus through the coefficient-image character
is derived internal reasoning, as explained above; it is not attributed
as a separate full-torus theorem printed in JPS.

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`:
Section 2.5, printed pp.388–389 (PDF23–24), recalls the torus expansion;
printed pp.391–392 (PDF26–27) use it in the analytic argument. These pages
were read during this task. The present theorem supplies the full-torus
finite-type expansion, without claiming the subsequent analytic results.
The checked project literature index and available errata-note locations
contained no source-specific correction for these inputs.
