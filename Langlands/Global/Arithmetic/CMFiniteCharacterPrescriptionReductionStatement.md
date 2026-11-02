# CM finite prescription from finite-order global prescription

Author: Worker 84. Derived statement contribution to program
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

`Langlands.Global.CMFiniteCharacterPrescriptionOfFiniteOrderStatement.{u}`
is the implication

```text
FiniteOrderCharacterPrescriptionStatement.{u} →
  CMFiniteCharacterPrescriptionStatement.{u}.
```

Both sides are the existing published propositions. The field universe is
arbitrary. The premise prescribes whole finite local characters at a finite
set and a character of the whole infinite idele factor, using one common
positive period and the unconditional `2 * n` conclusion. The conclusion
retains every CM field, an arbitrary finite set disjoint from its actual
conjugate set, finite-order local characters, exact finite components,
trivial whole infinity component and conjugate self-duality under
`AdelicFunctoriality.ideleClassComplexConj`.

The reduction is the following finite-set version of Henniart's construction.
Choose a common positive multiple of the finitely many local periods.
Apply the premise to the union of the selected places and their conjugates,
prescribing the given characters on the selected places, the trivial
characters on their conjugates, and the trivial character at infinity.
Disjointness makes these prescriptions compatible. If the resulting Hecke
character is `lambda`, form
`chi(x) = lambda(x) / lambda(c(x))` on actual idele classes. The arithmetic
involution implies conjugate self-duality. Its transport of local inclusions
makes the denominator trivial at each selected place; its transport of the
whole infinite factor preserves the trivial infinity component. A quotient
of finite-order characters again has finite order.

This paragraph describes the proposed reduction, not an implemented proof.
The sole declaration in this module is a `Prop`-valued definition of the
implication. A proof must supply the finite-period combination, actual
component transport and all character identities. In particular, this
statement supplies neither Grunwald--Wang existence nor an unconditional
proof of `CMFiniteCharacterPrescriptionStatement`. CM infinity realization,
local integral-unit extension, regular unit-prescription assembly, auxiliary
general position and Harris normalization remain separate.

The original is Guy Henniart, *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique* (2000), Section 3.6, Lemma 2, printed
pp.450--451 (one-based PDF pp.12--13), source
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Worker 84 read these original pages directly. The source prescribes two
places, chooses a finite-order character trivial at their conjugates and
takes the displayed conjugate quotient. The finite-set generalization and
explicit trivial whole infinity component are inherited from the existing
CM target, whose paired Markdown explains their provenance. Using the
explicit infinity prescription in the premise avoids needing a separate
connectedness argument in this reduction. No bound on the order of the final
CM character is added to that target.
