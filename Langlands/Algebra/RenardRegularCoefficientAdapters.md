# Actual regular-factor coefficient comparisons

Authored by Worker 6, Worker 185 and Worker 1207. Worker 6 supplied the proof
construction. Worker 185 completed the documentation and interface and boundary
examples; Worker 1207 independently completed the same proof prototype with
additional checks of explicitly selected coefficient and action structures.

The theorem
`Langlands.Algebra.RenardRegularCoefficientAdapters.regularCoefficientComparisons`
has exactly the type
`Langlands.Algebra.RenardRegularCoefficientStatements.RegularCoefficientComparisons`.
It proves all four universal comparison families in that unchanged Library
proposition. The coefficient ring k and the nonunital rings A and B have
independent universes `uk`, `uA` and `uB`. The equalities compare entire
`Module k B` structures on B's given additive group.

These are derived internal consequences of
`NondegenerateScalars.module_eq_of_compatible` and the published
`NonUnitalBimoduleTensorScalars.InputCompatible` interface. Their motivation is
David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, I.2.1 (printed p.14 / PDF20), I.2.2–I.2.3 (printed pp.15–18 /
PDF21–24), and I.4.2 (printed pp.23–24 / PDF29–30). Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source does not state the four adapters as separate results. The proof
uses the Library's coefficient uniqueness construction: for a fixing
idempotent e, compatibility gives `(c e) • b = c • (e • b) = c • b`.

For the right regular comparison and F:

- `rightRegularTower` explicitly uses `NonUnitalModule.rightRegular B`.
  Its scalar tower is the identity
  `x * (c • b) = c • (x * b)`, from `SMulCommClass k B B`.
  This helper alone needs no `IsScalarTower k B B`.
- `rightRegularRecoveredModule_eq` uses that tower and
  `NondegenerateScalars.module_eq_of_compatible` over B's opposite ring,
  with `hB.op` and exactly
  `NondegenerateTensorFunctor.rightRegular_isNondegenerate hB`.
  The opposite-ring coefficient laws are the local adapters
  `opIsScalarTower` and `opSMulCommClass`.
- `fInputCompatible` unfolds the exact `InputCompatible` proposition and
  rewrites by the entire Module equality. The remaining goal is the given
  `IsScalarTower k A B` for the supplied original left A-action. It requires
  neither idempotentedness of A nor nondegeneracy of that action.

For the supplied original right A-action and P,
`rightActionRecoveredModule_eq` applies the same uniqueness theorem over
A's opposite ring, retaining the supplied action, its coefficient tower,
and its specified nondegeneracy witness `hRight`. This comparison requires
no coefficient law for B's multiplication.
`pInputCompatible` explicitly installs `NonUnitalModule.regular B`,
unfolds `InputCompatible`, and rewrites by that Module equality.
Its remaining law is
`(c • b) * x = c • (b * x)`, exactly `smul_mul_assoc` from
`IsScalarTower k B B`. It needs no idempotentedness of B and no
algebra-homomorphism presentation of the original right A-action.

Finally, `regularCoefficientComparisons` introduces each conjunct's original
parameters and applies these four helpers. No Module identification,
compatibility certificate, or comparison map is an input. The companion
`RenardRegularCoefficientAdaptersChecks` module checks complete unapplied
types, unequal universes, named structures amid competing instances, and
nonzero, zero-action and subsingleton applications.

This proves the sufficient common-coefficient bridges for later actual F/P
specializations. The convention boundary in
[the public coefficient note](../../notes/renard/duality-coefficient-conventions.md)
continues to apply: commutation of original actions alone does not supply the
assumed towers. Tensor-dual evaluation maps, inverse and isomorphism statements,
naturality, and the full-source I.4.2 coefficient convention remain separate
obligations.
