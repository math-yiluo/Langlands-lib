# Associativity and the unit of graded normalized GL induction

`Langlands.Aubert.LocalFieldGraded.LocalFieldGradedAssociativeUnitStatement`
asserts associativity and both unit laws for the bilinear normalized
induction multiplication over any nonarchimedean local field. It applies
to every preservation witness for the actual binary functor. Its three
identities quantify over the entire graded direct sum of exact
Grothendieck groups. The unit is the class of the actual trivial line
of \(\mathrm{GL}_0\).

Zelevinsky 1980 §1.7(a), printed p. 173, obtains associativity by comparing
the two bracketings of a three-factor product with normalized induction
from the three-block Levi. §1.7(c), on the same page, gives the class of
the trivial representation in rank zero as the unit. The statement
uses the exact groups and bilinear maps of `LocalFieldGradedGrothendieck`
to express these identities. Commutativity is the separate assertion of
Zelevinsky §1.9.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.7(a), (c), printed p. 173.
