# Graded exact Grothendieck multiplication over a nonarchimedean local field

`Langlands.Aubert.LocalFieldGraded.GradedGrothendieckGroup` is the direct sum
over all natural ranks of the exact Grothendieck groups of actual
finite-length smooth complex matrix representations. Each homogeneous
group uses the topology from the supplied realization. The inclusion
`LocalFieldGraded.inclusion` puts an exact class in its rank summand.

For classes in ranks \(a,b\), `LocalFieldGraded.binaryProduct` descends the
actual binary normalized induction functor to a bilinear map with target
rank \(a+b\). The three preservation inputs are precisely those of
`LocalFieldBinaryProductExactLengthStatement`. The class formula
`LocalFieldGraded.binaryProduct_objects` identifies the product of two
actual classes with the class of the corresponding induced representation.
`LocalFieldGraded.multiplication` extends those maps to the two direct-sum
variables and `LocalFieldGraded.multiplication_homogeneous` recovers the
homogeneous product. The unit class `LocalFieldGraded.unit` is the
class of the actual one-dimensional trivial representation of
\(\mathrm{GL}_0(F)\).

Zelevinsky 1980 §1.1 specifies the standard upper-block Levi and the
trivial rank-zero group. §1.7, printed pp. 172–173, forms the graded
Grothendieck group, sends a pair of classes to the class induced from their
tensor product on the Levi and places the unit in rank zero. The exact
Grothendieck group uses actual short exact sequences, and its identification
with the free group on irreducible classes follows from the published
Jordan–Hölder comparison. The multiplication and unit class here provide
the operations for the ring identities of §§1.7 and 1.9.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §§1.1 and 1.7, printed pp. 170 and 172–173.
