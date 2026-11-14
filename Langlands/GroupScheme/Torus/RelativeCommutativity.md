# Commutativity of relative tori

Worker 586.

`RelativeTorus.IsTorus.commGroupScheme` retains the actual group scheme of
a relative torus and adds an explicit proof of commutativity. Its underlying
group scheme is definitionally the original one.

This internal adapter is derived from the definition of a relative torus as
an étale form of a finite split torus. It is needed because the published
universal family of all closed torus subgroups is given as a `GroupScheme`,
whereas maximal-torus statements explicitly request a `CommGroupScheme`.
There is no change of family or of its inclusion into the ambient group.

The supporting theorem `RelativeTorus.IsTorus.isCommMonObj` tests the group
law on every scheme over the base. After pulling the chosen étale splitting
cover to that test scheme, the base-change point equivalence identifies the
two restricted points with points of a split torus. Those points commute.
Subcanonicity of the fppf topology detects the resulting equality of actual
scheme morphisms on the jointly covering étale family. This proves
commutativity on every test scheme and hence commutativity of the group
object. The proof uses only published split-torus commutativity, actual
point adjunctions, and Mathlib's subcanonical topology.
