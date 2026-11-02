# Constants and scalar algebra for actual locally constant sections

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.4–II.2.5, printed pp.38–39 /
PDF pp.44–45, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were read and the constants remark on PDF45 was checked
visually. The separately registered 2010-edition corrections, PDF pp.2–3,
concern the later module nondegeneracy convention rather than these constants.

`constants R U` is Mathlib's `LocallyConstant.constRingHom` on the actual
open subtype `U`, with the existing pointwise ring. It takes a coefficient
to that constant function, and evaluation at any point is a left inverse.
This proves injectivity when `U` is nonempty.
`restrict_constants` and `restrict_comp_constants` prove compatibility
with every actual open restriction, both on coefficients and as equality
of unital ring homomorphisms. The all-open ring presheaf, every chosen
basis ring presheaf, and its forgetful abelian presheaf have corresponding
literal restriction equations. They are all proved by evaluation, using
the actual continuous open inclusion from the imported presheaf.

The source says that complex constants inject into every section ring.
For the empty open this is false: zero and one are the same empty-domain
function. The implementation proves their equality by function extensionality and
elimination of a hypothetical point in the empty open. Injectivity would
then contradict `zero_ne_one`. The complex specialization is an actual
empty-open counterexample, for any supplied topological space including an
empty space. For nontrivial coefficients, the implementation proves that injectivity
is equivalent to nonemptiness of the open subtype. The unital constant ring
homomorphism exists on the empty open and suffices for later restriction of
scalars; its target is the one-element ring.

For commutative coefficients, `sectionAlgebra` exposes Mathlib's existing
pointwise algebra. Its algebra map is exactly `constants`, and its scalar
action is multiplication by the constant section. These statements do not
require a topology on the coefficient ring.
`restrictAlgebraHom` is the existing `LocallyConstant.comapₐ` along the
same inclusion; its underlying ring homomorphism is exactly `restrict`.
`restrict_smul` and `restrict_algebraMap` prove scalar and algebra-map
compatibility. `complexSectionAlgebra` and `complexRestrictAlgebraHom`
expose the original complex specialization explicitly. These equations
include the empty open, without any injectivity premise.

Arbitrary rings and supplied topologies are an internal generalization of
the original complex-valued example on a source totally disconnected space.
The space universe `u` and coefficient universe `r` are independent; the
section carrier is `LocallyConstant U R` in `Type (max u r)`.
No module-sheaf categories, arbitrary vector-sheaf actions, compact-section
comparisons or categorical equivalences are constructed here.

Worker 1215 implements this unit. Worker 6 contributed the source diagnosis,
specification and prior empty-domain proof route. Worker 1227 supplies the
separate presheaf dependency, which is imported without modification.
