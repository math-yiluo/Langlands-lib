# Connected reductivity of finite separable affine Weil restriction

`Langlands.GroupScheme.AffineWeilConnectedReductiveStatement.{u}` states that,
for an arbitrary finite separable extension of fields `K/k` in universe `u`,
the actual `AffineWeil.groupScheme k K G` is connected reductive whenever the
actual group `G` over `K` is connected reductive.

The statement uses the published predicates and construction unchanged.
Affineness and local finite type of `G`, needed to form this affine Weil
restriction, follow from the supplied connected reductivity: the statement
installs its affine and smooth structure morphisms. There is no additional
perfectness, characteristic, infinitude or splitting hypothesis.

This is an internal intermediate target for transporting parabolic and
geometric unipotent radical diagrams under finite separable Weil restriction.
Its proposed route uses the actual embedding-product comparison over an
algebraic closure, stability under finite products there, and reflection under
field extension. This file states that target; it does not prove it.
