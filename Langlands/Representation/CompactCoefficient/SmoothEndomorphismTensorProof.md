# Smooth endomorphisms as rank-one tensors

Author: Worker 140.

This proof establishes the published `Langlands.Renard.CompactRepresentation.SmoothEndomorphismTensorStatement`, corresponding to David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, IV.1.4, equations (IV.1.4.1)–(IV.1.4.3) and the following admissibility remark, printed p.91 / PDF p.97. Source ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof uses coordinates rather than Renard's dimension comparison. Choose a basis of the representation space. The coefficient of a tensor at each basis vector is a smooth functional; evaluating it at a vector is the corresponding coordinate of the rank-one map applied to that vector. These equalities show injectivity.

Every elementary rank-one map is fixed on both sides by the intersection of open subgroups fixing its vector and its functional. Tensor induction and subgroup intersections give the same conclusion for sums. Conversely, an endomorphism fixed on both sides by an open subgroup `K` has image in the `K`-fixed subspace. Admissibility makes that subspace finite-dimensional. Each coordinate of the endomorphism is a smooth functional because of invariance on the right by `K`. Expansion in a finite basis of the image space gives the required tensor. This argument uses neither Haar measure nor a compact refinement of `K`.

The helper `smoothEndomorphismTensorMap` is exactly the linear map appearing in the published statement. Its injectivity helper needs no smoothness or admissibility; the range helper assumes precisely admissibility, including smoothness. The final theorem retains both independent universe parameters and all original quantifiers.
