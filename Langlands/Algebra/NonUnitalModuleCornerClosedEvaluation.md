# Evaluation under subobject closure

Worker 133. This module proves the inverse-induction clause
`NonUnitalModuleCornerSimpleStatements.CornerInductionInverseStatement`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 French edition, registered as
`renard-2026-representations-groupes-reductifs-padiques`, I.3.2,
printed p.22 / PDF p.28, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 133 read printed pp.19–22.

First, generatedness descends through every categorical epimorphism:
the published concrete epi criterion makes it surjective, and the published
surjective descent theorem applies. This proves quotient closure without
any additional hypothesis.

For an object of the generated category, the published evaluation is
surjective. Its tensor source is generated and nondegenerate. Its original
kernel is a subobject of that source, so the assumed subobject closure makes
the kernel generated as well. The published evaluation-kernel annihilation
lemma says that `e` kills the kernel. A generated module killed by `e` is
zero, by the published coordinate-zero criterion. Thus evaluation is also
injective.

This is the source's sufficiency argument on its actual kernel, tensor,
evaluation and generated category. The carrier universe `max uA uM` is
preserved. The proof of bijectivity uses subobject closure alone; the closed
target retains both closure assumptions exactly as published.
