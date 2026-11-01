# Normed vector valued smooth archimedean functions

Author: Worker 2.

This module extends the published scalar `Global/ArchimedeanGL` construction to
coefficients `V : Type uV` with `NormedAddCommGroup V` and `NormedSpace ℂ V`.
The number field `F : Type uF` has arbitrary universe, and the rank is any natural
number, including zero. The domain is the actual group of invertible matrices
over the product of archimedean completions. Its topology and its coordinates
are those of `archimedeanGLCoordinates`, with the actual mixed real/complex
matrix Banach algebra as model. No topology on the number field is an input.
Completeness or finite dimension of the coefficient space is not required.

In `Langlands.Global.ArchimedeanGL`, `vectorSmoothFunctions F n V` is the complex
submodule of actual functions whose coordinate expression is `ContMDiff` of
order infinity over `ℝ`, with target model the underlying real normed space of
`V`. `VectorSmoothFunctions` is its subtype. Addition preserves this condition;
complex scalar multiplication is real smooth through the continuous complex
linear scalar map restricted to real scalars. `vectorSmooth_continuous` proves
continuity in the original completion coordinates by composing with the
published homeomorphism and cancelling its inverse.

`vectorSmoothRightAction` is the representation by actual right translation,
`(R(g)f)(x) = f(xg)`. A right multiplication map in the mixed matrix units is
real smooth; composition and multiplicativity of the coordinate equivalence
prove stability. The representation laws are the unit and associativity laws
of the actual matrix group. `vectorSmoothRightAction_apply` records evaluation.

`vectorSmoothMap` postcomposes by `T : V →L[ℂ] W` for another normed complex
space, with its own arbitrary universe. Its smoothness proof restricts `T` to
real scalars and composes smooth maps. Postcomposition commutes with right
translation and satisfies the proved evaluation, identity and composition
formulas. The composition formula permits a third independently universed
normed complex space. An arbitrary algebraic linear map is not used in this
construction because it need not preserve real smoothness.

`vectorSmoothToContinuousMap` is the injective complex linear realization in
actual continuous functions. No topology on the smooth function space, or
continuity of the group action in such a topology, is claimed here.
`vectorSmoothScalarEquiv` identifies the complex scalar specialization with the
published `SmoothFunctions F n`; both maps keep the actual function unchanged.
The identification intertwines the two right translation representations.

The provenance is internal: the module generalizes the published scalar
coordinate definition using normed vector valued manifold calculus from pinned
Mathlib. All intrinsic submodule, representation and functoriality laws are
proved. There is no new identification with original literature. Topological
completions of induced representations, locally convex coefficients,
archimedean admissibility and automorphic existence remain separate work.
