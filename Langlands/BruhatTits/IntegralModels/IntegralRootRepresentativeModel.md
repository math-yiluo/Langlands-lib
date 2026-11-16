# Integral models for supplied root representatives

This internal construction is derived from the published integral split-root
construction. It uses no additional literature premise.

`IntegralSplitTorusData.exists_model_of_rootRepresentative` starts with a smooth
ambient integral model and compatible integral split-torus data. For any nonzero
generic character and any representative of its actual root subgroup functor,
it constructs a smooth integral model with geometrically connected fibres and
an integral closed inclusion extending the supplied generic map.

The proof first constructs the integral root group using
`IntegralModel.SplitRoot`. Its generic root subgroup represents the same full
functor as the supplied representative. Uniqueness of representatives gives an
isomorphism to the supplied group that commutes with both generic inclusions.
Retargeting the constructed model along this isomorphism changes only its
generic-fibre identification. The integral group, its smoothness, geometric
connectedness and closed inclusion remain those of the split-root construction.
The commuting relation for the representative isomorphism proves compatibility
of this inclusion with the new generic identification.

The theorem asserts no existence of the ambient model or compatible torus data,
and no comparison with an apartment filtration.
