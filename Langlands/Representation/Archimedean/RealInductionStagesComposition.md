# Composition of real induction in stages

`RealInductionStagesCompositionStatement` says that inducing a composite of two complex-linear, compact-equivariant maps of local compact-finite standard modules agrees with composing their induced maps through the same surrounding blocks. The local ranks agree, the slice fits in the ambient rank, and the intermediate and final ambient lists have that rank.

The proof uses the slice formula in `RealInductionStagesInduce` to evaluate both maps at every orthogonal matrix. An induced map evaluates there by applying the local map to a slice and evaluating at the identity. The slice of the first induced image is the first local image of the slice. The compact values therefore agree, and injectivity of compact restriction gives equality on the whole group.

The same formula shows that induction takes a local function inclusion to the corresponding ambient inclusion. Such an inclusion holds when the local ranks and position characters agree and every Fourier window required in the target is already required in the source. The position formulas in `RealBlockPositionData` preserve those conditions after adjoining the same prefix and suffix.
