# The word-seminorm bound on finite-dimensional algebraic carriers

`RealSmoothCasselmanWallachFiniteDimensionalStatement` considers a finite-dimensional
complex vector space, an injective linear map `e` into the genuine smooth carrier of a real
general linear group action by bounded operators, and a linear map `f` into another genuine
smooth carrier. The theorem `realSmoothCasselmanWallachFiniteDimensional` bounds the
empty-word norm of `f v` by a single nonnegative constant times the empty-word norm of
`e v`. The two ambient carriers and the algebraic vector space have independent universes.

The published `derivativeCLM_nil_injective` identifies `V` with the range of `e` followed by
the empty-word map into the first normed space. Transfer the empty-word map after `f` to this
range by the inverse linear equivalence. The range is finite dimensional with its inherited
norm, so the transferred linear map is continuous and satisfies its operator-norm inequality.
Evaluating that inequality on the image of `v` gives the conclusion.

This is an internal finite-dimensional case of the Library's word-seminorm bound. Its
single source word is the empty word. It follows from finite-dimensional normed linear
algebra and needs only injectivity of the source map.
