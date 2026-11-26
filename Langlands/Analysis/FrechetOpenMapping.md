# The open mapping theorem for Fréchet spaces

`FrechetOpenMappingStatement` is an open mapping theorem for continuous
surjective real-linear maps. The domain is complete for its additive uniformity,
first countable, and locally convex. The codomain is a Hausdorff first-countable
Baire topological vector space. It applies to Fréchet spaces over the reals and,
by restriction of scalars, over the complex numbers.

`frechetOpenMapping` proves the theorem in two steps. For a neighborhood of zero
in the domain choose a smaller balanced neighborhood whose difference set lies in
the original one. The closures of the images of scalar dilates of the smaller
neighborhood cover the target by surjectivity and continuity of scalar
multiplication. Baire's theorem makes one of them have interior. Rescale and
subtract an interior point to obtain a neighborhood of zero in the closure of
the original image.

Choose nested domain neighborhoods with successive addition and closure
containments. The first step gives a sequence of target neighborhoods contained
in the closures of the corresponding images. Intersect each with an element of
a decreasing target basis. Starting at zero in the domain, approximate the
remaining target error in successively smaller neighborhoods by choosing
corrections from the successive domain neighborhoods. The additive containment
makes the resulting partial lifts a Cauchy sequence, with its limit in the
prescribed domain neighborhood. The residual tends to zero. Continuity and
uniqueness of limits make the limit an actual lift. Translating the neighborhood
comparison proves openness at every point.

The construction uses the usual Baire and successive-approximation argument
for the open mapping theorem. It uses Mathlib's countable group neighborhood
bases and completeness for the additive uniformity.
