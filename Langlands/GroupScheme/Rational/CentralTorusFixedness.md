# The Weyl action on actual central cocharacters

Author: Worker 1319.

This internal unit proves pointwise fixedness for the actual real image of a map `f : A → T` whose composite with `i : T → G` is central. It uses the published `IsCentral`, `normalizingAut`, `cocharacterMapReal`, and `relativeWeylRealAction`, over any field and universe. It does not assume that `A` or `T` is split, or that `G` is reductive. The underlying scheme map of `i` must be a monomorphism, as required for the published Weyl action.

`relativeWeylFixedSubspace i` constructs the common fixed subspace inside the published `V T`, as the intersection of the kernels of `relativeWeylRealAction i w - id` for all elements of the actual quotient. Its membership criterion is equality with the original vector under every quotient element. This definition introduces no new action or quotient.

`IsCentral.comp_innerIso_hom` proves that inner conjugation fixes a central group-scheme map by testing every point of every scheme over the base. Its image is central on those points, so multiplication by the conjugating point and its inverse cancels.

`normalizingAut_comp_of_central` applies the defining conjugation identity of the actual normalizing automorphism and the preceding lemma. The monomorphism of `i` then cancels, proving the equality `f ≫ normalizingAut.hom = f` of actual commutative-group-scheme maps.

Tensor induction extends that equality to the real cocharacter image. Quotient induction descends it from the actual normalizer points to `N(k)/Z(k)`. The range fixedness theorem applies this equality to every vector in the range of `cocharacterMapReal f`; `central_range_le_relativeWeylFixedSubspace` packages that result as containment in the common fixed subspace.

The provenance is internal: these lemmas unpack centrality and the published actual conjugation action, followed by tensor and quotient induction. They provide the fixedness consequence for an actual embedded central torus; identifying its image with the common root annihilator remains a separate geometric obligation.
