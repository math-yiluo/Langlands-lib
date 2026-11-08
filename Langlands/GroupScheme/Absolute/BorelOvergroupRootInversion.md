# Root inversion preserving a Borel overgroup's tangent support

Worker 146. These internal results use the published geometric rank-one normalizer construction together with the preceding rank-one centralizer-containment helper. They work over an algebraically closed field of any characteristic with a connected reductive affine ambient group, its specified split maximal torus, and a smooth connected closed overgroup containing that torus via an actual lift.

If both signs of a root occur in the overgroup's actual tangent-weight support, the rank-one centralizer-containment lemma puts the actual generic cocharacter centralizer in the overgroup. That centralizer is connected reductive, retains the specified torus as maximal and has only pairwise-dependent roots. The published `RankOneCentralizerDetection.exists_nonidentityNormalizer` supplies an actual point in its torus normalizer with a nonidentity Weyl class. Published rank-one negation says that point sends the chosen root to its negative.

Transport along the centralizer inclusion gives an actual ambient normalizing point in the overgroup, with the same entire-character Weyl action. Every point of the centralizer conjugates the overgroup into itself because the centralizer is contained in it. The published `RelativeRoot.weylAction_mem_actionWeightSupport_iff` therefore shows that the transported point preserves the full intrinsic tangent-weight support, including zero when it occurs. Passing to the actual quotient `relativeWeylGroup` gives the second lemma.

Only inversion of the chosen root is asserted. The result introduces no coroot, reflection formula on other characters, root datum, simple-root system or parabolic classification premise. Connectedness of the overgroup is an explicit intermediate hypothesis and must be derived from Borel containment when applying these lemmas to the final target.

`AbsoluteBorelOvergroupRootInversionStatement` is the Prop-valued universal interface of the Weyl-quotient conclusion. The accompanying implementation lemmas are included for the final proof's use; this intermediate statement submission is not a proof record for the final overgroup-cocharacter target.
