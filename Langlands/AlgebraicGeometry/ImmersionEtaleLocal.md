# Checking immersions on étale neighbourhoods

This internal construction defines `etaleImage`, the open image of an étale
scheme morphism, and proves that immersion can be checked after an étale
neighbourhood of every point of the target. All schemes are arbitrary, in any
universe. No affine or quasi-compact neighbourhood hypothesis is imposed.

For one étale map, the proof factors it through its open image. This factor is
surjective and étale. The pullback of the original morphism is also the pullback
of the morphism restricted to that open image: the proof constructs the
comparison map and cancels the open restriction pullback square. The
surjective étale immersion descent theorem then gives immersion on the open
image.

For a family of neighbourhoods, the proof chooses one neighbourhood at each
target point. Their open images cover the target. The preceding result gives
immersion on each open image, and Zariski locality at the target gives immersion
of the original morphism.

The provenance is internal. The proof uses the Library's surjective étale
immersion descent and Mathlib's pullback and target locality interfaces; no
separate external-source translation is asserted.
