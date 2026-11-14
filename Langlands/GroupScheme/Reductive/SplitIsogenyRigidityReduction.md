# General torus rigidity implies split-isogeny uniqueness

This internal reduction proves
`SplitIsogenyRigidityReductionStatement`, namely
`ReductiveIsogenyTorusRigidityStatement → SplitIsogenyUniquenessStatement`,
in every universe. The general rigidity statement is an explicit premise.
This module does not prove it or claim unconditional split-isogeny uniqueness.
The published uniqueness target and all of its hypotheses are unchanged.

Three preliminary adapters relate the field and relative definitions.
`IsConnectedReductive.baseChange_fieldPoint` applies the published arbitrary
field-extension theorem to any actual morphism between field spectra. It
uses `Spec.map_surjective` to express that morphism as `Spec.map` of its own
coefficient map, and that map supplies the algebra structure. The resulting
base change is therefore the specified actual base change.
`IsConnectedReductive.isReductive` applies this to each geometric point and
uses the published passage from connected reductivity to pseudo-reductivity.
It supplies the original smooth and affine structure maps and the geometric
fibres required by `IsReductive`. `IsMaximalTorus.isFibrewiseMaximalTorus`
uses the same coefficient-map argument and the published maximal-torus
base-change theorem for each actual residue-field point. It assumes the
smoothness and affineness required by that theorem.

The theorem `splitIsogenyRigidityReduction` then proceeds as follows. The
supplied adjoint quotient provides connected reductivity of the target,
and the supplied adjoint-torus image provides splitness of the target torus.
The given equality after every target character implies equality of the two
actual torus homomorphisms by `IsSplitTorus.hom_ext_of_characters`. Thus the
two isogenies agree on the entire supplied source torus, including all
central character directions.

The adapters and split-torus relative-torus theorem supply precisely the
hypotheses of general rigidity over the field spectrum. The rigidity
statement is applied with `f = φ₂` and `F = φ₁`. Its existence assertion
produces an fppf cover and local torus points conjugating `φ₁` into `φ₂`.
Its uniqueness assertion, tested on every refinement, places the difference
of two such points in the full scheme-theoretic centre. The previously
proved `IsAdjointSplitTorusImage.exists_basePoint_of_local_conjugates`
therefore descends them to a ground-field point of the specified actual
adjoint torus whose inner action after `φ₁` equals `φ₂` as a group-scheme map.
Finally `splitIsogenyUniqueness_of_conjugatorExistence` supplies uniqueness
through all-test faithfulness after an arbitrary isogeny.

No separability, central-isogeny, smooth-kernel, reduced-centre, nonempty-root,
or rational-lifting assumption is added. All maps and all centre comparisons
remain scheme-theoretic. The provenance is internal: the only unproved input
is the explicitly assumed published general rigidity proposition, and all
other steps are formal consequences of the published field-extension,
character-separation, quotient, action and descent results.
