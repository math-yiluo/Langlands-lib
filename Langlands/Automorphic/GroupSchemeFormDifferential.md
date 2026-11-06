# Actual enveloping differentiation on uniform adelic forms

Fix a number field, an affine group scheme smooth of relative dimension
`d`, and the original finite plot-smooth rational-invariant function
carrier. Every element of the actual complex identity-tangent
enveloping algebra intertwines the action of its entire associative
center: a central element commutes with the chosen enveloping element.
The original operator therefore maps a finite-dimensional global center
orbit into a finite-dimensional orbit. This proves preservation of
`IsAdelicCenterFinite` and restricts the actual algebra action to the
existing center-finite submodule.

For the form constructions, retain the existing hypotheses of connected
reductivity, a closed matrix representation of positive dimension and a
specified maximal compact infinite subgroup. Membership in the existing
uniform automorphic subrepresentation is equivalent to whole-function
infinite-subgroup finiteness, whole-function center finiteness and the
existing full adelic uniform moderate-growth bound. The ordinary growth
condition in its definition follows by taking the identity derivative.
The uniform bound chooses one exponent before all enveloping operators,
each with its own constant.

The actual enveloping action preserves this intersection. The proof
combines the previously proved preservation of whole-function infinite
finiteness, the central commutation argument above, and the uniform
growth theorem: to bound the derivative by `b`, test the original bound
at `a*b` for each further operator `a`. Its identity derivative also
supplies the ordinary growth needed by the broader form space.
`uniformAdelicAutomorphicEnvelopingAction` restricts the original algebra
homomorphism to this unchanged subspace.
Its differential operators commute with the existing finite adelic
right action, by restriction of the original commutation theorem.

The uniform tensor form subrepresentation intersects the existing
literal tensor form subrepresentation with the same uniform growth
space. It consists exactly of uniform forms whose original functions
belong to `tensorSmoothSubrepresentation`. The earlier actual tensor
differentiation theorem and the uniform form preservation just proved
give its restricted enveloping algebra action. The displayed value
identities identify both restricted actions with the original action
under the original-function inclusions. The tensor restriction also
retains the same finite-translation commutation law.

This is an internal construction from the existing actual operators,
finite-vector image theorem and established growth and tensor
preservation theorems. The old `hcalc` proof parameter remains in the
existing form types; `adelicDifferentialCommutator_of_smooth` supplies it
on the original atlas, and proof irrelevance identifies every such
realization with `actualAdelicEnvelopingAction`. No additional covariance
or calculus hypothesis is introduced. This unit does not prove uniform
growth from ordinary moderate growth, infer a tensor condition from
finiteness, establish stability under all infinite translations, or
prove preservation of cuspidality or a comparison with the original
matrix form space.
