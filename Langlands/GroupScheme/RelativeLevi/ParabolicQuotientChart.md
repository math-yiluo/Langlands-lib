# Injective charts of the actual parabolic presheaf

Let `S` be any scheme, `G` a reductive group scheme over `S`, and
`i : P ⟶ G` an actual relative parabolic subgroup. Suppose that a supplied
morphism `q : G.X ⟶ Q` over `S` is smooth and surjective, and that, for every
test scheme `U` over `S` and every two group points `g,h`, equality
`g ≫ q = h ≫ q` is equivalent to membership of `g⁻¹ * h` in the full
normalizer subgroup functor of `range i`. The normalizer condition includes
all further refinements of `U`.

`quotientChart` is the natural transformation from the actual scheme Yoneda
presheaf of `Q` to the actual parabolic presheaf. It is obtained from the
already constructed `quotientParabolic` by the Yoneda equivalence.
`quotientChart_app` identifies evaluation with restriction of that family.
`quotientChart_app_comp` identifies evaluation at a point with a supplied
group-valued lift with the actual conjugate parabolic associated to the lift.
Neither assertion requires a global lift for every `Q`-valued point.

`quotientChart_injective` proves injectivity on every test scheme, and
`quotientChart_mono` gives the resulting monomorphism of presheaves. For two
parameters `a,b : T ⟶ Q` with equal parabolic families, first pull `q` back
along `a`, then pull it back again along the pullback of `b`. The resulting
composite `c : U₂ ⟶ T` is smooth and surjective, and both parameters have
group-valued lifts over `U₂`. Restriction of the equality identifies their
actual conjugate families. The exact conjugate-family normalizer criterion
places the difference of the lifts in the normalizer; the supplied fiber
criterion then identifies their quotient images. Thus `c ≫ a = c ≫ b`.
Smooth surjectivity makes the underlying scheme map an epimorphism, so
cancellation proves `a = b`.

This is an internal construction derived from actual quotient-family descent,
conjugate-family normalizer detection, stability of smoothness and
surjectivity under pullback and composition, and the effective-epimorphism
property of faithfully flat morphisms. It assumes neither an affine base nor
properness. It does not construct `Q`, establish surjectivity onto the whole
parabolic presheaf or a locally prescribed type, or prove the smooth proper
representability statement. Those remain separate geometric obligations.
