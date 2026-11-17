# Algebraizing functions constant on rational components

Let `X` be locally of finite type over an algebraically closed field `k`.
Every actual connected component of `X` contains a rational section.
A function from rational sections of `X` to rational sections of a relative
target `Y`, constant on these actual components, therefore defines an actual
componentwise constant relative morphism `X → Y`.

The construction `ofRationalFunction` chooses a rational representative of
each component and uses `ofComponents`. The theorem
`section_comp_ofRationalFunction` proves agreement with the original function
when the component-constancy hypothesis holds. The construction itself accepts
any function; without that hypothesis, only its values on the chosen
representatives are prescribed.

The generic formula `section_comp_ofComponents` identifies the value of a glued
map on any rational section. The equality theorem
`IsComponentConstant.hom_ext` then shows that rational sections detect equality
between two componentwise constant maps. This conclusion does not require the
source to be reduced.

These are internal derived interfaces for algebraizing component-constant
rational matrix homomorphisms. The representative argument generalizes the
published `IdentityComponent.pointComponent_surjective_of_isAlgClosed` proof:
each component contains a closed point by the Jacobson property, and a closed
point over an algebraically closed field gives a rational section. No claim
about detecting arbitrary scheme maps from their rational values is made.
