# Functorial carrier universe lifts

Author: Worker 1187. This is internal infrastructure for the preservation proof
requested by the represented-parabolic Renard VI.1.2 task. It makes the
published carrier lift from `Category/UniverseLift.lean` into fully faithful
functors on algebraic and smooth complex representations.

Maps are conjugated with the published `up` and `down` representation
equivalences. Module carrier lifts preserve small coproducts: a map out of the
lifted direct sum is the direct-sum descent of the maps restricted along `up`,
composed with `down`. Together with Mathlib's finite-colimit preservation this
gives all colimits of diagrams with objects and arrows in the original carrier
universe.

The algebraic representation lift commutes with forgetting the action.
Preservation and reflection by the module forgetful functor therefore give
preservation of small limits and colimits. The smooth lift commutes with the
full inclusion into algebraic representations. That inclusion is left adjoint
to the smooth part, so it preserves colimits. Full faithfulness reflects
colimits and yields preservation by the smooth carrier lift.

This module does not supply preservation of limits by the smooth carrier
lift, the comparisons with parabolic induction or Jacquet, or a proof of the
published represented-parabolic statement. The constructions and arguments
above are derived category infrastructure, not separate assertions from
Renard's text.
