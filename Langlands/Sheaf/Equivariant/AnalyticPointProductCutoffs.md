# Actual stable cutoffs on analytic induced point products

This internal module specializes the proved right Kan coordinate cutoffs to
the existing analytic point family used by the Godement construction, including
its lifted index universe and independent coefficients.

The actual fiber equation shows that a translated point coordinate has original
spatial position equal to its image under the untranslated structure morphism.
In particular that position lies in the defining open for an ordinary-open
domain. The spatial cutoff therefore agrees with a section on opens contained
in the selected set and is zero on disjoint opens. It commutes with ordinary
étale restrictions.

Raw induced point-product sections extend globally from every ordinary-open
domain. The domain inclusion is a monomorphism, hence all translated point
fibers inject, and the preceding raw-extension theorem applies.

For the existing distinguished lift system, a stable spatial cutoff preserves
the actual locally discrete submodule. Local discreteness of a global section
can be checked on two ordinary opens covering the underlying space: the sieve
of restrictions lying in the smooth submodule covers by actual joint
surjectivity, and the established locality theorem applies.

`exists_etaleSmoothPointProduct_compact_extension` combines these facts with
the proved compact stable-neighborhood theorem for a continuous analytic action
on a Hausdorff analytic space. A locally discrete section on an ordinary open
extends raw globally. Choose a stable relatively compact neighborhood of the
given compact subset whose closure lies in the original open, and cut off the
raw extension there. The result is locally discrete on the original open and
zero on the complement of the chosen closure, hence locally discrete globally.
It agrees with the original section on the chosen neighborhood. The theorem
retains arbitrary independent point coefficients and all the original
independent universes. It assumes the existing admissible-refinement instance
and makes no injectivity assumption.

No derived acyclicity assertion is made in this module.
