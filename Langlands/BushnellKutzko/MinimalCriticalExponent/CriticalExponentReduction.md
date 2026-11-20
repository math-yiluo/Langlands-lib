# The lower bound and the next adjoint lattice

This module supplies the lower bound in Bushnell–Kutzko (1993),
Proposition (1.4.15), printed p. 41, and reduces its equality clause to
containment at the next step of the adjoint lattice. It uses the critical
maximum of (1.4.5), printed p. 36, as established by `adjointExactness`.
The source is `bushnell-kutzko-1993-admissible-dual-gln`.

If `g` shifts the lattice chain by `d`, its endomorphism lies in filtration
step `d`. Left and right multiplication by that endomorphism carry the
order into step `d`, so its adjoint lattice at `d` is the full order. Every
adjoint lattice lies in the order. A witness to the nonempty critical-index
set therefore shows that the order fails containment in the sum of the
centralizer lattice and the first filtration step. Thus `d` is a critical
index and lies at or below the greatest index `k₀`. The stabilizer shift
formula identifies `d` with the order valuation.

At `d = k₀`, the greatest-index property gives the containment at `d + 1`.
Conversely, containment there gives containment at every larger index by
antitonicity, so `k₀` must equal `d`.
