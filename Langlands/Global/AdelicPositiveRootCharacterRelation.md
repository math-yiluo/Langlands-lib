# Adelic bounds from a positive integral root-character relation

This internal derived calculation evaluates an exact integral character
relation under the actual normalized adelic character norms.

`HasUniformCharacterBound F T psi S` means that the normalized norm of the
actual torus character psi has one positive upper bound on the given set S of
full adelic torus points.

Suppose d psi equals the ambient restriction of eta plus b alpha. On a torus
point whose image in G lies in the actual norm-one subgroup for every ambient
algebraic character, the norm of eta is one. Character addition becomes
multiplication of normalized norms, and natural multiples become powers.
Consequently the d-th power of the psi norm equals the b-th power of the
alpha norm exactly.

If d and b are positive and the psi norm is at most C uniformly on S, this
identity gives the uniform alpha bound max(C^d,1). For an alpha norm at most
one the bound is immediate. Otherwise its positive b-th power is at least
itself and is bounded by C^d. Inverting each torus point gives the positive
weak lower bound C' inverse for its alpha norm, in the left-action chamber
convention.

`HasUniformTorusLineHeightBound` is an explicit uniform upper-bound assumption
on the actual selected-vector representation height at torus images. For a
preserved coordinate line, the exact height-scaling formula writes this height
as its normalized line-character norm times its fixed positive identity
height. Dividing a supplied positive height bound by that fixed identity
height therefore constructs a uniform bound on the actual torus line
character.

The uniform height bound is assumed in this last conversion and is not
constructed by this module. The root-bound transfer likewise assumes the
positive integral relation, the ambient norm-one condition and the uniform
character bound. No rational-orbit uniform height estimate, fundamental-set
coverage or chamber theorem is asserted.
