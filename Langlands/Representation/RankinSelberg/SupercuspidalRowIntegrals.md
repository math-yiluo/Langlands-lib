# Compact and positive supercuspidal row integrals

This internal derived unit uses the canonical topology of a supplied p-adic
field, with independent field and representation-carrier universes.
`HasCompactSupercuspidalRowIntegrands` asserts compact support of the actual
equal-rank quotient integrand for every vector of the first representation,
every inverse-character Whittaker function, every row Schwartz–Bruhat test
vanishing at zero, and every complex spectral parameter. It asserts no
convergence for an arbitrary measure.

The construction explicitly assumes the full `SupercuspidalKirillovStatement`,
supercuspidality and irreducibility of the first representation, and a supplied
nonzero standard Whittaker functional. Apply the imported Kirillov support
adapter to every right translate of its coefficient. Intersect a smooth vector
stabilizer with the compact level-zero subgroup to obtain a compact open right
stabilizer. The imported mirabolic row-support argument now proves the compact
support assertion, independently of the second Whittaker function and parameter.

The second theorem starts with this compact-support assertion and the actual
weighted squared-norm coefficient package for a pair at parameter `u`. It also
requires a nonzero first functional, smoothness of both representations, and a
quotient measure positive on nonempty open sets and finite on compact sets.
Choose the integer-lattice test `Φ` from `CentralRowShell`. It has `Φ(0)=1`,
and its difference `Ψ` with its inverse-uniformizer central translate vanishes
at zero, takes only zero and one, and equals one at the identity last row.
The preceding compact-support assertion applies to every specified paired
coefficient integrand for `Ψ`, so the imported strict-positivity theorem gives
an absolutely convergent actual integral at `-u` with positive real part.
The result retains `Φ`, the exact central-difference formula and `Ψ(0)=0`.

These are internal compositions of the imported support, test-function and
coefficient constructions. The full Kirillov statement and the weighted
coefficient package remain explicit premises. No rational continuation, pole,
root of a normalized generator, or L-factor identity is concluded here.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
