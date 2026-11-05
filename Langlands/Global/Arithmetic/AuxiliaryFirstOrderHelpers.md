# First-order auxiliary-character proof helpers

Worker 84 implements these helpers for the existing AuxiliaryCharacterStatement.
The final assembly in AuxiliaryCharacterFirstOrderProof uses these lemmas; no
new proposition target or independent acceptance is asserted by this file.

The universal valuation bound v(x)<=exp(-ord(x)) includes x=0. Positivity of
ord(p) makes p^k*x integral for k=max(0,-ord(x)); the normalized order bound
and multiplication of valuations prove this without a nonzero condition on x.
For a nonzero base-linear functional, choose a nonzero value and clear the
argument's denominator by this prime power. Base-linearity and p nonzero preserve
its nonzero value, producing an actual integral witness.

traceDifference is the actual base-linear difference
Tr(b*sigma(x))-Tr(b*x), assembled from multiplication, field trace and the
actual automorphism linear map. If b has the existing exact trace-stabilizer
property, its difference is nonzero for each automorphism outside the fixing
subgroup. The proof evaluates a hypothetical zero map and applies the exact
stabilizer equivalence.

exists_simultaneous_linear_detection chooses an integral witness for each member
of a finite family of nonzero base-linear maps, makes a finite set of their
nonzero values, and applies
the common inverse-prime-power separation theorem on the actual base integer
lattice. Each base-lattice detector x scales the chosen integral witness through
the actual relative integer map. Base-linearity identifies the new value with
x times the chosen coefficient, so one threshold works for every unwanted
family member and every later exponent. exists_simultaneous_trace_detection
specializes it to the nonzero trace differences of every unwanted automorphism.
The finite-separation theorem is imported by Lean name from its separate proof
unit. The final proof task records that independent prerequisite explicitly.

weighted_trace_tower is the exact identity
Tr(L/F)(b*i(a)*Tr(M/L)(y))=a*Tr(M/F)(b*y). Base-linearity pulls out a,
L-linearity puts b inside the relative trace, and pinned Mathlib's trace_trace
identifies the composed trace. No topology or character equality is substituted
for this actual field equality.

intermediatePadicField packages the same intermediate-field carrier and actual
p-adic algebra, with finite-dimensionality obtained by the scalar tower.
norm_units_fixed promotes an automorphism fixing L to an actual L-algebra
automorphism and imports Mathlib's norm invariance; it proves equality of the
actual norm units before any character is applied. weighted_trace_character
unfolds the published traceCharacter and scale evaluation formulas and applies
weighted_trace_tower, so its value is exactly the total weighted trace.

AuxiliaryCharacterFirstOrderProof combines these helpers with traceCharacter
and scale, the separate deep-unit character, finite-order extension and
norm-trace comparison, a finite family of integral trace witnesses and common
prime-power scaling. The other helper modules implement the valuation bounds,
actual subtype topology, depth nontriviality and exact stabilizer. The unchanged
target Markdown retains the original-source scope and characteristic-two
qualifications; this implementation uses the independent first-order route.
