# Primitive coefficients with exact trace-functional stabilizer

Author: Worker 84. This is an internal algebraic target for the H2 auxiliary
character investigation in the global automorphic program. The file defines
propositions and proves no existence theorem.

## Mathematical content

Let \(M/F\) be a finite separable field extension, and let \(L\) be an actual
intermediate field. `PrimitiveTraceStabilizerStatement` asks for a nonzero
element \(a\in L\) which generates \(L/F\) and satisfies

\[
 \left(\forall x\in M,\quad
   \operatorname{Tr}_{M/F}(a\,\sigma(x))
     =\operatorname{Tr}_{M/F}(a\,x)\right)
 \quad\Longleftrightarrow\quad
 \sigma\in\operatorname{Gal}(M/L)
\]

for every \(F\)-algebra automorphism \(\sigma\) of \(M\).
Here \(\operatorname{Gal}(M/L)\) means the pointwise fixing subgroup of
\(L\) in \(\operatorname{Aut}_F(M)\). Normality of \(M/F\) is not assumed.
The notation makes no claim that \(M/F\) or \(L/F\) is Galois.

`HasExactTraceStabilizer L a` is the displayed equivalence, quantified over
all automorphisms. It is defined for any finite field extension; the existence
target additionally requires separability. The action is precomposition by
\(\sigma\), exactly as displayed. The trace is Mathlib's actual algebraic
trace, and `L.fixingSubgroup` is its actual pointwise fixing subgroup.
Primitivity is expressed within \(L\) by
`IntermediateField.adjoin F ({a} : Set L) = ⊤`. The coefficient in the trace
is its image under the actual subtype inclusion \(L\hookrightarrow M\).
The base and ambient field universes `u` and `v` are independent.
There is no characteristic restriction.

The nonzero condition also applies to \(L=F\). In that case one may choose
\(a=1\); a primitive element equal to zero would not suffice for the
nontriviality needed in the later character construction.

## Provenance and intended proof

This is a derived algebraic lemma, not a transcription of a theorem in Harris
or Henniart. Its intended proof uses the primitive element theorem, invariance
of trace under algebra equivalences and nondegeneracy of the trace pairing for
finite separable extensions. Trace invariance moves the automorphism from the
variable to the coefficient. Nondegeneracy then identifies functional
stabilization with fixation of the coefficient. Primitivity identifies that
fixation with pointwise fixation of \(L\).

The pinned Mathlib sources supplying these ingredients are
`Mathlib/FieldTheory/PrimitiveElement.lean`
(`Field.exists_primitive_element`) and
`Mathlib/RingTheory/Trace/Basic.lean`
(`Algebra.trace_eq_of_algEquiv` and `traceForm_nondegenerate`).
These are imported infrastructure, rather than assumptions that encode the
desired stabilizer equality.

The motivation is Harris 1998, proof of Lemma 4.7, printed pp.204–206,
especially (4.12)–(4.13), and Henniart 2000, Section 3.4(3) and Section 3.6,
Lemma 3. Harris constructs characters using logarithmic lattices and normal
bases. The trace-functional route is an alternative algebraic starting point.
The relevant Harris proof passage and the retained source correction note were
read directly. This target does not attribute this alternative proof to Harris.

## Boundary with auxiliary character existence

`AuxiliaryCharacterStatement` requires continuous finite-order complex
characters, arbitrarily deep nontriviality, and exact stabilizer on valuation
units after pullback by the actual multiplicative norm. None of those
conclusions is stated here. This lemma concerns an additive functional on the
whole field \(M\).

Using it for that statement still requires logarithm and norm compatibility
on sufficiently deep units, trace transitivity, control of the additive
character's kernel on local lattices, finite-order continuous extension to
\(L^\times\), arbitrarily deep nontriviality, and exactness on valuation units
in both directions. In particular it does not itself repair the
characteristic-two step in the printed character argument. Every prime,
including two, remains required by the separate auxiliary-character target.

## Motivating originals

- Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p* (1998), proof of Lemma 4.7, pp.204–206.
  Source `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique* (2000), Section 3.4(3), p.449, and Section 3.6,
  Lemma 3, p.451. Source `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

These locators explain the intended consumer. The asserted algebraic target
is internal derived content, with its precise scope given above.
