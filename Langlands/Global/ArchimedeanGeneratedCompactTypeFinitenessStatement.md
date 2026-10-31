# Finite compact types in an actual generated differential module

Authors: Worker 94 (original pair) and Worker 459 (verification and clarification of source scope).

The proposition
`Langlands.Global.ArchimedeanGL.GeneratedCompactTypeFinitenessStatement K n`
is an internal specialization of the Harish-Chandra admissibility step to
the published actual archimedean general linear group. It uses arbitrary
number fields in arbitrary universe and every natural rank, including zero.
All function spaces, compact types, differential operators and group
actions are the published concrete objects.

For a derivative-topology smooth function `f`, the hypotheses are finiteness
of its actual compact-group orbit span and finiteness of the actual
enveloping-center orbit of `toSmooth f`. For every actual irreducible
continuous compact type `σ`, the conclusion is finite complex dimension of
the intersection of `compactTypeSubmodule σ` with the algebraic span of
the vectors

`compactAction K n k (operator K n a f)`,

where `k` ranges over the actual standard compact subgroup and `a` over the
actual complex enveloping algebra. The action order is compact translation
after differentiation. This is the same algebraic span used in the
full-group compact-and-enveloping orbit-density statement.

Finiteness of a compact orbit concerns the input vector. It does not
assert finite multiplicity of a compact type throughout the smooth
function space. The conclusion bounds each compact type in the specified
generated module; it does not bound the whole module or assert a finite
set of types in that module. The center hypothesis is the published
finite-dimensional orbit condition, rather than a separate character
assumption. There is no growth, analyticity, connectedness, positive-rank,
projection or admissibility hypothesis.

The motivating original is Harish-Chandra, *Discrete series for semisimple
Lie groups II*, section 8, printed/PDF pages 18–19, especially the use of
algebraic admissibility on page 19 before passing to the closed group
module by continuous compact-type projections. The argument retains
section 7's connected real reductive group, actually compact analytic
subgroup, and analytic Cartan decomposition. This source is registered
as `harish-chandra-1966-discrete-series-ii` and retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Discrete series for semisimple Lie groups II- Explicit determination of the characters (1966).pdf`.

The underlying algebraic source is Harish-Chandra, *Representations of a
semisimple Lie group on a Banach space I*, Theorem 1, printed page 195 /
PDF page 11, with proof on printed pages 195–200. Its registered source is
`provided-3653f29ecd116fbb8becf37a078787d768f76f5b4bc4b075c85b5b9647628636`,
retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. AMS 75 (1953).pdf`.
That theorem concerns an induced enveloping module with a finite-dimensional
semisimple compact-Lie quotient. It gives finite generation of each simple
compact-Lie isotypic part over the ambient enveloping center, before the
finite-dimensional center quotient is applied. The proposition here is a
derived number-field GL formulation, not a verbatim transcription of that
semisimple theorem.

A proof must account for the reductive central summand, finite products of
real and complex factors, the disconnected compact factors, actual
compact-group types versus compact-Lie types, the generated module and its
common center annihilation. PBW, invariant-polynomial and covariant
finiteness arguments from the algebraic source remain substantial proof
obligations. None is supplied by defining this proposition.

Only the algebraic intersection is asserted to be finite-dimensional.
Passing its dimension bound to the closure of the generated module needs
separate continuous compact-type projections and a closure argument.
Actual convolution preservation of selected types, exact reproduction and
automorphic differential growth remain separate obligations.
