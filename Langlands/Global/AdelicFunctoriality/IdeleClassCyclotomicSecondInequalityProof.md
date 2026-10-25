# Conditional cyclotomic reduction of the actual second inequality

The theorem
`Langlands.Global.AdelicFunctoriality.ideleClassCyclotomicSecondInequalityReduction.{u,v}`
proves exactly the existing proposition
`IdeleClassCyclotomicSecondInequalityReduction.{u,v}`. Its type is the implication

```text
IdeleClassNormIndexFinite.{u,v} →
IdeleClassNormTower.{u,v,v} →
IdeleClassKummerPrimeDegreeSecondInequality.{v,v} →
IdeleClassPrimeDegreeSecondInequality.{u,v}.
```

The conclusion concerns the existing actual `ideleClassNorm`: for a Galois extension
of number fields of prime degree, its norm-image index divides that degree.
The fields in the conclusion retain independent universes `u` and `v`, and all
prime degrees, including two, are covered. The three displayed antecedents remain
explicit inputs. This theorem does not establish any of them or the unconditional
second inequality. It adds no hypothesis on roots of unity, cyclicity, auxiliary
fields or norm base change.

The implemented proof is a direct application of
`ideleClassCyclotomicSecondInequalityReduction_holds.{u,v}` from
[CyclotomicSecondInequalityReduction](CyclotomicSecondInequalityReduction.md).
That imported theorem already has the exact target type; the new theorem simply
exposes it in a dedicated proof module.

For context, the imported proof puts `p = [L : K]`, takes
`M = CyclotomicField p L`, and takes the intermediate field `E = K(ζ)` inside `M`.
Both auxiliary carriers lie in `Type v`. It proves
`0 < [E : K] ≤ φ(p) < p`, hence coprimality with `p`; linear disjointness gives
`[M : E] = p`, and the Galois compositum lemma gives that `M/E` is Galois.
The chosen root belongs to `E`, so the Kummer antecedent applies there.
The finite degree-power bound gives
`index N(L/K) ∣ p^r` and `index N(E/K) ∣ [E : K]^s`.
The two norm towers then give
`index N(L/K) ∣ [E : K]^s * p`. Coprimality cancels the first factor and yields
`index N(L/K) ∣ p`. These constructions and lemmas are imported unchanged.
The proof uses no global reciprocity, global fundamental class, global
idele-class first-cohomology vanishing or general second inequality.

The mathematical source is Artin and Tate, *Class Field Theory* (2009),
VI §1, the two lemmas and Reduction 2, printed pp.20–21 (PDF pp.29–30),
registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata dated January 23, 2009 (PDF p.202) contain no correction to
this passage. The original and errata were read. This wrapper is derived
packaging of the published formalization of that argument; it does not use
Milne's alternative norm base-change argument.

Worker 107 authored this wrapper and its explanation. Worker 269 authored the
underlying cyclotomic construction and proof, with Worker 123 contributing its
two tower-index lemmas. Their existing published module is reused by import;
no draft source is copied or adapted here.
