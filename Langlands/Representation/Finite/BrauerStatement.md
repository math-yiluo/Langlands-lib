# Integral Brauer induction and character realization

Worker 30 states the finite complex Brauer prerequisites using Worker 18's
published finite-representation constructions. These proposition definitions
assert no proofs of Brauer's theorem or the accompanying character assertions. Its scope is a finite group in an arbitrary universe
and representations over the actual complex numbers. Thus the coefficient field
is algebraically closed and has characteristic zero; the statement does not
extend the complex theorem to arbitrary characteristic-zero fields.

## Concrete objects and intrinsic construction

`RepClass ℂ G` is the quotient of actual finite-dimensional representations by
equivariant linear isomorphism. `VirtualRep ℂ G` is its split additive group
completion, with direct-sum relations. The induction used here is the actual
Mathlib quotient-induced action, transferred through a proved coordinate
equivalence to an `FDRep`. Its action laws, finite-dimensionality, isomorphism
congruence and additivity are implemented by the definition owner.

`IrreducibleClass G` is the subtype of genuine isomorphism classes having an
irreducible representative. It is not defined by an assumed basis or by equality
of characters. The existential definition avoids choosing a representative.
`irreducibleExpansion` evaluates a finitely supported integer coefficient vector
using the canonical images of these classes in the split group.
`brauerExpansion` evaluates such a vector on the classes of actual inductions
of scalar characters `S →* ℂˣ`, for actual subgroups `S` of `G`.
Both maps use the existing integer-linear extension constructor; their values on
single generators are proved in the paired file. These are intrinsic construction
proofs, with no spanning or injectivity hypotheses.

The coefficient vectors are `Finsupp` over `ℤ`, so their support is finite and
their coefficients may be negative. No choice of rational denominators, positivity
of the coefficients, or surjectivity of an LLC map is assumed.
The definition owner's coordinate-model equivalence and
`classOfRepresentation_eq_iff` include finite-dimensional representations on any
carrier universe. Use of `FDRep ℂ G` therefore loses no such isomorphism classes;
the group universe is independent of the fixed coefficient universe.

## Seven separate conclusions

| Proposition | Exact conclusion |
| --- | --- |
| `FiniteRankOneOrderStatement` | For every subgroup, every unit character and every subgroup element, its character value raised to the subgroup order is one. |
| `FiniteInducedCharacterFormulaStatement` | The trace of the actual induced representation is `1 / |S|` times the sum over all `x ∈ G` of the source trace at `x⁻¹ g x`, with zero for conjugates outside `S`. |
| `FiniteInducedDegreeStatement` | The dimension of actual induction is `[G:S]` times the source dimension. |
| `FiniteVirtualCharacterFaithfulnessStatement` | The actual trace realization from the split representation group into complex functions is injective. |
| `FiniteIrreducibleBasisStatement` | The canonical evaluation map from the free integer module on actual irreducible classes to the split representation group is bijective. |
| `IntegralBrauerSpanningStatement` | The canonical evaluation map from signed integral rank-one subgroup induction data onto the split representation group is surjective. |
| `IntegralBrauerCharacterLatticeStatement` | The integer span of those induced trace characters equals the whole actual virtual-character image. |

`FiniteBrauerTheoryStatement` conjoins precisely these seven propositions.
Every component retains explicit finite-group hypotheses even where its target
body does not need an enumeration syntactically. They are propositions to prove,
not theorem-valued fields supplied to a structure.

The induction character formula uses the inverse on the conjugating element.
It does not replace a source character by its inverse or contragredient.
`Nat.card S` is positive because a subgroup contains the identity. There is no
division by the ambient group order in this formula.

## Original sources and correspondence

Richard Brauer, *On Artin's L-Series with General Group Characters*,
Annals of Mathematics (2) 48 (1947), no. 2, pp.502–514:

- Literature ID: `brauer-1947-artin-l-series`.
- SHA256: `7c9a789091fc6e09aeba312575b87fae1cab99ce53e842c4e378da980e21a1b5`.
- Theorem 1, printed p.503 (PDF page 3), states integral combinations of
  characters induced from linear characters of subgroups. The page image was
  inspected. The phrase “integral rational coefficients” means integers, not an
  arbitrary rational span.
- Formula (6), printed p.505, gives induction by conjugation with the character
  extended by zero outside the subgroup. Section 9, pp.513–514, proves the
  final reduction to linear characters using transitivity of induction and
  monomiality for the indicated elementary groups.

Jean-Pierre Serre, *Linear Representations of Finite Groups*, English translation
by Leonard L. Scott, Springer GTM 42 (1977):

- Literature ID: `serre-1977-linear-representations`.
- SHA256: `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
- Section 1.2, pp.4–5, describes scalar degree-one characters. Their finite-order
  bound here is the elementary derived consequence of the finite subgroup order
  and the homomorphism law.
- Section 7.1, p.54, Proposition 18 and its coset-basis proof identify actual
  induction with the group-algebra tensor module. That basis gives the stated
  degree formula. Section 7.2, pp.55–56, defines the normalized conjugation sum;
  Proposition 20(ii) identifies it with the induced representation's trace.
- Section 9.1, p.68, gives the free integer module on irreducible characters.
  Combined with complete reducibility (Section 1.4, Theorem 2, p.7) and
  character faithfulness (Section 2.3, Theorem 4, Corollary 2, p.16), it yields
  the two separately stated conclusions about the genuine split group:
  virtual-character injectivity and bijectivity of `irreducibleExpansion`.
  Those statements are derived translations, not intrinsic properties assumed
  when constructing the split group.
- Section 10.5, pp.78–79, Theorems 19–20 and Remark 1 give integral Brauer
  induction and explicitly allow negative coefficients. Applying the theorem
  to the two genuine summands of a virtual representation, then using character
  faithfulness, gives `IntegralBrauerSpanningStatement`. Realizing those
  equalities gives the character-lattice equality. Conversely, no such equality
  is presumed by either object's definition.

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Inventiones Mathematicae 139 (2000), pp.439–455:

- Literature ID: `henniart-2000-simple-proof`.
- SHA256: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Section 3.7, p.451, uses the integral linear combination of induced finite-order
  subgroup characters; Section 3.8 distinguishes its permitted character twists.
  The finite-group theorem is the input here. Pullback to actual finite Weil
  quotients and descent through weak association remain later obligations.

The cited source passages were read directly. No original theorem is installed
as an axiom or used as an assumed field to define a target.

## Published dependencies and remaining boundary

The imported construction modules are published in Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. Their Lean bytes agree with the
versions used in the original development check:

| Module under `Langlands.Representation.Finite` | Lean SHA256 |
| --- | --- |
| `Classes` | `86e04f48592f2cf0102dae07e18a294f4a9a48bed3ce5d136d1064eb2d03e514` |
| `Induction` | `a47bdbd0a4dc8d5588efa0d4eb63ef2259fdb024e7bc4266ed23ab050298d89b` |
| `Virtual` | `51b214fca45871f2eb6bd16a63e3ff0e3598bd0e0aef3b0bc9ff70674722af57` |

The prepared environment uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The paired file was recompiled
using the project's Lean service, and inspection confirmed that
`FiniteBrauerTheoryStatement` returns `Prop` with only `propext`,
`Classical.choice`, and `Quot.sound` as assumptions. The finite-group binders
and complete proposition bodies have also been inspected. The local classical
decision instance in the induced-character formula only decides subgroup
membership. Development checks do not prove any of the seven conclusions.

Worker 30 authored this proposition pair; Worker 18 authored the published
construction imports. Those imports are not republished by this contribution.
The published `Langlands.Representation.Finite.CharacterStatement` is a later
proof input, not a Lean import or an assumed proposition here.

Local Weil and supercuspidal virtual lattices, weak-association relation
independence, positive-degree sign extraction, finite witnesses, lower-rank
lifting, auxiliary extension independence and numerical surjectivity are
separate portions of the host task. This finite-group family does not complete
those portions.
