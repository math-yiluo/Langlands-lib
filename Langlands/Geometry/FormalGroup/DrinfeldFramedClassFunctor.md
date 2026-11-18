# Actual varying-Nilp functor of height-zero framed comparison classes

`comparisonClassFunctor Φ` is the actual functor on
`Nilp.{v,u} R (algebraMap 𝒪[K] R π)` with value `ComparisonClass Φ A`.
The quotient is the same original finite-chain relation of actual framed
comparisons, whose precise direct-comparison criterion was proved earlier.
Its map is the already constructed actual representative base extension,
descended through that relation. On a representative, the functor maps its
class to the class of its actual base extension.

The identity law uses the actual original framed identity comparison. The
composition law uses the actual original framed composition comparison.
Both retain the specified original target comparison, the forced residue
equality and the proved original all-test framing square. Quotient induction
establishes the corresponding class laws, which directly supply the functor
fields. No new equivalence relation or compatibility premise is introduced.

`targetClassNatTrans` retains the actual height-certified target class, and
`reducedTargetClassNatTrans` retains its actual quotient-reduced target class.
Their naturality equations are the already proved actual base-change equations
for those classes, using the same quotient functor in the second case.
`residueMapNatTrans` retains the actual descended residue algebra map and its
naturality under the induced quotient scalar map. A universe lift places the
residue-map value in the same type category as the framed classes; removing
the lift gives exactly the original residue map.

The generic `Nilp.coefficientFunctor` views the actual Nilp coefficient
algebra over the original scalar ring and maps each morphism by its actual
restricted scalar algebra map. `Nilp.residueMapFunctor` sends a Nilp algebra
to algebra maps from a supplied commutative scalar algebra into its actual
quotient; its maps compose with the actual quotient scalar maps. The quotient
functor identity/composition equations prove its functor laws.

This is an internal packaging of the existing actual height-zero framed
problem relative to a supplied height-certified frame. The local-field,
central finite-dimensional division-algebra, embedded-field and
coefficient/residue-field hypotheses are retained. Framed Nilp targets and
the frame residue field have universe u; the fixed base has universe v. Generic
coefficient and residue functors allow separate universes {u,v,w,z}. Covers
may be infinite, and coefficient maps may merge principal generators.

The full Drinfeld/Harris moduli problem, its group actions, all height
components, Weil descent, levels and representability remain further task
obligations. This construction assumes no representing object, universal
object or uniformization isomorphism.
