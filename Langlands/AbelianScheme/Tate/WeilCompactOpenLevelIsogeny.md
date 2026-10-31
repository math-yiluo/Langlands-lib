# Natural rational-isogeny comparisons of compact-open Weil level towers

Worker 142. This derived unit assembles the published actual
fixed-level rational-isogeny equivalences into natural isomorphisms of
the full and away compact-open Weil level towers. Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
printed p.18 and Section III.1, pp.90–92, gives the rational-isogeny
convention, invariant-orbit levels, isogeny relation and right level
action motivating this construction. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`. The functor
packaging and coherence laws here are deductions from existing Library
constructions, rather than separate geometric existence assertions.

The endpoints `A`, `B` and, for composition, `C` are actual abelian
schemes over the same quasi-separated scheme `S`. Each retains its
constructed dual, dual geometry, inverse Poincaré bundle and evaluation
isomorphism, actual integral map `lam` to that dual, and rational algebra
action `i : D →ₐ[ℚ] Rationalization.End A`. The common rational module
`V` has a `D`-action and bilinear form `ψ`. The maps `lam` are not
assumed to be polarizations in this general interface.

The named pullback-tensor and Picard pullback coherence inputs, finite
Weil transition input, and dual-map additivity inputs for the ordered
pairs used remain explicit. The actual pairing functoriality and
geometric compatibility are instantiated by the published proofs
`rationalWeilFunctoriality` and `rationalWeilGeometricTransport`.
Neither pairing identity is an additional hypothesis of the new
definitions. Those proofs retain the construction and geometry
hypotheses just listed.

Fix a field-valued point `s : Spec Ω → S` and finite-fibre witnesses for
its actual finite étale cover fibre functor. Retain
`TorsionFiniteEtaleStatement`, invertibility of the selected positive
torsion orders on `S`, and finite étaleness of the corresponding
root-of-unity group schemes. The full version selects all positive
orders. The away version selects orders coprime to a natural modulus
`m` and uses `PrimeToRationalProfiniteIntegerAdeleComparison h m`.
The same scalar comparison acts on the actual rationalized torsion
inverse limit and on its actual section-ring Tate twist. The away
comparison is coupled to the full comparison `h`; both appear in the
away interface. No roots of unity, independent pairing or independent
monodromy action are supplied.

Write `T_A`, `T_B` and `T_C` for the actual compact-open towers at `s`.
Their common index category is `FiniteAdelicScalarExtensionLevel D V ψ`
or `PrimeToScalarExtensionLevel D V ψ m`. At a compact open `K`, the
tower consists of right `K`-orbits of actual compatible frames fixed by
the actual geometric fundamental group. Fixedness is imposed on the
orbit class and does not require a fixed representative.

Let `e : Rationalization.of A ≅ Rationalization.of B` be an invertible
rational homomorphism and `q : ℚˣ`. The hypotheses are that `e`
intertwines the given rational algebra actions and that the actual
rational dual pullback satisfies

`e^∨ lamB e = q lamA`.

The latter is the published predicate `IsRationalDualPullbackMultiple`,
using the actual constructed `dualHom0` and rationalized integral maps.
It is a geometric homomorphism equation, rather than a supplied equation
between arbitrary bilinear forms.

`weilAdelicCompactOpenLevelIsogeny` constructs `T_A ≅ T_B`. At `K` its
component is the published equivalence
`weilAdelicLevelIsogeny ... K.toSubgroup q e`, converted to an
isomorphism in the category of types. That equivalence uses the actual
rational Tate map of `e` on compatible frames and descends its commuting
actions to fixed orbit classes. `NatIso.ofComponents` assembles the
components; naturality follows from the published
`weilAdelicLevelIsogeny_translate` equation with the transporter arrow's
element and subgroup condition.

The `_hom_app` and `_inv_app` lemmas identify the components with the
published fixed-level equivalence and its inverse by definitional
equality. The `_arrow` theorem is its elementwise naturality equation:
for every transporter arrow `a : K → L`,

`Isogeny(L)(T_A(a)(x)) = T_B(a)(Isogeny(K)(x))`.

Thus it includes level forgetting and both Hecke legs whenever their
existing compact-open intersection construction applies. The underlying
right convention is precomposition by `g` with
`g⁻¹ K g ≤ L`. No additional subgroup or action compatibility is assumed.

The `_refl` theorem identifies the actual identity rational isogeny,
with the derived unit multiplier equation and identity intertwining
equation, with `Iso.refl T_A`.

`weilAdelicCompactOpenLevelIsogenyComp` applies direct isogeny transport
to `e.trans f` with multiplier `q*r`. Its algebra intertwining equation
comes from `rationalIntertwines_comp`; its actual geometric multiplier
equation comes from `IsRationalDualPullbackMultiple.comp`. The theorem
`_IsogenyComp_eq_trans` identifies this direct natural isomorphism with
successive transport, first by `e` and then by `f`. The intermediate
abelian scheme and all its geometry are shared between the two maps.

`weilAdelicCompactOpenLevelIsogenyInverse` applies direct transport to
`e.symm` with multiplier `q⁻¹`. Its reverse intertwining and geometric
multiplier equations are derived by `rationalIntertwines_inverse` and
`IsRationalDualPullbackMultiple.inv`. The theorem `_Isogeny_symm`
identifies it with the inverse natural isomorphism of forward transport.
No additional identity, composite or inverse pairing hypothesis is used.

Each coherence proof applies isomorphism and natural-transformation
extensionality, then applies the corresponding published fixed-level
equivalence identity to the element at `K`. The fixed-level proofs
already descend the compatible-frame identities through the actual
orbit quotient.

The declarations beginning `weilPrimeToAdelicCompactOpenLevelIsogeny`
implement the same constructions and laws for the away tower, with the
order and scalar hypotheses specified above. The modulus need not be
prime; at a prime it gives the prime-to-that-prime version.

This unit compares actual towers for specified rational isogenies over
one base and point. It does not assert polarization, positivity,
nondegeneracy or existence of compatible frames for arbitrary
dual-valued maps. It constructs no PEL moduli functor or comparison
between different bases. The independent base-change and geometric-point
tower comparisons are separate modules.
