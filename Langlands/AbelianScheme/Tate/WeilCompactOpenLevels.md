# Compact-open towers of actual Weil-compatible Tate levels

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), p.18 and Section III.1, pp.91–92, defines full and
prime-to-p levels using monodromy-invariant orbits of pairing-compatible
frames. Page 91 also specifies level forgetting and right translation.
The source is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`. This module packages
the existing actual Weil-compatible fixed-orbit sets as functors on the
compact-open transporter category. The categorical packaging, application
formulas and Hecke spans are derived from Library constructions.

Let `A/S` be an actual abelian scheme, with `S` quasi-separated, and let
`s : Spec Ω → S` be a field-valued point whose finite-étale fibres are finite.
The explicit inputs are the named pullback-tensor coherence and Picard
pullback statements, the dual-scheme geometry and Poincaré evaluation
package, the finite Weil transition statement, and an actual homomorphism
`polarizationMap` from `A` to its constructed dual. The latter parameter
does not assert that this homomorphism is a polarization. Let `D` be a
rational algebra, `i : D →ₐ[ℚ] Rationalization.End A`, and `V` a rational
`D`-module with compatible scalar tower. Let `ψ` be a rational bilinear form.

The full construction retains the scalar comparison
`RationalProfiniteIntegerAdeleComparison`, the torsion finite-étaleness
statement, invertibility on `S` of every selected positive torsion order,
and finite-étaleness of the corresponding root-of-unity group schemes.
The away construction selects the orders coprime to a natural modulus `m`,
uses `PrimeToFiniteAdeles m`, and retains a coupled
`PrimeToRationalProfiniteIntegerAdeleComparison h m`. The same scalar
comparison acts on both the actual Tate module and its twist. The full
Tate vector space is the rationalization over `ℤ` of the integral torsion
inverse limit, as in Harris–Taylor p.18.

The new definitions instantiate geometric pairing transport with the
proved `rationalWeilGeometricTransport` theorem. They do not introduce an
additional geometric transport hypothesis. The other displayed theorem
and scalar-comparison dependencies remain explicit.

For `R = FiniteAdeles ℚ` or `PrimeToFiniteAdeles m`, the source group is
`ScalarExtensionSimilitudePoints D V R ψ`. This is the named topological
carrier of the existing `D ⊗[ℚ] R`-linear similitude group of
`ψ.baseChange R` on `R ⊗[ℚ] V`. Its topology observes the forward operator,
the actual inverse operator, and the unit multiplier, using the canonical
`R`-module topology on the scalar extension. The indices are respectively
`FiniteAdelicScalarExtensionLevel D V ψ` and
`PrimeToScalarExtensionLevel D V ψ m`; each is an actual compact open
subgroup with an accessor into the original algebraic group.

`WeilAdelicCompactOpenLevel K` is exactly `WeilAdelicLevel K.toSubgroup`
with the proved geometric transport theorem installed.
`WeilPrimeToAdelicCompactOpenLevel K` is its away counterpart. In each
case a frame is an actual tensor-linear isomorphism into the rationalized
torsion inverse limit. Its compatibility predicate existentially
quantifies a linear trivialization of the actual Tate twist taking the
standard scalar-extended form to the actual Weil pairing. The pairing is
the imported Poincaré construction pulled back by `polarizationMap` in
the second variable. A trivialization is not part of a frame.

The level set consists of right subgroup orbits of those frames fixed by
the actual automorphism group of the finite-étale fibre functor.
Monodromy acts on both the Tate module and the twist and commutes with
source precomposition. A fixed orbit need not have a fixed representative.

`weilAdelicCompactOpenLevelTower` and
`weilPrimeToAdelicCompactOpenLevelTower` are functors from the corresponding
compact-open transporter category to `Type (max u w)`. They specialize
`InvariantOrbit.tower` to the actual frame, monodromy and commuting actions.
For an arrow `f : K → L`, its element `g` satisfies

`g⁻¹ K g ≤ L`.

The arrow acts by the existing fixed-level translation, sending the orbit
of `η` to that of `η ∘ g`. The `_obj`, `_map` and `_map_val` lemmas identify
the objects, maps and underlying right-orbit maps definitionally.
The functor identity and composition laws come from the proved
`InvariantOrbit` translation laws: first `g`, then `k`, acts by `g * k`.
The `_inclusion` lemmas identify the arrow with element one associated
to `K ≤ L` with the existing fixed-level forgetting map.

For the Hecke definitions additionally assume `Module.Finite ℚ V`.
This supplies the topological-group instance on the source similitudes
and hence the existing compact open intersection level

`H = K ∩ g L g⁻¹`.

`weilAdelicCompactOpenHeckeLeft K L g` maps the actual level set at `H`
to the one at `K`; `weilAdelicCompactOpenHeckeRight K L g` maps it to
the one at `L`. They are the tower maps on `CompactOpenLevel.heckeLeft`
and `CompactOpenLevel.heckeRight`. The two `_eq` lemmas identify the
first leg with forgetting and the second with translation by `g`.
The prime-to-modulus definitions and formulas have the same meaning.
All these identifications are proved by definitional equality with the
existing translation and forgetting constructions.

The tower itself requires no finite-dimensionality, involution,
faithfulness, alternation or nondegeneracy hypotheses. In the intended
PEL application these come from `RationalPELConditions`, whose
`finite_module` consequence supplies the extra Hecke hypothesis.
The present module constructs towers for a fixed actual abelian scheme
and point; it does not construct the PEL moduli scheme or prove
nonemptiness of any frame space. Away from a prime this gives the
prime-to-that-prime tower in the source; the Lean definition also allows
an arbitrary natural modulus. A topology on the frame or level set,
canonical unpointed base-point change, and pointed base-change natural
transformations are outside this unit.
