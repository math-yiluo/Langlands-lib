# Pointed base change and rational isogenies of actual Weil level towers

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), p.18 and Section III.1, pp.91–92, uses rationalized
torsion inverse limits, compatible frames, monodromy-invariant right
orbits, and transport by rational isogenies. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`. This module
derives the commutation of the Library's actual pointed base change
and actual rational-isogeny transport. The mixed maps and their
commuting squares are consequences of those constructions, rather
than separate theorems quoted from Harris–Taylor.

Let `b : S' → S` be a morphism between quasi-separated schemes, let
`A` and `B` be abelian schemes over `S`, and let
`s : Spec Ω → S'` be a field-valued point. Write `A_b` and `B_b`
for their actual base changes. No algebraic closedness assumption on
`Ω` is needed for this conditional pointed interface.

The inputs retain the named pullback-tensor coherence, Picard pullback,
and Picard universal base-change statements, actual dual schemes and
their geometry, and Poincaré evaluation data for the relevant schemes.
The integral homomorphisms `lamA : A → A∨` and `lamB : B → B∨`
land in the dual abelian schemes constructed from those data. Their
names do not assert that they are polarizations.

The new homomorphisms are exactly
`canonicalDualValuedBaseChange b A ... lamA` and
`canonicalDualValuedBaseChange b B ... lamB`. Thus their pairings use
the actual canonical dual-scheme base-change comparison. The new
rational algebra actions are
`(rationalBaseChangeEnd b A).comp iA` and
`(rationalBaseChangeEnd b B).comp iB`, for the given rational
`D`-algebra actions `iA` and `iB`. The rational `D`-module `V` and
rational bilinear form `ψ` are shared by all four frame types.

Let `e : Rationalization.of A ≅ Rationalization.of B` be an invertible
rational homomorphism and `q : ℚˣ`. The original action intertwining
condition is

`e ∘ iA(d) = iB(d) ∘ e`.

`rationalIntertwines_baseChange` proves this condition for the actual
pulled-back actions and `rationalBaseChangeIso b e`. It applies the
actual rational Hom pullback to the original equation and simplifies
using preservation of composition and the definitions of pullback on
endomorphisms and isomorphisms. It needs none of the dual data.

Isogeny transport uses actual geometric multiplier identities. The
original hypothesis `hqe` is
`IsRationalDualPullbackMultiple ... (q : ℚ) e.hom
(Rationalization.ofHom lamA) (Rationalization.ofHom lamB)`.
It expresses

`e∨ ∘ lamB ∘ e = q lamA`

in the rational Hom groups, with `e∨` constructed by `dualHom0`.
The square additionally assumes the corresponding identity `hqeb`
for `rationalBaseChangeIso b e` and the two specified canonical
base-changed integral maps. The same scalar `q` is used. Dual-map
additivity is retained for both pairs of schemes. This unit proves
neither multiplier stability under pullback nor a new duality theorem;
the new multiplier equation is an explicit geometric hypothesis.

The finite Weil-transition statement and the rational
profinite-integer/finite-adele comparison remain explicit. The full
coefficient ring is `Global.FiniteAdeles ℚ`. The away version uses
`Global.PrimeToFiniteAdeles m` and the coupled comparison
`PrimeToRationalProfiniteIntegerAdeleComparison h m`, with the
torsion index restricted to positive orders coprime to `m`. The
modulus may be any natural number; a prime gives the usual
prime-to-that-prime version. Each comparison is shared by the actual
rationalized Tate module and its actual Tate twist. Compatibility of a
frame includes existence of a twist trivialization; the construction
does not choose roots of unity or replace the twist action by a
trivial action.

Write `F_A`, `F_B`, `F_Ab`, and `F_Bb` for the actual compatible-frame
types at `s ≫ b` or `s`, respectively. The published base-change
equivalences have directions
`C_A : F_Ab ≃ F_A` and `C_B : F_Bb ≃ F_B`.
The published isogeny equivalences have directions
`I : F_A ≃ F_B` and `I_b : F_Ab ≃ F_Bb`.
The theorem `weilAdelicFrameIsogeny_baseChange` states

`C_B (I_b η) = I (C_A η)`.

Subtype extensionality and linear-map extensionality reduce this to
`rationalBaseChange_iso`, the published naturality of the actual
rational Tate maps. The `_baseChange_symm` theorem gives the inverse
base-change direction
`I_b (C_A⁻¹ η) = C_B⁻¹ (I η)` by injectivity of `C_B`.

`weilAdelicFrameIsogenyBaseChange` is the mixed equivalence
`C_B⁻¹ ∘ I : F_A ≃ F_Bb`. Its `_eq` theorem identifies it with
`I_b ∘ C_A⁻¹`. The definition itself needs only the original
multiplier and the new target dual data. The alternative expression
and square additionally need the new source dual data, new
dual-map additivity, and new multiplier hypothesis.

For levels, retain the finite-fibre hypotheses on the actual
finite-étale fibre functors at `s` and `s ≫ b`, the
`TorsionFiniteEtaleStatement`, invertibility of every selected torsion
order on both bases, and finite étaleness of the corresponding
root-of-unity group schemes. In the full case the selected orders are
all positive integers; in the away case they are those coprime to
`m`. The geometric pairing transport and rational Weil functoriality
inputs of the imported constructions are instantiated by the
published proofs `rationalWeilGeometricTransport` and
`rationalWeilFunctoriality`.

For a subgroup `U` of the appropriate scalar-extension similitude
group, let `L_A(U)` denote the right `U`-orbits in `F_A` fixed by the
actual finite-étale fundamental group, and use analogous notation for
the other schemes. Fixedness is a property of the orbit class; a
fixed representative is not required. The pointed level maps
`P_A : L_A(U) → L_Ab(U)` and `P_B : L_B(U) → L_Bb(U)` use the inverse
frame comparisons and the actual fundamental-group pullback map.
The actual rational isogenies give fixed-level equivalences `J` and
`J_b`. The theorem `weilAdelicLevelIsogeny_baseChange` proves

`P_B (J x) = J_b (P_A x)`.

Its proof installs the four published right actions, removes the
fixedness subtype, and uses quotient induction on the underlying
right orbit. Applying the right-orbit constructor to the inverse
frame square proves the desired equality. In particular, this is
descent through the actual orbit quotient.

`weilAdelicLevelIsogenyBaseChange` is `P_B ∘ J`; its `_eq` theorem
identifies it with `J_b ∘ P_A`. As with the mixed frame equivalence,
the definition needs only the original multiplier, whereas the
reverse-route equality also needs the new multiplier.

Write `T_A`, `T_B`, `T_Ab`, and `T_Bb` for the corresponding actual
compact-open level towers. Their common index category is
`FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`. The definition
`weilAdelicCompactOpenLevelIsogenyBaseChange` is the natural
transformation

`T_A ⟶ T_Bb`

obtained by composing the original natural isogeny isomorphism with
the target's pointed base-change natural transformation. Its component
at `K` is the mixed fixed-level map at `K.toSubgroup`. Naturality
therefore holds for every existing transporter arrow, including level
forgetting and the Hecke legs whenever their compact-open
intersection construction applies. The right-action convention is
`η ↦ η ∘ g` with condition `g⁻¹ K g ≤ L`. This module assumes no
finite-dimensionality of `V` beyond what the imported constructions
need; constructing those compact-open intersections uses their
separate finite-dimensionality hypothesis.

`weilAdelicCompactOpenLevelIsogeny_baseChange` identifies the two
routes as natural transformations:

`Isogeny(e).hom ≫ BaseChange(B) =
  BaseChange(A) ≫ Isogeny(rationalBaseChangeIso b e).hom`.

Natural-transformation extensionality and function extensionality at
`K` reduce the proof to the fixed-level square.
`weilAdelicCompactOpenLevelIsogenyBaseChange_eq` supplies this
alternative expression for the named mixed transformation.
The mixed tower map is a natural transformation; its pointed
base-change factor is not asserted to be surjective.

All the frame, fixed-level, and compact-open constructions and squares
have analogous declarations beginning `weilPrimeToAdelic` with the
selected orders and coefficient comparison described above.

These are derived transport constructions on the actual Tate
modules, Weil pairings, and monodromy-invariant orbits. They do not
prove positivity or polarization of the supplied integral maps,
nondegeneracy, rank, or nonemptiness of the frame types. They add no
unpointed moduli functor or base-point-independence assertion.
