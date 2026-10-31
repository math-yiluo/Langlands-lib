# Pointed base change of compact-open Weil level towers

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), p.18 and Section III.1, pp.91–92, uses the rationalized
torsion inverse limits and monodromy-invariant orbits of compatible
frames. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`.
This module packages the existing actual pointed level pullback maps
as natural transformations between the compact-open towers. Naturality,
injectivity and the Hecke squares here are derived from Library results,
rather than quoted as separate assertions in the source.

Let `b : S' → S`, let `A/S` be an actual abelian scheme, and let
`s : Spec Ω → S'` be a field-valued point. Both bases are quasi-separated,
and the finite-étale fibre functors at `s` and `s ≫ b` are assumed to have
finite fibres. The inputs retain the named pullback-tensor, Picard
pullback and Picard universal base-change statements, dual geometry and
Poincaré evaluation packages for `A` and `A_b`, and the finite Weil
transition statement. The map `lam : A → A∨` is an actual homomorphism
into the constructed dual; its name does not assert polarization.

The base-changed map is exactly
`canonicalDualValuedBaseChange b A ... lam`, using the canonical
dual-scheme base-change comparison. The rational action on `A_b` is
`(rationalBaseChangeEnd b A).comp i`. Neither the target pairing nor its
rational algebra action is supplied independently. The same rational
`D`-module `V`, rational bilinear form `ψ`, and scalar comparison are used
on both sides.

For the full version, all positive torsion orders are required to be
invertible on both bases, the corresponding root-of-unity group schemes
are finite étale, and `TorsionFiniteEtaleStatement` remains explicit.
The away version requires these conditions only for positive orders
coprime to a natural modulus `m`. It uses the coupled comparison
`PrimeToRationalProfiniteIntegerAdeleComparison h m` and the coefficient
ring `PrimeToFiniteAdeles m`. In both versions the scalar comparison used
on the rationalized torsion inverse limit is the one used on its actual
Tate twist. The geometric pairing transport theorem is instantiated by
the proved `rationalWeilGeometricTransport`.

Write `T_A` for the actual compact-open level tower of `A` at `s ≫ b`,
and `T_b` for that of `A_b` at `s`, with the base-changed map and action
just specified. The common index category is respectively
`FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`, with the existing compact-open
transporter arrows. Its object at `K` is the set of right `K`-orbits of
actual compatible frames fixed by the actual finite-étale fundamental
group. A fixed orbit need not contain a fixed representative.

`weilAdelicCompactOpenLevelBaseChange` is a natural transformation

`B_b : T_A ⟶ T_b`.

Its component at `K` is exactly
`weilAdelicLevelBaseChange ... K.toSubgroup`, wrapped as a morphism in
the category of types. The component lemma `_app` is definitional.
The `_val` lemma identifies the underlying right-orbit value with
`weilAdelicFrameRightOrbitBaseChange ... K.toSubgroup` applied in its
inverse direction. The compatible-frame comparison runs from the
base-changed fibre to the original fibre, so its inverse is used for
pullback.

The imported pointed fixed-level map carries a class fixed under
`π₁(S,s ≫ b)` to one fixed under `π₁(S',s)`, using the actual
`fundamentalGroupMap b s (s ≫ b) rfl` and its proved equivariance.
Its underlying orbit map is an equivalence; restriction to these
different fixed subsets gives an injective map. The theorem
`weilAdelicCompactOpenLevelBaseChange_injective` supplies componentwise
injectivity. No assertion of componentwise surjectivity is made.

For every transporter arrow `f : K → L` and `q ∈ T_A(K)`, the theorem
`_arrow` states

`B_b(L)(T_A(f)(q)) = T_b(f)(B_b(K)(q))`.

The naturality proof is the existing
`weilAdelicLevelBaseChange_translate` equation applied to `f.element`
and `f.respects`. In particular it uses the actual right action
`η ↦ η ∘ g` with the condition `g⁻¹ K g ≤ L`. Naturality for the
identity-element inclusion arrow also gives compatibility with level
forgetting.

For the two Hecke lemmas additionally assume `Module.Finite ℚ V`.
This supplies the existing topological-group structure and compact open
intersection `H = K ∩ g L g⁻¹`. The `_heckeLeft` and `_heckeRight`
theorems give the displayed naturality equation for the two tower maps
`H → K` and `H → L`. They follow directly from
`NatTrans.naturality_apply`; the tower's identification of these maps
with forgetting and translation gives the corresponding Hecke squares.

`weilPrimeToAdelicCompactOpenLevelBaseChange` and its `_app`,
`_injective`, `_val`, `_arrow`, `_heckeLeft` and `_heckeRight` lemmas
implement the same construction and proof for the away tower. The
modulus need not be prime; at a prime the construction gives the
prime-to-that-prime version.

This unit constructs naturality in the compact-open level variable for
a specified pointed base change. It does not construct an unpointed
moduli functor, establish independence of a geometric point, or supply
identity and composition comparisons between the resulting tower
functors. The fixed-level identity and composition comparisons are
available separately in `WeilLevelBaseChangeCoherence`. Frame
nonemptiness, polarization of an arbitrary `lam`, and nondegeneracy are
not conclusions of this module.
