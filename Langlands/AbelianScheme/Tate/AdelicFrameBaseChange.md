# Pointed base change of ambient adelic Tate frame orbits

This module constructs full and prime-to-modulus frame comparisons for actual
abelian-scheme pullback. They induce equivalences of underlying right orbit
sets, commute with level translations and level forgetting, and satisfy the
rational-isogeny square on frames. The orbits in this module have no geometric
invariance or Weil-form condition.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 (PDF p.26), defines the full and away Tate modules using
actual torsion points, their rationalizations, and isogenies as invertible
rational homomorphisms. Section III.1, printed p.91 (PDF p.99), uses linear
frames over the full endomorphism/finite-adele tensor algebra, invariant right
orbits, and the convention that a level translation precomposes a frame with
an element of the similitude group. Printed p.92 (PDF p.100) supplies the
prime-to-p version.

Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The constructions here are derived infrastructure for those conventions.
They use the actual pullback and tensor-linear Tate comparisons of
`Tate.AdelicBaseChange`, the existing ambient frames and right actions, and the
quotient helper `Shimura.PEL.OrbitEquiv`. The cited pages do not state the
implementation lemmas below. In particular, the arbitrary source action in
this module is an algebraic helper for the eventual similitude specialization.

## Parameters and actual carriers

Let `b : S' ⟶ S`, let `A` be an abelian scheme over `S`, and let
`s : Spec Ω ⟶ S'`, for a field `Ω`. No algebraic-closure hypothesis is needed
for this comparison; geometric points are an intended specialization. Let `D`
be a rational algebra and `i : D →ₐ[ℚ] End0 A`. Write

- `b*A = (AbelianScheme.baseChange b).obj A`;
- `i' = (AbelianScheme.rationalBaseChangeEnd b A).comp i`;
- `R = D ⊗[ℚ] Global.FiniteAdeles ℚ` in the full case;
- `Rᵐ = D ⊗[ℚ] Global.PrimeToFiniteAdeles m` in the away case.

The source `V` is an additive group with an `R`-module, or respectively an
`Rᵐ`-module, structure. The module uses the existing actual rational Tate
carrier, namely rationalization of the coherent inverse limit of torsion
points. In the away case the positive orders are restricted by
`Nat.Coprime n m` before rationalizing. Taking `m` prime gives the requested
prime-to-p variant.

The full comparison retains a common explicit
`h : Global.RationalProfiniteIntegerAdeleComparison`. The away comparison
retains one common `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.
These are scalar-comparison hypotheses, not arbitrary equivalences between
Tate modules. The constructed tensor actions use the actual `End0` action
and the finite-adelic scalar actions determined by these hypotheses. This
module does not prove the hypotheses or independence from their witnesses.

## Frames and their underlying right orbits

`adelicFrameBaseChange` is the equivalence

\[
 \operatorname{AdelicFrame}(b^*A,i',s)
   \longrightarrow \operatorname{AdelicFrame}(A,i,sb),\qquad
 \eta\longmapsto C_b\circ\eta,
\]

where `C_b = finiteAdeleAlgebraBaseChange b (Over.mk s) (fun _ => True) A i h`.
Its inverse postcomposes with `C_b.symm`; hence the inverse is the direction
used to pull back a frame on `A`. The `_apply` and `_symm_apply` lemmas identify
these maps pointwise with the actual `rationalBaseChange` and its inverse.
The codomain test scheme is definitionally the point `s ≫ b`.

For a group `G`, a representation `ρ : G →* (V ≃ₗ[R] V)`, and a subgroup `U`,
`AdelicFrameRightOrbit` abbreviates the right orbit set using the existing
action `η · g = η ∘ ρ(g)`. It imposes no left fixedness condition. The theorem
`adelicFrameBaseChange_right` proves that postcomposition with `C_b` commutes
with this source action, by evaluating both linear equivalences on each
vector. `adelicFrameRightOrbitBaseChange` applies `RightOrbit.equiv` to obtain
an equivalence of these orbit sets. Its `_mk` and `_symm_mk` formulas are

\[
 [\eta]\longmapsto[C_b\circ\eta],\qquad
 [\theta]\longmapsto[C_b^{-1}\circ\theta].
\]

If `g⁻¹ U g ⊆ U'`, `_translate` proves that this comparison commutes with
`RightOrbit.translate g hg`, which sends `[η]` to `[η ∘ ρ(g)]` at level `U'`.
It applies the existing equivariant-map translation lemma. `_forget` is its
specialization to `g = 1` and `U ≤ U'`; its statement uses the identity
transporter directly. Thus forgetting changes the subgroup while retaining
the representative frame.

`primeToAdelicFrameBaseChange`, `PrimeToAdelicFrameRightOrbit`, and
`primeToAdelicFrameRightOrbitBaseChange`, with the correspondingly prefixed
application, inverse, equivariance, representative, translation and forgetting
lemmas, give the same constructions over `Rᵐ` using
`primeToFiniteAdeleAlgebraBaseChange`. The inverse-limit predicate in the
underlying map formulas is exactly `Nat.Coprime n m`.

## Compatibility with rational isogenies

Suppose `e : Rationalization.of A ≅ Rationalization.of B` intertwines `i`
and an action `iB` in the existing categorical composition convention:
`i(d) ≫ e.hom = e.hom ≫ iB(d)`. The theorem
`rationalBaseChange_intertwines` proves that the actual pulled-back rational
isogeny intertwines the actual pulled-back actions. It applies
`rationalBaseChangeHom` to the assumed equation and uses preservation of
composition. No new intertwining hypothesis on the pullbacks is introduced.

`adelicFrameBaseChange_isogeny` and
`primeToAdelicFrameBaseChange_isogeny` prove the square

\[
 C_{b,B}\circ V(b^*e)\circ\eta
   =V(e)\circ C_{b,A}\circ\eta.
\]

The Lean statements use the constructed frame isogeny equivalences and the
proved pullback intertwining. Their proofs reduce by linear-equivalence
extensionality to `rationalBaseChange_homMap`. These are frame equations;
no separate isogeny-square theorem on invariant orbits is asserted here.

## Scope

All comparisons are algebraic and permit arbitrary schemes, base morphisms,
subgroups and source representations. They do not require finite étaleness,
invertibility of torsion orders, or a topology on rational Tate modules.
The module does not assert existence of a frame. It also does not construct
the map on geometric fundamental groups, prove monodromy compatibility,
restrict to Weil-form similitudes, or define base change on invariant PEL
levels. The equivalence on unrestricted orbits alone does not imply an
equivalence on invariant orbits for arbitrary base change. Identity and
composition laws at the frame level, and independence of geometric base
point, remain separate obligations.
