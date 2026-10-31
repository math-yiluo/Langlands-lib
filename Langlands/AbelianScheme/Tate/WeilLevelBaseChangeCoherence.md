# Identity and composition of actual Weil-compatible fixed-level base change

This module constructs identity and direct-to-successive comparisons on the
existing `WeilAdelicLevel` and `WeilPrimeToAdelicLevel` sets and proves the
corresponding pointed pullback equations. These are sets of monodromy-fixed
right subgroup orbits of actual compatible frames. Fixedness is a property of
the orbit class, rather than a condition on a chosen representative.

## Data and geometric hypotheses

Let `A/S` be an abelian scheme with quasi-separated base. The tensor/Picard
statements, dual representability and geometry, evaluation line bundle and
evaluation isomorphism, and relative finite-Weil transition statement remain
explicit inputs. The map `lam` is an actual homomorphism into the constructed
dual abelian scheme; an arbitrary such map is not asserted to be a
polarization. The rational action is `i : D →ₐ[ℚ] End0 A`, and `V` has
compatible rational and `D`-module structures and a rational bilinear form `ψ`.

The scalar ring `R` is `Global.FiniteAdeles ℚ` in the full case and
`Global.PrimeToFiniteAdeles m` in the away case. The same rational scalar
comparison `h`, or the same coupled `hAway`, is used throughout for the actual
Tate modules and twists. The away parameter `m` is an arbitrary natural
number; the selected positive orders satisfy `Nat.Coprime n m`. Frames have
source `R ⊗[ℚ] V`, are linear over `D ⊗[ℚ] R`, and satisfy the existing
twist-valued form-compatibility predicate. That predicate permits a twist
trivialization existentially without choosing one for monodromy.

The geometric point is `s : Spec Ω ⟶ S`, with `Ω` a field in the scheme
universe. The witness `hs` asserts that all finite étale cover fibres at `s`
are finite. The acting group is the actual `FundamentalGroup s hs`.
`htor : TorsionFiniteEtaleStatement` is retained, as are invertibility of
every selected order on the relevant bases and finite/étale instances for
the selected roots-of-unity group schemes. The existing monodromy actions
and level types receive the published proof `rationalWeilGeometricTransport`,
so no additional geometric-transport assertion is assumed here.

Identity and composition comparisons also take
`PicardZeroUniversalBaseChangeStatement`. Identity uses dual
geometry/evaluation packages for both `A` and `id* A`. Composition uses
`b : S' ⟶ S` and `c : S'' ⟶ S'`, with all three bases quasi-separated, and
four packages: for `A`, `b* A`, `(c ≫ b)* A`, and `c* (b* A)`. Their
dual-valued homomorphisms are the actual canonical direct or successive
pullbacks of `lam`, and their algebra actions use `rationalBaseChangeEnd`.
All base points used in a pointed pullback have explicit finite-fibre
witnesses; all three bases have the selected-order invertibility and
roots-of-unity hypotheses needed by those pullbacks.

## Point equality and identity

`weilAdelicLevelPointEq` eliminates an equality `s = t` and gives the
reflexive equivalence of the resulting fixed level sets. Its `_val` theorem
identifies the underlying orbit map with
`weilAdelicFrameRightOrbitPointEq`. After equality elimination, the proof
reduces the left side to the original class and uses quotient induction.
The `_symm_val` theorem identifies inverse transport by applying the
forward orbit equivalence, rewriting `_val`, and cancelling inverses.
The away declarations have prefix `weilPrimeToAdelicLevel`.

`weilAdelicFrameBaseChangeId_monodromy` proves that the actual frame
identity comparison intertwines the two monodromy actions at `s`.
Subtype and linear-map extensionality reduce the equation to one on
vectors. The published pointwise identity-comparison formula reduces it to
`rationalMonodromy_map` for `(baseChangeIdIso A).hom`.

`weilAdelicLevelBaseChangeId` uses `InvariantOrbit.equiv` with the identity
equivalence of `FundamentalGroup s hs`, the actual compatible-frame
identity equivalence, its right equivariance, and this monodromy equation.
It goes from the fixed levels of `id* A` at `s` to those of `A` at `s`.
Its `_val` and `_symm_val` equations identify the forward and inverse
underlying right-orbit comparisons definitionally.

`weilAdelicLevelBaseChange_id` says that pointed pullback along `𝟙 S`,
followed by this identity comparison, equals point transport along
`Category.comp_id s`. Subtype extensionality and the value formulas reduce
the proof to the published frame-orbit identity square, evaluated on the
inverse base-change image of the original orbit. Inverse cancellation
finishes the proof. All these constructions and proofs also appear away
from `m`.

## Composition and pointed pullback

`weilAdelicFrameBaseChangeComp_monodromy` intertwines monodromy on the
direct-pullback compatible frames and on the successive-pullback compatible
frames at the same point `s` of `S''`. The proof again compares the
underlying maps pointwise and applies `rationalMonodromy_map`, now to
`(baseChangeCompIso b c A).hom`, using the published frame-comparison
application formula.

`weilAdelicLevelBaseChangeComp` restricts this direct-to-successive
comparison to fixed right orbits by `InvariantOrbit.equiv` and the identity
equivalence of the actual fundamental group at `s`. Its `_val` and
`_symm_val` equations give precisely the existing forward and inverse
frame-orbit composition comparisons.

Write `B_b` for the pointed fixed-level pullback along `b`, `C` for this
direct-to-successive comparison, and `T` for point transport from
`s ≫ (c ≫ b)` to `(s ≫ c) ≫ b`. Then
`weilAdelicLevelBaseChange_comp` proves, for a fixed orbit `q` at
`(s ≫ c) ≫ b`,

```text
C (B_(c ≫ b) (T⁻¹ q)) = B_c (B_b q).
```

The proof first removes the fixedness proof fields. The value equations
for `C`, direct pullback, and inverse point transport reduce the left side
to the inverse orbit-comparison square. The private lemma
`inverse_level_comparison_square` derives that inverse square from
`weilAdelicFrameRightOrbitBaseChange_base_comp`: apply injectivity of the
successive forward comparisons and cancel inverse equivalences. The
values of the two successive pointed pullbacks agree definitionally with
their inverse orbit comparisons. The away construction and proof use
the same argument with the coupled `hAway`.

## Hecke maps and forgetting

The fixed-level identity and composition comparisons both commute with
`InvariantOrbit.translate g hg` whenever the source and target subgroups
`U`, `U'` satisfy `∀ u ∈ U, g⁻¹ * u * g ∈ U'`. The right action is source
precomposition, `eta * g = eta ∘ g`. The proofs remove the subtype
fixedness fields and apply the corresponding established right-orbit
translation equations. The `_forget` equations specialize translation
to `g = 1` and `U ≤ U'`.

These statements allow arbitrary subgroups of
`ScalarExtensionSimilitudes D V R ψ`; they require no normality or
topology. They have parallel full and away forms.

## Provenance and scope

The constructions are derived from
[WeilFrameBaseChangeCoherence](WeilFrameBaseChangeCoherence.md),
[WeilLevelBaseChange](WeilLevelBaseChange.md),
[RationalMonodromy](RationalMonodromy.md), and the generic
`InvariantOrbit.equiv` in
[OrbitTransport](../../Shimura/PEL/OrbitTransport.md).
The new equations use the actual geometric comparison maps, rather than
assuming new identity or composition assertions.

Harris–Taylor (2001), printed p.18 / PDF p.26, defines the full and away
Tate rationalizations. Section III.1, printed pp.91–92 / PDF pp.99–100,
supplies the compatible-frame, invariant-orbit and right Hecke conventions.
The coherence equations here are deductions from the Library constructions
implementing that framework, not additional quoted theorems from that
passage.

The equivalences compare levels on canonically isomorphic abelian schemes
over the same base. Arbitrary pointed ground-base pullback remains the
previously constructed injective map; no surjectivity is inferred. This
module does not establish frame existence, alternation or nondegeneracy of
an arbitrary form, a polarization property for `lam`, compact-open
topology, or canonical independence from an unpointed geometric base
point.
