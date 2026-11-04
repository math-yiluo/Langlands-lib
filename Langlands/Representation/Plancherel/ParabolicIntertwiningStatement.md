# Conditional finite-length standard intertwining target

`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement` is a
Prop-valued **statement**, with field universe `u`, inducing-carrier universe
`uV`, and independent representative-carrier universe `uW`. It states the
finite-length convergence and rationality assertion for the actual standard
integral, conditional on the structural data listed below. This file does
not prove that assertion.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`, source SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
IV.1, printed pp.276–278 / PDF pp.42–44, defines the isomorphism-class orbit,
the representative square, compact-picture polynomial and rational families,
and the weak integral. Theorem IV.1.1, printed p.278 / PDF p.44, adds finite
length and asserts convergence on one full-root cone and rationality.
The full rational norm kernel and normalized real-part conventions come from
I.1, printed pp.238–240 / PDF pp.4–6.

The orbit helpers are internal constructions on the existing `SmoothRep`
and continuous-character interfaces. The statement combines the source
assertion with explicit modulus and representative-transport obligations
needed by the existing implementation. It uses a quotient topology and
concrete evaluation-generated scalar algebra; it does not assert an
algebraic-variety identification of the orbit.

## Actual twist classes, orbit, and saturation

The first section works for any group `L : Type uL` with a topology and
`NonarchimedeanGroup L`, any full indexed positive-character family
`ν : I → (L →* ℝ≥0ˣ)`, and any `π : SmoothRep.{0,uL,uV} ℂ L`.
No admissibility, finite-length, or continuity premise on the indexed family
is needed for these helpers. The characters themselves are continuous:
`unramifiedCharacters ν` is the existing subgroup of continuous complex
characters trivial on the common kernel of **every** `ν i`.
Its existing topology is retained. The published
`unramifiedCharacter_isOpen_ker` gives smoothness of each twist.

`unramifiedTwistClass ν π χ` is the existing `SmoothRep.isoClass` of the
actual smooth representation `π.twist χ`. `UnramifiedTwistOrbit ν π`
is the subtype of `SmoothRep.IsoClass` lying in the range of this map.
It is not restricted to irreducible representations, is not resized to
a smaller universe, and makes no choice of representative.
`unramifiedTwistOrbitMap` sends a character to that range subtype.
It is surjective by construction. The topology on the orbit is exactly
`TopologicalSpace.coinduced` by this map: a set is open when its full
preimage in the existing character space is open.

For a character set `D`, `unramifiedTwistOrbitRegion ν π D` is its image
in the orbit, and `unramifiedTwistOrbitSaturation ν π D` is the full
preimage of that image. The two implemented helper proofs show:

- `subset_unramifiedTwistOrbitSaturation`: `D` lies in its saturation;
  the witness for a character is that same character.
- `mem_unramifiedTwistOrbitSaturation_iff`: a character `χ` belongs
  precisely when some `ψ ∈ D` has `π.twist ψ ≅ π.twist χ`.
  The proof takes the underlying class equality of the orbit-subtype
  equality and applies the published `SmoothRep.isoClass_eq_iff`;
  conversely it applies that theorem and `Subtype.ext`.

These class equalities use one fixed carrier universe. Naturality in the
main target separately handles equivalent representations with an
independent carrier universe, without identifying different `IsoClass`
types. A cone is not assumed to be saturated: for example, for the zero
representation all its twists have the same class.

## Structural hypotheses of the conditional target

Every input is quantified inside the Prop definition, including hypotheses
used only to identify the mathematical setting.

1. `F : Type u` is an arbitrary nonarchimedean local field, with `Field`,
   `ValuativeRel`, `TopologicalSpace`, and `IsNonarchimedeanLocalField`
   instances. There is no characteristic restriction. `G` is a group
   scheme over `Spec F` with `IsConnectedReductive G`. Its affineness
   and smoothness are taken from that predicate. The point group is
   `rationalPoints G` with exactly `rationalPointTopology F G.X` and
   its proved topological-group structure. Locally compact,
   nonarchimedean-group, and Hausdorff instances for that point group
   remain explicit structural inputs.
2. The supplied group schemes are `M,P,P',Q,U,U',V`, with a commutative
   group scheme `A`, and actual maps `p:P→G`, `l:M→P`,
   `p':P'→G`, `l':M→P'`, `a:A→M`, `n:U→P`, `n':U'→P'`,
   `q:Q→G`, and `v:V→Q`. Affineness and locally finite type of `M`
   are explicit instances. They are consistent with the existing
   connected reductivity of the specified rational Levi.
3. `r : ParabolicRootPresentation p l a` and
   `r' : ParabolicRootPresentation p' l' a` are the complete existing
   compatible presentations, not just root labels. Each retains the
   actual parabolic, rational Levi, split component, maximal split torus,
   generic cocharacter, subset of simple roots, all-test standard
   parabolic and Levi image equalities, factorization through the
   ambient split torus, dynamic minimality and containment, and a
   cocharacter realizing both supplied images. The literal common-Levi
   equation `l ≫ p = l' ≫ p'` is a separate input.
4. Both `n` and `n'` satisfy
   `LeviSubgroup.IsGeometricUnipotentRadical`. The functor of the negative
   dynamic parabolic for `r'.splitComponentCocharacter`, embedded by
   `a ≫ l' ≫ p'`, is represented by `q`; `v` satisfies the same
   geometric-radical predicate. These are the specified radical and
   opposite-image hypotheses, including their geometric greatestness
   conditions. General existence of presentations or these representatives
   is not asserted.
5. A `Fintype` instance on the actual `relativeWeylGroup r.data.i`
   remains explicit. The ambient torus monomorphism follows from
   maximal splitness. Monicity of the factor `r.data.f` is derived from
   the monic split-component, Levi and parabolic composites and
   `r.isCompatible.factor_comp`. No extra root-correspondence or
   bilinear-form compatibility premise is supplied.
6. At the identity test scheme, `Ppt` and `P'pt` are the values of
   `range p` and `range p'`; `Mpt` is the literal
   `parabolicLeviPointSubgroup p l`, the value of `range (l ≫ p)`;
   `Upt` and `U'pt` are the values of `range (n ≫ p)` and
   `range (n' ≫ p')`. All carry the inherited canonical point topology.
   The input semidirect decompositions `h` and `h'` use this **same**
   `Mpt`. Closedness of both parabolics and both radicals is explicit.
   Closedness of `Mpt` is obtained by
   `isClosed_parabolicLeviPointSubgroup r`.
7. One actual open subgroup `K` is compact and has both full
   factorizations `Gpt = Ppt K` and `Gpt = P'pt K`.
   Continuity of both actual Levi projections `h.projection` and
   `h'.projection` is explicit. No existence theorem for this common
   compact subgroup is asserted.
8. The integration space is exactly
   `StandardIntertwining.QuotientSpace (U := Upt) U'pt`, the left
   quotient of `U'pt` by `Upt.subgroupOf U'pt`. The intersection need
   not be normal. Borel measurable structures on `U'pt`, that
   intersection, and the quotient are explicit. `μU'` and `μI` are
   regular Haar measures with right invariance as well; `qν` is a
   measure on the actual quotient, with
   `QuotientIntegration.IsCompatible` for those two Haar measures.
   This is the existing quotient-integration normalization.

These are conditional framework inputs. In particular the target assumes
no analytic intertwiner convergence, rational continuation, induced
irreducibility, finite spectral support, or Plancherel assertion.

## One ambient form and every actual root

The norm family in the target is exactly
`ν := parabolicLeviRationalNormCharacters r`, indexed by **all**
`rationalCharacters M`. The canonical point homeomorphism from the
specified Levi scheme onto `Mpt` transports their norms. Its continuity
is the proved `continuous_parabolicLeviRationalNormCharacters r`.
There is no selected sublattice or substitute norm kernel.

The form is the constructed `weylInducedCharacterForm` from the single
ambient Weyl form of `r.data.i`, the actual factor `r.data.f`, and its
orthogonal lift. It is not an arbitrary form. Write
`C R := parabolicPointUnramifiedIntertwiningRegion r B n q v R`.
By the imported `mem_parabolicPointUnramifiedIntertwiningRegion`,
membership tests **every** `α ∈ relativeRoots (a ≫ l ≫ p)` with

```text
0 < latticePairing A α r.splitComponentCocharacter
latticePairing A α r'.splitComponentCocharacter < 0.
```

For each such root it requires the strict inequality

```text
R < B (SplitTorus.normalizedRealPart
          (χ restricted through parabolicSplitComponentPointHom r))
        (1 ⊗ α).
```

The normalized real part is the existing residue-cardinality-normalized
parameter of the same character. The signs select the full source and
opposite-target radical intersection. Simple roots alone, indivisible
roots alone, or a reduced-root replacement are not substituted. The
imported `parabolicPointUnramifiedIntertwiningRegion_eq_ambient` identifies
this with the complete ambient-root region under the same orthogonal
lift, including merged restrictions. Empty root intersections and
rank zero are included.

## Quantified conclusions

For **every** `π : SmoothRep.{0,u,uV} ℂ Mpt` satisfying `π.IsAdmissible`
and `π.HasFiniteLength`, the target concludes all of the following.
Admissibility is the existing all-open-subgroups convention. Finite length
means finite composition length over the complex group algebra, not
finite-dimensionality of the inducing space.

First, it concludes `IsUnimodularModulus Upt hU` and
`IsUnimodularModulus U'pt hU'`: inner automorphisms of each radical have
trivial Haar modulus. It also concludes
`SquaredModulusCompatibility h hU h' hU'`, the actual identity
`δ_U(m) δ_U'(m) = δ_(U∩U')(m)^2` on the common Levi, in the existing
closed-subgroup Haar-character convention. The intersection character
is equivalently the modulus of the actual restricted conjugation on
`Upt.subgroupOf U'pt`. These are obligations of the target, not permanent
external structural hypotheses. Their proofs are needed to package the
integral with the actual positive normalized covariance laws.

There is then **one** real threshold `R` such that `C R` is nonempty and
open and its image in `UnramifiedTwistOrbit ν π` is open. Put

```text
Ω = unramifiedTwistOrbitSaturation ν π (C R).
```

For every `χ : Ω`, the actual `StandardIntertwining.domain` for
`π.twist χ` equals the whole positive Levi-normalized source induction.
By that domain's definition, at every source vector and every `g ∈ Gpt`
all scalar integrals against smooth functionals converge absolutely and
are represented by a vector in the **original** inducing carrier.
No carrier completion or formal integral replaces this conclusion.
Since `C R ⊆ Ω`, it includes the original full-root convergence cone.
It also covers every parameter representing the same orbit region.

`StandardCompactRationalOn` is asserted on this entire `Ω`. Its operators
are the actual `fullSourceIntertwiner` conjugated by the source and target
`unramifiedLeviInductionCompactEquiv` restriction isomorphisms to the fixed
compact pictures. They retain the original smooth-dual integral
specification at every ambient argument. Expanding the existing
rationality predicate gives

```text
∃ b ∈ unramifiedRegularFunctions ν,
  (∀ χ ∈ Ω, b(χ) ≠ 0) and
  ∀ f, ∃ a finite family (b_i) and fixed target vectors (f_i),
    ∀ χ ∈ Ω, b(χ) J_compact(π.twist χ) f = Σ_i b_i(χ) f_i.
```

The scalar algebra is the actual complex subalgebra generated by all
evaluations `χ ↦ χ(m)`. Inverse evaluations are already included.
There is **one denominator before the input vector**; the finite numerator
expansion may depend on that vector. The denominator is nonzero on all
parameters over the open orbit image, not only on the original cone.

Finally, for every `χ : Ω`, every
`W : SmoothRep.{0,u,uW} ℂ Mpt`, and every actual equivariant linear
equivalence `e : (π.twist χ).representation.Equiv W.representation`,
the target concludes full domain for `W` and the equality

```text
J(W) ∘ Ind_P(e) = Ind_P'(e) ∘ J(π.twist χ).
```

Both operators in this square are the actual full-source integrals with
their displayed domain proofs and the same compatible measures.
This includes automorphisms, equivalent twists, and independent-carrier
representatives. The existing `fullSourceIntertwiner_natural` supplies the
formal square once full-domain transport is established; neither
full-domain transport nor the square is an input to this statement.

## Scope and remaining proof obligations

This is a source-motivated conditional target, with two elementary
orbit-helper proofs. It establishes neither IV.1.1's analytic proof nor
general realization or independence of the structural data. It does not
prove an algebraic quotient description of the orbit, identify a new
variety with it, or construct the universal algebraic `B`-family and
specialization maps discussed in IV.1. The open set here uses the
explicit quotient topology; rationality uses the concrete
evaluation-generated algebra on its full preimage, together with the
actual representative square. Any comparison with additional
algebraic-geometric orbit constructions requires its own proof.

The analytic proof, general radical-unimodularity proof and actual
squared-modulus proof remain necessary. No irreducibility of normalized
parabolic induction is imposed. Arbitrary field characteristic, nonsplit
and non-quasisplit ambient groups, and independent representation
carriers are retained. Publication of this statement alone does not
close the broader Plancherel program.
