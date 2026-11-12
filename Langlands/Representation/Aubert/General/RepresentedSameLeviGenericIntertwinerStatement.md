# Generic nonzero morphisms between represented inductions sharing a Levi

`RepresentedSameLeviGenericNonzeroIntertwinerStatement`, in namespace
`Langlands.Aubert.General.RepresentedParabolic`, is an internal derived proposition. It is the
represented-parabolic form of the published target
`RationalPointFamily.RationalSameLeviGenericNonzeroIntertwinerStatement`.

## Statement

Fix a nonarchimedean local field `k` of any characteristic and a connected reductive group `G`
over `k`. Give `G(k)` its canonical rational-point topology, and assume that it is locally compact
and a nonarchimedean group. Fix two actual represented parabolics with the same Levi scheme `M`:

- `P = MN`, given by `p : P → G`, `l : M → P` and `r : N → P`;
- `Q = MU`, given by `q : Q → G`, `lQ : M → Q` and `rQ : U → Q`.

For each one, the statement assumes the usual parabolic, rational-Levi, geometric-unipotent-radical
and multiplication hypotheses. It also assumes that the two Levi inclusions agree in `G`:
`l ≫ p = lQ ≫ q`.

Let `σ` be an irreducible admissible smooth complex representation of `M(k)`, where `M(k)` has
its canonical topology. The conclusion is that there is a nonzero polynomial `poly` in the
published finite coordinates `Plancherel.rationalCanonicalUnramifiedCharacterCoordinates M`.
For every unramified character `ψ` of `M(k)` in `Plancherel.rationalUnramifiedPrincipalOpen M _ poly`,
some morphism

`leviInductionFunctor p l r … (σ ⊗ ψ) ⟶ leviInductionFunctor q lQ rQ … (σ ⊗ ψ)`

in `SmoothRep` is different from the zero morphism. Here `leviInductionFunctor` is the published
normalized parabolic induction from `M(k)` through each parabolic.

## Provenance

This is a derived intermediate proposition. Its mathematical content is the generic-nonvanishing
part of Waldspurger's IV.1(10) (`waldspurger-2003-plancherel`, p.283), restricted to two
parabolics that share a Levi. The intended proof follows Renard's algebraic construction in
VII.3.2–VII.3.4 (`renard-2026-representations-groupes-reductifs-padiques`, printed pp.232–236)
instead of Waldspurger's integrals. Generic `PQ`-regularity of `σ ⊗ ψ` gives a nonzero
intertwiner, which is then read through Frobenius reciprocity and the identity support piece.

The statement adds no hypothesis beyond the represented structure. In particular it does not
assume that either induced representation is irreducible.
