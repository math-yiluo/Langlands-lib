# Frobenius equivalence on actual Schwartz functions vanishing at zero

`Langlands.RankinSelberg.EqualRankFrobeniusStatement.{uF,uV,uW}` is a
Prop-valued definition of the equivalence used in JPSS (2.10.5)–(2.10.6),
printed p.397. It states existence of a complex-linear equivalence; this
module does not construct that equivalence or prove the proposition.

## Exact Lean statement

For `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`, and `n : ℕ`, install `T.topology`,
`T.valuativeRel`, and `T.localField` and put
`r = n+1`, `G = Langlands.GeneralLinear r F.Carrier`,
`P = Langlands.GeneralLinear.mirabolic n F.Carrier`, and
`abv = normalizedAbsoluteValue T`. The field and two representation-carrier
universes are independent. For every pair of complex modules `V : Type uV`
and `W : Type uW`, representations `ρ : Representation ℂ G V` and
`σ : Representation ℂ G W` satisfying `IsSmooth ρ` and `IsSmooth σ`,
and every `s : ℂ`, the conclusion is

```text
Nonempty (invariantForms ρ σ SplusAction (fun g => determinantWeight abv g (-s))
  ≃ₗ[ℂ]
  InvariantBilinear.forms (ρ.comp P.subtype) (σ.comp P.subtype)
    (fun p => determinantWeight abv p.val (1 - s))).
```

Here `Splus` is exactly the underlying submodule
`(rowVanishingAtZero (F := F.Carrier) (n := r)).toSubmodule` of the actual
`SchwartzBruhat (Fin r → F.Carrier)`, and `SplusAction` is this published
subrepresentation's `toRepresentation`. In particular, an element is a
compactly supported locally constant row function `Φ` with `Φ 0 = 0`.
The Lean expression explicitly supplies this underlying submodule as the
carrier parameter `S` of `invariantForms`.

The source space reuses
`Langlands.RankinSelberg.TrilinearReduction.invariantForms` from
`Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly`.
Its elements are the full curried linear forms
`B : V →ₗ[ℂ] W →ₗ[ℂ] Splus →ₗ[ℂ] ℂ` with

```text
B (ρ g v) (σ g w) (SplusAction g Φ)
  = determinantWeight abv g (-s) * B v w Φ.
```

The action is the restriction of the published
`Langlands.HarmonicAnalysis.rowSchwartzRepresentation`. Its underlying
Schwartz function is `Langlands.HarmonicAnalysis.rowTranslate g Φ`,
whose value at `x` is `Φ (Matrix.vecMul x g.val)`.
The proved `rowSchwartzRepresentation_apply`, `rowTranslate_apply`, and
`eq_rowTranslate_iff` in `Langlands.HarmonicAnalysis.RowSchwartzAction`
give the comparison with the pointwise translation convention. Thus for
`Φ, Φg : Splus`, the premise
`∀ x, Φg.val x = Φ.val (Matrix.vecMul x g.val)` is equivalent to
`Φg = SplusAction g Φ`: apply `eq_rowTranslate_iff` to their underlying
functions and use subtype extensionality. On the full Schwartz space,
the same comparison for invariant forms is already proved by
`TrilinearReduction.invariant_iff_pointwise`. No additional action,
translation premise, or test-function replacement is assumed.

The target space reuses `Langlands.InvariantBilinear.forms` from
`Langlands.Representation.Filtration.InvariantBilinear`. Its elements are
exactly `β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` satisfying, for each actual `p : P`,

```text
β (ρ p.val v) (σ p.val w)
  = determinantWeight abv p.val (1 - s) * β v w.
```

Smoothness means that every vector has an open subgroup fixing it; it
imposes no topology on `V` or `W`. There is no Whittaker, admissibility,
finite-length, irreducibility, nonzero-vector, finite-dimensionality,
quotient-section, or supplied Frobenius-theorem premise. The proposition
includes `n=0`, when `G=GL₁(F)` and the actual mirabolic group is trivial.
It also includes zero representation spaces. The equivalence has precisely
the type consumed, parameter by parameter, by the published
`TrilinearReduction.source_uniqueness_of_mirabolic_bound`.

## Original sources and normalization

The following registered originals were read visually at the stated pages:

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
  367–464: modular convention and normalized induction, printed pp.376–377;
  invariant bilinear forms, p.378; (1.3), p.380; and (2.10), pp.397–398.
  Literature ID `jpss-1983-rankin-selberg`; retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  These printed pages are one-based PDF pages 11–13,15,32–33.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68: pp.23–24, especially 2.25(c), Theorem 2.28,
  and Proposition 2.29.
  Literature ID `bernstein-zelevinsky-1976-representations-gln`; retained file
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`;
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Printed and one-based PDF page numbers agree.

No matching source erratum note was found in the checked project literature,
project notes, or Library notes. The formulas below explain the source
correspondence and the remaining proof route; they are not Lean results
proved by this module.

Write `η = (0,…,0,1)` and `α(g) = abv(det g)`. The last-row map
`g ↦ ηg` is constant on left `P`-cosets, has stabilizer `P`, and identifies
`P\G` with the nonzero rows. For the needed function-space identification,
this must be a homeomorphism. A bare bijection would not transport local
constancy and compact support. Under this identification, `Splus` corresponds
to `C_c^∞(P\G)` with right translation.

The support condition uses compact support in the nonzero-row orbit.
Because a locally constant `Φ` with `Φ(0)=0` vanishes on a neighborhood of
zero, its compact support stays inside that orbit. Conversely, a compactly
supported locally constant function on the orbit extends by zero: its
compact support is closed in the Hausdorff ambient row space and misses
zero, giving a zero neighborhood there. This explains the exact use of
Schwartz functions vanishing at zero.

JPSS pp.376–377 defines its module `δ_H` by the condition that
`δ_H^(-1) d_r` is left Haar measure when `d_r` is right Haar measure.
For `p = (m,u;0,1)` in the mirabolic group, right Haar measure is `dm du`
and left Haar measure is `|det m|^(-1) dm du`, with `dm` Haar measure on
the unimodular group `GL_n(F)` and `du` additive Haar measure on `F^n`.
Thus, in this source's convention, `δ_G=1` and `δ_P(p)=α(p)`.
For `n=0`, both `P` and its modular character are trivial, in agreement
with the same formula.

JPSS (2.10.5) writes the orbit function space as its compactly induced
`Ind(G,P,δ_P^(-1/2))`. Its normalized induction formula on p.377 has
left factor `δ_P^(1/2) δ_G^(-1/2)`, which cancels the inducing character
`δ_P^(-1/2)` here and leaves scalar left-`P` invariance.
JPSS (1.3), p.380, supplies the relative factor
`δ_G^(1/2) δ_P^(-1/2)` in bilinear Frobenius reciprocity. Applying it
therefore gives `Bil_P(ξ,δ_P^(-1))` for `ξ=(ρ ⊗ σ ⊗ α^s)|P`.
By the definition on p.378, `Bil_P` consists of invariant bilinear
pairings. The second argument here is the character representation
`δ_P^(-1)=α^(-1)|P`. If `b` is such a pairing and `ℓ(z)=b(z,1)`, its
invariance reads

```text
b(ξ(p) z, α(p)^(-1)) = b(z, 1),
ℓ(ξ(p) z) = α(p) ℓ(z).
```

Removing the `α^s` factor from `ξ` gives the bilinear covariance
`β(ρ(p)v,σ(p)w)=α(p)^(1-s) β(v,w)`. Equivalently, this is an invariant
pairing in
`Bil_P((ρ ⊗ α^(s-1))|P, σ|P)`, exactly (2.10.6).
This accounts for the exponent `1-s` in Lean.

BZ76 2.28 is the smooth-induction adjunction. Proposition 2.29 combines
it with the contragredient relation 2.25(c); its displayed formula retains
the modular-character ratio. This is the closed-subgroup bilinear
reciprocity needed here. JPSS continues on pp.397–398 with Whittaker-type
constituent bounds and a residual pairing supported at zero. Those later
steps do not supply hypotheses for the earlier Frobenius equivalence.
Its extension here to arbitrary smooth `ρ,σ` is the direct specialization
of (1.3) to their smooth tensor product and the same orbit representation.

## Separate proof obligations and existing infrastructure

The future proof must supply the following constructions, without assuming
them as premises of this statement:

1. Identify the actual left quotient by `mirabolic n F.Carrier` with the
   nonzero-row orbit, including surjectivity, the fibers, topology, and right
   equivariance. Local coordinate constructions may be used; no global
   quotient section is part of the statement.
2. Construct the restriction/extension-by-zero equivalence and its
   equivariant comparison with actual compact induction. The existing
   `Langlands.Induction.CompactFunctions` and `compactInduced` in
   `Langlands.Representation.Induction.Definitions` use compact projected
   nonzero support in the left quotient and a uniform open right stabilizer.
   The published `Langlands.HarmonicAnalysis.rowTestSmooth` in
   `RowTestSmoothProof` already gives that stabilizer for row Schwartz
   functions; transferring it through the orbit identification is still
   required.
3. Prove the scalar modular-character comparison in the chosen Haar
   conventions and its equality with the supplied normalized absolute value.
   The JPSS formula above is the required normalization, not an assumed
   Lean identification of a Mathlib modular character with that formula.
4. Construct the closed-subgroup bilinear Frobenius maps, their linearity,
   and both inverse laws, including the tensor/curried-form comparison.
   Reuse the actual induction constructions and the published
   `Langlands.Induction.SmoothFrobeniusClause` in
   `Langlands.Representation.Induction.StructuralStatement` as the existing
   smooth-adjunction target, with the required contragredient and modular
   comparisons. That Prop-valued clause is not itself a proof. The
   open-subgroup compact-induction adjunction has an openness hypothesis
   that this mirabolic use does not provide.

These obligations describe a proof of this focused target, rather than a
new induction theory or an analytic integral construction. Existing Library
pairs are imported unchanged.
