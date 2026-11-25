# The locally closed locus of frame-normalized polarized data in a projective family

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameHilbertLocusStatement` is a
proposition definition (universe `0`). It is a statement target only; this module proves
nothing.

## The statement

Fix `P : Prerequisites.{0}`, natural numbers `g d n` with `0 < d` and `3 ≤ n`, and
`ρ : Fin (m + 2) → Fin (2*g) → ZMod n` with `m = cubicProjectiveDimension g d`
(so `m + 1 = 6^g·d`). Let `S` be a locally noetherian scheme, `I` an ideal sheaf on
`RelativeProjectiveSpace S m` whose closed subscheme `I.subscheme` is flat and locally of
finite presentation over `S`, and `σ r : S ⟶ ProjectiveSpace (ULift ℤ) m` an integral
projective point for every level coefficient tuple `r : Fin (2*g) → ZMod n`.

For `t : T ⟶ S`, the pulled-back family is `I.comap (RelativeProjectiveSpace.map m t)`
(the ideal of the fibre product of `I.subscheme` with `T`) together with the points
`t ≫ σ r`. Then there are a level base `S' : LevelBase n` and an immersion
`j : S'.obj ⟶ S` such that:

1. there are a datum `U : Datum P S'.obj g d n` with `U.frameLocus ρ = ⊤` and a
   frame-normalized cubic embedding `ψ` of `U` (`Datum.IsFrameEmbedding`, module
   `FrameEmbedding`) realizing the family pulled back along `j` (`Datum.Realizes`); and
2. for every level base `T`, morphism `t : T.obj ⟶ S`, datum `b : Datum P T.obj g d n` with
   `b.frameLocus ρ = ⊤`, and frame-normalized cubic embedding `ψ` of `b` realizing the
   family pulled back along `t`, the morphism `t` factors through `j`.

In other words, `j` represents, on level bases, the subfunctor of morphisms `t : T ⟶ S`
along which the family comes from a frame-normalized datum, and `U` is a universal such
datum. Uniqueness of the factorization is automatic since immersions are monomorphisms.
The hypotheses `0 < d` and `3 ≤ n` are the range of the published moduli functor; the
mathematics below does not need `3 ≤ n`, since frame-normalized data have no
automorphisms.

## Mathematical content and source

This is the relative, frame-normalized form of Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, 3rd ed. (1994), Proposition 7.3 and its proof, printed pp.132–134 (PDF pp.145–147),
registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`, with
Definitions 7.5–7.6 (printed p.130).

**The source's parameter scheme.** Mumford fixes the Hilbert polynomial
`P(x) = 6^g·d·x^g` of the embedded abelian scheme and takes the Hilbert scheme with
`k = 2g + 1` sections (printed p.132): if `Z ⊂ P^m × Hilb^{P}_{P^m}` is the universal closed
subscheme, its parameter scheme `H_0` is the `k`-fold fibre product `Z ×_Hilb ⋯ ×_Hilb Z`.
A `T`-point of `H_0` is a flat closed subscheme of `P^m_T` together with `k` sections *of that
subscheme*: the identity mark and the `2g` level marks. On `H_0` the locus `H_{g,d,n}` is cut
out in six steps (printed pp.133–134): (I) the open part where the geometric fibres are
smooth and connected; (II) by Theorem 6.14 the open and closed part where they are abelian
varieties, the group law having the incident identity mark as identity; (III) the closed part
where the level marks are killed by `n`; (IV) the open part where the residue
characteristics do not divide `n` and the level marks form a basis of the `n`-torsion of
every geometric fibre; (V) by Proposition 6.11 the closed part where `𝒪(1)|_X`, normalized
along the identity, is `L_Δ(ω)^3` for a polarization `ω`; (VI) the open part where the
homomorphism `(*)`, `H^0(P^m, 𝒪(1)) ⊗ M^{-1} → π_*(L_Δ(ω)^3)` with
`M = e^*(𝒪(1)|_X)`, is an isomorphism (its kernel and cokernel vanish). This homomorphism is
the restriction of the coordinate sections to `X`, twisted by the inverse of `M` (printed
p.134). Over this open part, `P` of `(*)` is a linear rigidification inducing the given
embedding.

**The relative, frame-normalized form stated here.** Here `S` is an arbitrary locally
noetherian scheme with an ideal sheaf `I` (flat, locally finitely presented closed subscheme
`Z_S ⊂ P^m_S`) and one *ambient* point `σ r : S ⟶ P^m_ℤ` for every level coefficient tuple
`r : Fin (2g) → ZMod n`. These points are not assumed to lie on `Z_S`, and there are more of
them than Mumford's `2g + 1` marks. The family may also have the wrong Hilbert polynomial.
The locus `S'` is therefore obtained in the following order:

1. the open and closed part `S_P ⊂ S` over which the fibres of `Z_S` have Hilbert
   polynomial `P(x) = 6^g·d·x^g` (the Hilbert polynomial of a flat projective family is
   locally constant on the base). Over `S_P`, `Z_S` defines a morphism to `Hilb^P_{P^m}`;
2. inside `S_P`, the closed incidence locus where `σ 0` and the basis labels
   `σ (Pi.single i 1)` lie on `Z_S` (closed, since `Z_S` is closed in `P^m_S`). Over this
   locally closed part these `2g + 1` points are sections of `Z_S`, namely Mumford's
   identity mark and `2g` level marks. Together with step 1 they define a morphism to
   Mumford's `H_0`;
3. the pullbacks along this morphism of the subschemes `H_1, …, H_6` of steps (I)–(VI)
   above (step (IV) includes invertibility of `n`, as required by `LevelBase n`);
4. for every other tuple `r`, the closed equalizer condition that `σ r` equals the image of
   the torsion section `Σ r_i · (level mark i)` computed with the group law from step (II);
5. the frame equations: `σ (ρ j)` is the `j`-th coordinate point for `j ≤ m` and
   `σ (ρ (m+1)) = [1 : ⋯ : 1]` (closed conditions on points of `P^m`).

Without step 1 the incidence locus need not map to `H_0`. For example, take `g = d = 1`,
`n = 3`, `S = Spec ℚ`, `Z_S` a single rational point of `P^5` and every `σ r` that point.
All incidence conditions hold, but the Hilbert polynomial is `1`, not `6x`. Such a base
point lies outside `S'`.

The frame normalization in 4 is the slice of the free `PGL(m+1)` action described in
`FrameChartRepresentabilityStatement.md`. Over `S'` one must also supply the Library's
per-datum dual witness (`DualWitness`) and check the Library's `IsPolarization`,
`HasDegreeSquare` and `FullLevel` conditions.

The statement is formulated relative to an arbitrary locally noetherian `S` with a family,
so that it does not depend on a particular presentation of the Hilbert scheme. The reduction
of `FrameChartRepresentabilityStatement` applies it to the Hilbert scheme of `P^m` over `ℤ` (published
`HilbertSchemeUniversalFamilyStatement` and its proof) followed by successive relative
projective spaces carrying the ambient points. That parameter scheme is larger than
Mumford's `H_0`, which is why steps 1, 2, 4 and 5 above appear.

## Use

This is the geometric input of the reduction of
`FrameChartRepresentabilityStatement` (`frameChartRepresentability_of_frameHilbertLocus`,
module `FrameChartRepresentabilityReduction`). Its other inputs are
`CubicBundlePolarizationDeterminationStatement` (a datum is determined by its embedded image
and torsion sections), `FrameLocusBaseChangeStatement`, `FrameLocusIsoInvarianceStatement`,
`FrameEmbeddingUniquenessStatement` and `FrameEmbeddingExistenceStatement`. The last supplies
a frame-normalized embedding of every datum with frame locus `⊤`; its proof from the
complete cubic embedding input over fields, `CubicFieldEmbeddingStatement` (Lefschetz), is
`frameEmbeddingExistence_of_cubicFieldEmbedding` (module `FrameEmbeddingReduction`); the
relative step of that input is `Datum.cubicProjectiveEmbedding_of_fieldEmbedding` (module
`CubicEmbeddingReduction`: the cubic evaluation into the projective bundle of `π_* L³` is a
closed immersion). The frame then trivializes this projective bundle `P(π_* L³)`. On the
frame locus, the evaluations at the first `m + 1` frame sections identify `π_* L³` with the
sum of their `m + 1` evaluation lines. The remaining frame conditions identify each of
these lines with the evaluation line `Λ` at the last frame section. So `π_* L³ ≅ Λ^{m+1}`,
which gives `P(π_* L³) ≅ P^m_S`. The frame thus trivializes the projective bundle, not
`π_* L³` itself. In that construction the coordinates are the corresponding
sections of `L³ ⊗ π^*Λ^{-1}`, so the base line bundle `N` in `ψ^*𝒪(1) ≅ L³ ⊗ π^* N`
(`Datum.IsFrameEmbedding.cubic`) is `Λ^{-1}`.
