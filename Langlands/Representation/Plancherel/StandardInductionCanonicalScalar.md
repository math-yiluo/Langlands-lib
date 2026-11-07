# Canonical rational scalars of actual standard integral composites

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed pp.276–278 / PDF pp.42–44, defines rational functions on
the complex inducing orbit, identifies the normalized induced carriers
with fixed compact pictures, and formulates naturality under inducing
isomorphisms. At the beginning of IV.3, printed p.285 / PDF p.51, generic
induced irreducibility and Schur's lemma give a rational scalar for the
opposite-intertwiner composite. This module supplies an internal
normalized coefficient to the existing actual-standard-integral scalar
construction and proves independence from that coefficient. It is an
algebraic implementation of the scalar's choice independence, rather
than a separately numbered assertion in the article.

Here “canonical” means independence of the normalized coefficient, both
rational continuation choices, and the chosen irreducibility locus, with
the displayed compact model, subgroups, inducing object and measures
held fixed. It does not mean the parabolic-independent, source-normalized
`j` of IV.3. No opposite-parabolic relation is assumed in this module.

## Constructing a normalized coefficient

The first section is generic. Let `G` be a locally compact
nonarchimedean group, `P = M U` an actual semidirect subgroup
decomposition, `U` and `P` closed, `K` compact open, and `G = P K`.
Retain `IsUnimodularModulus U hU`, continuity of the semidirect
projection, a continuous family `ν` of positive characters of `M`,
and a canonical complex smooth representation `A` of `M`. The index,
group and representation-carrier universes `uI,uG,uV` are independent.

`compactInductionPicture_nontrivial_of_irreducible` takes a character
`χ` for which the actual `UnramifiedLeviInduction` is irreducible.
Its proof uses the nontriviality of the associated simple monoid-algebra
module, then transfers that nontriviality through
`unramifiedCompactRepresentationEquiv`. Thus the compact picture is
nonzero because an actual induced representation is irreducible; no
abstract scalarity or chosen nonzero compact vector is assumed.

`compactInductionScalarExtraction` chooses a pair `(v,ℓ)` on this
compact carrier with `ℓ(v) = 1`. It chooses `v ≠ 0` using the preceding
nontriviality, then applies `exists_normalized_scalar_functional` to
choose `ℓ`. The functional is in the algebraic linear dual; it is not
asserted to be continuous. The output is a subtype containing the pair
and its normalization proof. These constructions need just one
irreducible induction, without any open irreducibility locus.

## Actual standard families and visible premises

The second section uses exactly the actual data of
`StandardInductionOrbitScalar`. The local field `F` has arbitrary
characteristic; `L` is a connected reductive group scheme over `F`.
Write `H = L(F)` and `νL` for its complete rational norm-character
family. The topology on `H`, its nonarchimedean group structure,
continuity `hp` of the rational valuation-image projection, and
continuity of every norm character are explicit.

`G` is a locally compact Hausdorff nonarchimedean group with actual
closed decompositions `P₀ = M U₀`, `P₁ = M U₁`, both
`IsUnimodularModulus` premises, a common compact open `K`,
`G = P₀ K = P₁ K`, and continuous semidirect projections. The
identification `e : H ≃ₜ* M` supplies the character chart. Put
`νM ψ = νL ψ ∘ e.symm`,
`χM = unramifiedCharactersHomeomorph e νL`, and
`π = SmoothRep.pullback e A`. The inducing object is the canonical
`SmoothRep.{0,uG,uV} ℂ M`. Let `Iᵢ(χ)` denote the actual normalized
induction from `Pᵢ` of the twist of `A` by `χM χ`.

All measure hypotheses remain visible: Borel structures on both
radicals, both subgroup intersections and both quotient spaces;
regular right-invariant Haar measures on the radicals and
intersections; quotient measures `q₁₀,q₀₁` with their two integration
compatibility proofs; closedness of the Levi; and both
`SquaredModulusCompatibility` identities. These are supplied data and
premises, not realizations proved for all reductive rational points.

`Ω₁₀,Ω₀₁` are the exact `standardIntertwiningFullDomainRegion` sets.
They require absolute scalar convergence against every smooth dual
functional and representability in the original inducing carrier,
for every source vector and group element. The families `J₁₀,J₀₁`
are the actual `standardInductionIntertwinerFamily` objects on those
sets. They are determined by the displayed subgroup and measure data.

`p,q` are independently supplied whole-operator rational continuations
of their compact restrictions. Each continuation has a polynomial
numerator family and one denominator nonzero on its entire original
full domain. Separate nonempty ambient open subsets
`D₁₀ ⊆ Ω₁₀`, `D₀₁ ⊆ Ω₀₁` remain convergence premises in the
comparison and equation results. Neither the full domains nor these
opens are assumed to intersect. The common continued regular region is

\[
R=p.\mathrm{regularRegion}\cap q.\mathrm{regularRegion}.
\]

Its nonemptiness follows from the independent nonempty original
regions and the existing density results for actual rational norm
characters. Neither original full domain is asserted open.

The field, ambient-group and inducing-carrier universes `u,uG,uV`
remain independent. There is no split, quasisplit, characteristic-zero,
finite-length, admissibility or unitary-locus restriction.

## The internally defined fraction and its independence

Let `D` be a nonempty set of characters and assume `I₀(χ)` irreducible
for every `χ ∈ D`. Choose `χ₀ ∈ D`, then use
`compactInductionScalarExtraction` at `χM χ₀` to obtain `(v₀,ℓ₀)`
with `ℓ₀(v₀)=1`.

`standardInductionCompositeCanonicalRationalScalar` defines the concrete
function-field fraction

\[
j_C=\mathrm{continuedCompositeRationalScalar}
       (p,q,v_0,\ell_0).
\]

This is extracted from the reverse continued compact operator after the
forward one. It is not a scalar supplied to force a desired composition
identity. The definition itself needs the nonempty original regions
and the displayed irreducibility premise used to construct `(v₀,ℓ₀)`;
it does not need separability of `G` or openness of `D`.

`standardInductionCompositeCanonicalRationalScalar_continuation_independent`
compares arbitrary replacement continuations `p',q'` of the same original
families. It specializes
`continuedCompositeRationalScalar_continuation_independent` using the
same internally selected coefficient on both sides. This result uses
the two nonempty open convergence subsets but does not need generic
scalarity, separability of `G`, or openness of `D`. Equality is in the
actual rational function field, even when the regular regions differ.

For all remaining declarations, `G` is additionally separable and `D`
is open. The actual induced irreducibility on `D` remains a premise.
The imported engine applies smooth Schur only at irreducible parameters
and then uses rational uniqueness; irreducibility at an evaluation
parameter in `R` is not needed.

`standardInductionCompositeCanonicalRationalScalar_eq_extraction` proves
that for every compact vector `v` and algebraic linear functional `ℓ`
with `ℓ(v)=1`,

\[
j_C=\mathrm{continuedCompositeRationalScalar}(p,q,v,\ell).
\]

Its proof is
`continuedInductionCompositeRationalScalar_independent`, with the
internally selected pair on the first side and the arbitrary normalized
pair on the second.

`standardInductionCompositeCanonicalRationalScalar_irreducibility_locus_independent`
uses that equality with the pair selected from another nonempty locus
`D'` on which the same actual induction is irreducible. It proves
equality of the two internally defined fractions. The second locus
need not be open, because generic scalarity is already available from
`D`. Together these results remove dependence on the selected point,
vector and functional without asserting uniqueness of the selected pair.

## Full stabilizer, orbit presentation and ambient equations

`standardInductionCompositeCanonicalRationalScalar_stabilizer_fixed`
applies the preceding actual-standard-family fixedness theorem to
`(v₀,ℓ₀)`. For every element of the full smooth inducing self-twist
stabilizer it proves

\[
\tau^*j_C=j_C.
\]

The translation convention is `τ*(b)(χ)=b(τχ)`. The full stabilizer is
of the actual isomorphism class of `π`. The original comparison squares
are supplied by proved standard-integral naturality; they are not new
hypotheses. Fixedness needs no finite-stabilizer premise.

`standardInductionCompositeCanonicalOrbitScalarPresentation` adds
`Finite` for that full stabilizer and applies
`standardInductionCompositeOrbitScalarPresentation` to `(v₀,ℓ₀)`.
It constructs an `UnramifiedInvariantScalarPresentation` of exactly
`j_C`: an invariant regular numerator and a nonzero invariant regular
denominator with the prescribed fraction. The existing interface gives
its value on the complex representation-isomorphism-class orbit and
agreement of different presentations on their common regular region.

For any such presentation `r`,
`standardInductionComposite_eq_canonicalOrbitScalar` proves, for
`χ ∈ R` with `r.denominator(χ) ≠ 0`,

\[
J^{\mathrm{ext}}_{01}(\chi)J^{\mathrm{ext}}_{10}(\chi)
 =r([\pi\otimes\chi])\operatorname{id}_{I_0(\chi)}.
\]

`standardInductionOriginalComposite_eq_canonicalOrbitScalar` instead
uses `χ ∈ Ω₁₀ ∩ Ω₀₁` and the same denominator condition to prove

\[
J_{01}(\chi)J_{10}(\chi)
 =r([\pi\otimes\chi])\operatorname{id}_{I_0(\chi)}.
\]

Both proofs instantiate the existing actual-standard-family ambient
equations with `(v₀,ℓ₀)`. The canonical fraction is definitionally the
fraction used there, so no presentation is replaced by an unrelated
one. These are equalities of ambient `Representation.IntertwiningMap`
objects. The original equation uses the imported agreement of each
continued intertwiner with its original integral. The theorem does
not assert nonemptiness of `Ω₁₀ ∩ Ω₀₁`.

Neither equation needs a finite-stabilizer instance once `r` is
supplied. Both allow reducible evaluation parameters in their stated
regular region. Finiteness is used only to construct an invariant
presentation; no value at a pole is asserted.

## Remaining obligations

The normalized extraction pair is now constructed rather than supplied.
Initial nonempty-open full convergence, whole-operator rational
continuation, generic actual induced irreducibility and full-stabilizer
finiteness remain obligations for applications. The representation and
analysis premises are not permitted external structural assumptions for
completion of the standing program.

The module proves no independence from the compact model, measures,
inducing representatives or parabolic subgroups. Opposite-parabolic
identification, parabolic independence, nonvanishing, positivity,
source-normalized `j` and `mu`, structural realizations, and the
Schwartz, spectral and main Plancherel conclusions remain separate.
Chosen regular loci are not asserted maximal, and no density on a
unitary locus is inferred from complex density.
