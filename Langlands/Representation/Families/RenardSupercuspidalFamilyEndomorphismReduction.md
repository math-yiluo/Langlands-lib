# Renard VI.8.6 Example, reduced to three inputs

This module reduces the published closed statement
`Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement`
([RenardSupercuspidalFamilyEndomorphismStatement](RenardSupercuspidalFamilyEndomorphismStatement.md))
to three inputs that are not yet proved. It contains:

- one **statement**, the `Prop`-valued definition `SupercuspidalFamilyFiberStatement`
  (universes `u, v`), the fiber step of Renard's argument;
- the theorem `endomorphismScalar_leviInduced`, the VI.8.6 Proposition for a normalized
  parabolic induction `i_P^G(σ)` of an abstract flat admissible family `σ`;
- the theorem `supercuspidalFamilyEndomorphism_of_statements`, which proves
  `SupercuspidalFamilyEndomorphismStatement.{u, v}` from
  `GenericInducedIrreducibilityStatement.{u, v}`,
  `RationalPointsIrreducibleAdmissibleStatement.{u, v}` and
  `SupercuspidalFamilyFiberStatement.{u, v}`.

It does **not** prove the closed target, because the three inputs are open.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`,
file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- VI.8.6, the Example after the Proposition, first paragraph, printed p. 195 / PDF
  p. 201: "Grâce au théorème d'irréductibilité générique, les hypothèses de la
  proposition ci-dessus sont satisfaites, et l'on en conclut qu'il existe un `b ∈ B`
  tel que `φ` est l'action de `b`."
- The proof of the VI.8.4 Proposition, printed p. 192 / PDF p. 198, which sets up the
  notation of the Example. It contains the specialization used by the fiber step:
  "Spécialisons maintenant en `ψ ∈ X(M)`. On a, d'après le corollaire VI.8.2,
  `sp_ψ(π_B, V_B) = sp_ψ(i_P^G(ρ_B, W_B)) = i_P^G(ρ ⊗ ψ)`."
- Theorem VI.8.5, printed p. 193 / PDF p. 199 (generic irreducibility), and
  Theorem VI.2.2, printed p. 140 / PDF p. 146 (irreducible supercuspidal
  representations are admissible), which the source uses for the admissibility of
  `V_B`.

## The statement `SupercuspidalFamilyFiberStatement`

Binders and conventions are those of `SupercuspidalFamilyEndomorphismStatement`:
`k`, `G`, `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, `hp`, `hl`, `hr`, `hmul`, the Levi
point topology on `M(F)`, `ν` the rational norm characters of `M(F)`,
`B = Plancherel.unramifiedRegularFunctions ν`, and the universal family
`ρB = Plancherel.universalUnramifiedRepresentation ν σ` on `B ⊗[ℂ] W`. The `letI`
structures on `B ⊗[ℂ] W` and the instance-search option are copied from that
statement. The representation `σ : Representation ℂ (rationalPoints M) W`,
`W : Type v`, need only be smooth.

For every unramified character `ψ : Plancherel.unramifiedCharacters ν` and every
`ℂ`-algebra map `χ : B →ₐ[ℂ] ℂ` with `χ b = b ψ` for all `b` (evaluation at `ψ`):
if the published normalized parabolic induction
`(leviInductionFunctor p l r hp hr hl hmul).obj ((SmoothRep.of σ hσ).twist ψ ...)`
of the twist `σ ⊗ ψ` is irreducible, then the fiber of `V_B = LeviInduced p l r hp hr hl hmul ρB`
at `χ` is irreducible. The fiber is `ℂ ⊗_{B,χ} V_B` with `G(F)` acting through
`Module.End.baseChangeHom`, exactly the form of the fiber hypothesis of the published
`EndomorphismScalarStatement`
([RenardFamilyEndomorphismStatement](RenardFamilyEndomorphismStatement.md)).

Provenance: derived. The source identifies the specialization `sp_ψ(V_B)` with
`i_P^G(ρ ⊗ ψ)` (proof of VI.8.4, by Corollary VI.8.2), so irreducibility of one is
irreducibility of the other. The statement records the implication from the
induction to the fiber, the only direction the Example needs. Two published
conventions enter: `leviInductionFunctor` normalizes by the full-`P` half modulus,
while `LeviInduced` uses Renard's Levi normalization (see
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md)); and the universal
family acts by `m · (b ⊗ w) = χ_un(m) b ⊗ σ(m) w`, whose specialization at `ψ` is
`ψ(m) σ(m)`, the published twist by `ψ`. A proof of the statement has to compare
the two normalizations at `B = ℂ`, as noted in the task context of the target.

## Proof of `endomorphismScalar_leviInduced`

The binders are those of the published `InductionFlatStatement`
([RenardFamilyParabolicFlatnessStatements](RenardFamilyParabolicFlatnessStatements.md)):
a reduced Noetherian finitely generated `ℂ`-algebra `B`, a `B`-module `E`, and a smooth
family `σ` of `M(F)` on `E` that is flat over `B` and has finitely generated
compact-open fixed modules. Given a `G(F)`-equivariant `B`-linear `φ` on
`LeviInduced p l r hp hr hl hmul σ`, a set `Ξ` of points `B →ₐ[ℂ] ℂ` such that every
`b` vanishing on `Ξ` vanishes at all points, and irreducibility of the fiber at every
`χ ∈ Ξ`, it concludes that `φ` is `f ↦ b • f` for some `b ∈ B`.

The proof applies the published `endomorphismScalar` (the VI.8.6 Proposition) with
group `rationalPoints G` and module `LeviInduced p l r hp hr hl hmul σ`. Its inputs are:

- `G(F)` is locally profinite: `BruhatTits.rationalPoint_isLocallyProfinite`, with
  `IsAffine G.X.left` from the affine structure morphism and smoothness from
  `hG.smooth`;
- the induced action is smooth: `isSmooth_inducedRepresentation`;
- flatness and finite generation of the fixed modules: the published proofs
  `inductionFlat` and `inductionAdmissible` (VI.8.2 Lemma).

The theorem quantifies over abstract `B` and `E` so that its instance arguments are
found in a generic context. Applying `endomorphismScalar` or `inductionFlat` directly
to the concrete `B ⊗[ℂ] W` timed out comparing instances.

## Proof of `supercuspidalFamilyEndomorphism_of_statements`

After introducing the binders of the target:

1. **The ring `B`.** With `hM := hl.isConnectedReductive`, `IsAffine M.X.left`,
   smoothness of `M` and the continuity `continuous_rationalValuationImageProjection`,
   the published `rationalUnramifiedRegularFunctions_finiteType`,
   `_isNoetherianRing` and `_isDomain` show that `B` is finitely generated, Noetherian
   and a domain, hence reduced.
2. **Admissibility of `σ`.** `hAdm` (Jacquet's theorem, at the Levi `M` with its point
   topology) shows that `σ` is admissible.
3. **The universal family.** The published `isAdmissible_universalUnramifiedRepresentation`,
   with continuity of the norm characters from `rationalNormContinuousCharacter`, shows
   that `ρB` is smooth with finitely generated compact-open fixed modules. `B ⊗[ℂ] W`
   is flat over `B` by `Module.Flat.baseChange`.
4. **Generic irreducibility.** `hGen` gives a nonzero polynomial `f` such that, for
   every `ψ` in the principal open set `rationalUnramifiedPrincipalOpen M hM f`, the
   normalized induction of `σ ⊗ ψ` is irreducible.
5. **The Proposition.** Apply `endomorphismScalar_leviInduced` with `E = B ⊗[ℂ] W`
   (the target's `TensorProduct.addCommGroup` and `TensorProduct.leftModule` passed
   explicitly), `φ`, and `Ξ` the image of the principal open set under
   `ev ψ = (evaluation at ψ) ∘ B.val`. Two goals remain.
   - *Density.* If `b ∈ B` vanishes at every point of `Ξ`, the function `b.val` on
     the unramified characters is continuous (`continuous_unramifiedRegularFunction`)
     and vanishes on the principal open set, which is dense
     (`dense_rationalUnramifiedPrincipalOpen`, using `f ≠ 0`). By `Continuous.ext_on`,
     `b.val = 0`, so `b = 0` and every point vanishes on it.
   - *Fibers.* For `χ = ev ψ` with `ψ` in the principal open set, `hFiber` applied to
     `ψ`, `ev ψ`, the identity `ev ψ b = b.val ψ` (true by definition) and the
     irreducibility from step 4 gives the fiber irreducibility. It matches the goal up
     to instance paths, closed by `convert … using 2`.

## Relation to published work

The three inputs are open:

- `GenericInducedIrreducibilityStatement`
  ([RenardGenericIrreducibilityStatements](RenardGenericIrreducibilityStatements.md)),
  Theorem VI.8.5, proof task `822bbd74-8853-4535-87b2-aede25e9a259`; the published
  `RenardGenericIrreducibilityRemainingInputs` reduces it to three open inputs;
- `RationalPointsIrreducibleAdmissibleStatement`
  ([IrreducibleAdmissibleStatement](../Aubert/General/IrreducibleAdmissibleStatement.md)),
  Jacquet's theorem, a stronger form of Renard VI.2.2;
- `SupercuspidalFamilyFiberStatement`, stated here; Worker 79 is proving it within
  Task 5205.

The module asserts none of them. The final proof of the target applies
`supercuspidalFamilyEndomorphism_of_statements` to their proofs.

## Environment

Environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. No axiom is introduced.
`supercuspidalFamilyEndomorphism_of_statements` uses `set_option maxHeartbeats 400000`;
both theorems and the statement use `set_option synthInstance.maxHeartbeats 400000`,
as the target statement does.
