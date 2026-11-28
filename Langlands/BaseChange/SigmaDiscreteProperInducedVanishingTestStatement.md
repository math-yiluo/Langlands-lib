# σ-discrete series are detected by test functions killing properly induced twisted traces

Module `Langlands.BaseChange.SigmaDiscreteProperInducedVanishingTestStatement`, declaration
`Langlands.BaseChange.SigmaDiscreteProperInducedVanishingTestStatement.{u, v, uW} : Prop`.
This `Prop`-valued definition states the result without proving it. Nothing in the module is
proved.

Sources: Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), cited as HL: II.5.13, Proposition, its proof
and Remarque (printed pp. 113–114), and II.5.14, Proposition 2 (1) and its proof (printed
pp. 115–116), with II.5.4, II.5.7 and II.5.11 for the Grothendieck groups of σ-representations
and the twisted Paley–Wiener theorem used there.

## The statement in words

Let `F` be a nonarchimedean local field of characteristic zero (`F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
[CharZero F]`). Let `E : Type v` be a field with `[Algebra F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`, and let `σ : E ≃ₐ[F] E` and `l r : ℕ` with
`hE : IsCyclicAlgebra σ l`. Put `n = r + 1`. As in the Library's
`SigmaDiscreteEllipticOrbitalTestStatement`, the statement takes `Module.Finite F E` from `hE.1`,
the Hausdorff, locally compact and totally disconnected structures on `GeneralLinear (r + 1) E`
from `generalLinear_t2Space_of_finite`, `generalLinear_locallyCompactSpace_of_finite` and
`generalLinear_totallyDisconnectedSpace_of_finite`, and the Borel σ-algebra with its
`BorelSpace` instance.

Let `W : Type uW` be a complex vector space, `τ : Representation ℂ (GL_n(E)) W` with
`hτ : IsAdmissible τ` and `IsSigmaDiscreteSeries σ (r + 1) τ`, `A : SigmaIntertwiner σ (r + 1) τ`
an isomorphism of `τ` onto `τ^σ = τ ∘ entrywiseAut σ (r + 1)`, and `μ` a Haar measure on
`GL_n(E)`. Then some `φ : SchwartzBruhat (GL_n(E))` satisfies both clauses:

- (a) `twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0`, that is, `tr(τ(φ) ∘ A) ≠ 0`;
- (b) for every `B : GeneralLinear.BlockShape (r + 1)` with `2 ≤ B.length`, every complex vector
  space `X : Type uW` and every `Ξ : Representation ℂ (B.Levi E) X` with `IsAdmissible Ξ`,
  `Ξ.IsIrreducible` and `IsLeviSigmaStable σ B Ξ`, put
  `Ind_B(Ξ) = Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))`. If
  `Ind_B(Ξ)` is irreducible, then for every `h : IsAdmissible (Ind_B(Ξ))` and every
  `A' : SigmaIntertwiner σ (r + 1) (Ind_B(Ξ))`,
  `twistedDistribution μ (Ind_B(Ξ)) h A'.toLinearMap φ = 0`.

Clause (b) is, word for word at `n = r + 1`, clause (b) of the Library's
`TwistedCuspidalPseudoCoefficientExistenceStatement` (module
`Langlands.BaseChange.TwistedCuspidalPseudoCoefficientExistenceStatement`).

## Library notation

- `IsSigmaDiscreteSeries σ n τ`, `IsLeviSigmaStable σ B Ξ` (module
  `Langlands.BaseChange.PseudoCoefficient`): `τ` is admissible, irreducible, tempered, σ-stable
  and not isomorphic to the smooth induction of a smooth σ-stable representation of a proper
  standard Levi product; `Ξ` is isomorphic to `Ξ ∘ leviAut σ B`, its entrywise σ-twist.
- `BlockShape`, `B.Levi E`, `B.parabolic E`, `B.leviProjection E` (module
  `Langlands.Group.GL.Blocks`): a block shape is an ordered list of positive block sizes with
  sum `n`; `B.Levi E` is the product of the groups `GL_{n_i}(E)`; `B.parabolic E` is the
  standard upper block triangular subgroup of `GL_n(E)`, and `B.leviProjection E` its projection
  onto the block diagonal.
- `Induction.smoothInduced P ρ` (module `Langlands.Representation.Induction.Definitions`): right
  translation on the smooth functions `f` on `GL_n(E)` with `f(p x) = ρ(p) f(x)`. This is
  unnormalized induction; its carrier lies in `Type (max v uW)`.
- `SigmaIntertwiner σ n τ` and `twistedDistribution` (modules
  `Langlands.BaseChange.TwistedCharacter` and `Langlands.BaseChange.TwistedCharacter.Basic`):
  an isomorphism of `τ` onto `τ^σ`, and the distribution `φ ↦ tr(τ(φ) ∘ A)` with
  `τ(φ) = ∫ φ(g) τ(g) dμ(g)`.
- `SchwartzBruhat (GL_n(E))`: locally constant compactly supported complex functions.

## Design

- **Nonzero trace, no central character.** HL's twisted pseudo-coefficients lie in
  `C^∞_c(G(E), χ)` for the central character `χ` of `τ` and have twisted trace `1` at `(τ, A)`.
  The statement asks only for a compactly supported `φ` with nonzero twisted trace at `(τ, A)`,
  and for nothing on the other tempered representations. It is the form in which the
  vanishing on properly induced representations is used in the Library's
  `SigmaDiscreteEllipticOrbitalTestReduction`.
- **Irreducible induced representations, every intertwiner.** HL state the vanishing for the
  σ-representation `ι_α(Ξ, B)` with the intertwiner induced from `B : Ξ ≅ Ξ^σ`. When `Ind_B(Ξ)`
  is irreducible and admissible, Schur's lemma makes every `A'` a nonzero scalar multiple of
  that induced intertwiner, so the vanishing for every `A'` is equivalent to HL's. When the
  induced representation is reducible, an arbitrary `A'` may act differently on its
  constituents; the statement makes no claim there. The admissibility proof `h` is an input of
  the trace, not a conclusion.
- **Unnormalized induction.** HL's `ι_α` is normalized induction. For the modulus character
  `δ_B` of the parabolic, `Ind_B(Ξ)` is the normalized induction of `Ξ ⊗ δ_B^{-1/2}`. Since
  `|σ(x)|_E = |x|_E`, `δ_B` is invariant under entrywise `σ`, so `Ξ ⊗ δ_B^{-1/2}` is irreducible
  and σ-stable exactly when `Ξ` is. HL's vanishing on all `ι_α(Ξ, B)` with `(Ξ, B)` irreducible
  is therefore the same family of representations.
- **σ-stable inducing data.** `IsLeviSigmaStable σ B Ξ` restricts to σ-stable `Ξ`, as HL do.
  Without it, for a quadratic twist the induction of `ξ ⊗ ξ^σ` with `ξ^σ ≇ ξ` can itself be
  σ-stable and σ-discrete, and its twisted trace need not vanish.
- **`n = r + 1`.** The setting is that of `SigmaDiscreteEllipticOrbitalTestStatement`. At
  `r = 0` no block shape of `1` has two blocks, so clause (b) is empty.
- **Relation to the cuspidal existence statement.** A σ-discrete series is tempered and has a
  central character `χ`. Clauses (a) and (b) of `TwistedCuspidalPseudoCoefficientExistenceStatement`
  at `n = r + 1` with this `χ` then give the present statement: a twisted pseudo-coefficient has
  twisted trace `1` at `(τ, A)`.

## Provenance and proof route

This is a derived statement. HL prove the existence of twisted pseudo-coefficients (II.5.13,
Proposition) as follows. A `ℤ`-linear form `Φ` on the Grothendieck group of σ-representations
of `G(E)` is built with `Φ[τ, A] = 1`, scaling with the intertwiner (`Φ[Π, λA] = λ Φ[Π, A]`),
zero on the σ-representations properly induced from σ-stable Langlands data (the subgroup
`G^L_ind(G(E), σ)` of II.5.11) and zero on the essentially tempered σ-representations outside
the unramified twists of `(τ, A)`. The twisted Paley–Wiener theorem (II.5.7, after Rogawski)
gives a locally constant compactly supported `φ̃` on `G(E)` with `Θ^{A'}_{Π'}(φ̃) = Φ[Π', A']`
for every strongly irreducible σ-representation `(Π', A')`. The pseudo-coefficient is the
central average `φ = φ̃_χ`.

The function `φ̃` itself is the witness here:

1. `Θ^A_τ(φ̃) = Φ[τ, A] = 1`, so clause (a) holds (twisted traces for other Haar measures are
   positive multiples).
2. By II.5.13, Remarque, `Θ^{A'}_{Π'}(φ̃) = 0` on `G^L_ind(G(E), σ)` and at every strongly
   irreducible essentially tempered `(Π', A')` with `Π'` not essentially σ-discrete.
3. The proof of II.5.14, Proposition 2 (1) (printed pp. 115–116) writes `[ι_α(Ξ, B)]`, for
   `l(α) > 1` and `(Ξ, B)` an irreducible σ-representation of `G_α(E)`, modulo the subgroup
   `G_{0+}(G(E), σ)` on which every twisted trace vanishes (II.5.4, Remarque, and II.5.7), as a sum of
   integral multiples of classes of the two kinds of step 2. This decomposition does not use
   the central character of `Ξ`. So `Θ^{A'}_{Π'}(φ̃) = 0` for `(Π', A') = ι_α(Ξ, B)`.
4. The translation to unnormalized induction and to arbitrary intertwiners is explained under
   Design.

HL write `G(E)` for `GL_n(E)`, `Θ^{A}_{Π}(φ)` for `tr(Π(φ) ∘ A)`, and `(Π, A)` for a σ-representation.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.5.4 (printed pp. 102–103); II.5.7, twisted
  Paley–Wiener theorem (printed p. 105); II.5.11 (printed pp. 109–112); II.5.13, Définition, Proposition, its proof
  and Remarque (printed pp. 113–114); II.5.14, Proposition 2 (1) and its proof (printed
  pp. 115–116).
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Corollary 2.10 (printed p. 18), the
  existence of twisted pseudo-coefficients in characteristic zero.
