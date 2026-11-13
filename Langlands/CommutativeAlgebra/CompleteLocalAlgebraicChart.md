# Finite-type algebraic charts of complete local algebras

This module proves the algebraic part of Stacks Project Lemma 98.12.7 (Tag 07XH),
conditional on étale approximation. It combines the approximation step of Lemma
98.10.1 (Tag 07XB, `artin.pdf` printed pp. 14–16) with the isomorphism argument of
Lemma 98.12.7 (printed pp. 20–21). It is stated without line bundles. The
provenance is derived: Stacks constructs its isomorphism from a versal formal
object, while here the isomorphism property is proved for every lift of an
identification modulo squares.

`exists_algebraicChart` assumes
`happrox : FiniteTypeIntEtaleCompletionApproximationStatement.{u}` and the
following data, all in universe `u`:

- a commutative ring `R` of finite type over `ℤ`;
- a field `K` of finite type over `R`;
- a Noetherian local `R`-algebra `A`, complete for its maximal ideal `m_A`;
- a surjective `R`-algebra map `ε : A →ₐ[R] K`;
- a finite-type `R`-algebra `B` with `β : B →ₐ[R] A`.

It gives a finite-type `R`-algebra `T`, a surjection `εT : T →ₐ[R] K`, an ideal
`mT = ker εT`, an `R`-algebra map `βT : B →ₐ[R] T` and an `R`-algebra map
`φ₂ : A →ₐ[R] T / mT ^ 2` such that:

1. `φ₂ ∘ β = (T → T / mT ^ 2) ∘ βT`;
2. if `φ₂ a` is the class of `t`, then `εT t = ε a`;
3. for every `n ≥ 2` and every `R`-algebra map `φ : A →ₐ[R] T / mT ^ n` whose reduction
   modulo `mT ^ 2` is `φ₂`, the map `φ` is surjective with kernel `m_A ^ n`.

In particular `φ₂` identifies `A / m_A ^ 2` with `T / mT ^ 2`, and every lift of `φ₂` is
an isomorphism `A / m_A ^ n ≅ T / mT ^ n`.

## Proof

1. **Presentation.** `LocalPresentationModSquare` gives `σA : S → A` from a
   polynomial ring `S = R[x_i]` in finitely many variables, surjective modulo
   `m_A ^ 2`. Let `𝔪 = ker (ε ∘ σA)`, a maximal ideal. The ring `S` is of finite
   type over `ℤ`, so `happrox` gives étale approximation for `P = S_𝔪`.
2. **Completion.** `MaximalLocalizationCompletion` extends `σA` to a surjection
   `π : P̂ → A`. The preimage of `m_A ^ n` is `ker π + (maximalIdeal P̂) ^ n`.
3. **Generators and syzygies.** `P̂` is Noetherian
   (`AdicCompletion.isNoetherianRing_of_isNoetherianRing`). Hence `ker π` is generated
   by finitely many `b j`, and their relations by finitely many rows `Ks l`. Let `c`
   be the Artin–Rees constant of `ArtinReesSyzygyApproximation`.
4. **Equations.** Present `B` by `ψB : MvPolynomial (Fin m) R ↠ B` with finitely many
   generating relations `F j`. Lift the images of the variables to `ã i ∈ P̂`. Then
   `F j (ã) ∈ ker π`, so `F j (ã) = ∑ cc j i * b i`. These equations and the
   syzygies `∑ Ks l i * b i = 0` form a finite system in variables
   `Y i, Bv i, Cv j i, Kv l i` with solution `ã, b, cc, Ks` in `P̂`.
5. **Approximation.** `EtaleApproximationModel` with order `N = c + 2` gives
   `T₀`, `σT`, `vT`, `ι₀`. In `T₀` the system has an exact solution `vT(…)` that is
   congruent to the given one modulo `(maximalIdeal P̂) ^ N`, and `T₀ = S + u₀ ^ 2`.
   The Artin–Rees comparison gives the hypothesis `hAR` of
   `ApproximateQuotientRigidity` for `b'' i = vT (Bv i)`.
6. **The chart.** `T = T₀ / (b'')`. `εT` is induced by `ε ∘ π ∘ ι₀`, which kills
   every `b''`. Its kernel is the image of `u₀` because `ker π ≤ maximalIdeal P̂`.
   `βT` sends the `i`-th generator of `B` to the class of `vT (Y i)`. It is well
   defined because the relations `F j (Y) = ∑ Cv j i * Bv i` hold in `T₀`.
7. **Modulo squares.** The kernels of `S → A / m_A ^ 2` and `S → T / mT ^ 2` are
   both `σ⁻¹ (ker π + (maximalIdeal P̂) ^ 2)`. Here
   `ker π + 𝔫̂ ^ 2 = (ι₀ b'') + 𝔫̂ ^ 2` because `b'' ≡ b` modulo `𝔫̂ ^ N`, `N ≥ 2`.
   Both maps are surjective. `φ₂` is the induced isomorphism
   `A / m_A ^ 2 ≅ S / ker ≅ T / mT ^ 2`, composed with `A → A / m_A ^ 2`.
8. **Properties.** (1) is checked on the generators of `B`: approximating `ã i` by
   `σ s` modulo `𝔫̂ ^ 2` identifies both sides with `q 2 s`, using
   `mem_u₀_pow_of_mem`. (2) holds since `φ₂ a = q 2 s` with `a ≡ σA s`.
   (3) is `ApproximateQuotientRigidity.rigidity`. Its locality hypothesis follows
   from (2), and its reduction hypothesis from the construction of `φ₂`.

`algebraicChartOfEtaleApproximation` is the same implication as a definition. It
is `@exists_algebraicChart`, with the type of that theorem. The defining linter
for Prop-valued definitions is disabled for this one declaration.
