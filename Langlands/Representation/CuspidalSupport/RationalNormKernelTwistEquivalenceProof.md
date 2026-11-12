# Renard VI.3.2(iii) on the actual norm kernel

This module proves the published proposition
`Langlands.CuspidalSupport.RationalNormKernelTwistEquivalenceStatement.{u, uV, uW}` from `RationalNormKernelOrbitTwistStatement`. The theorem is `Langlands.CuspidalSupport.rationalNormKernelTwistEquivalence`. Its type is exactly that proposition, with the three independent universe parameters `u`, `uV` and `uW`.

## What is proved

The statement is Proposition VI.3.2(iii) of David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, printed pp.143–144 / PDF pp.149–150. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Fix a nonarchimedean local field `F` of either characteristic, a connected reductive group scheme `G` over `F` (rank zero and anisotropic groups included), and its rational-point group with the canonical topology `rationalPointTopology F G.X`. For irreducible smooth complex representations `π₁` (carrier in universe `uV`) and `π₂` (carrier in universe `uW`), write `H = Plancherel.rationalCommonNormKernel G` (Renard's `⁰G`, V.2.3) and `ρᵢH = πᵢ.representation.comp H.subtype` for the restriction of `πᵢ` to `H` on the same carrier. Write `XG = Plancherel.unramifiedCharacters ν` with `ν = fun χ => (Plancherel.rationalNormCharacters G χ).toMul`: the continuous characters `G → ℂˣ` that are trivial on `H` (Renard's `X(G)`). Then the theorem gives `(A ↔ B) ∧ (A ↔ C)`, where:

- `A`: `ρ₁H` and `ρ₂H` are equivalent (`Nonempty (Representation.Equiv ρ₁H ρ₂H)`);
- `B`: some `χ : XG` has `Langlands.twist χ.val.toMonoidHom π₁.representation` equivalent to `π₂.representation`. The twist acts by `g ↦ χ(g) • π₁(g)`, so this is Renard's `π₂ ≅ π₁ ⊗ χ`;
- `C`: some intertwiner `f : ρ₁H → ρ₂H` is nonzero.

The statement's Lean/Markdown pair, its imports and its hypotheses are unchanged. Irreducibility of the two representations is the only representation-theoretic premise. No finite dimension, admissibility, central character or semisimplicity is assumed.

## Proof

### Setting up

After introducing `F`, `G` and `hG`, the proof recreates the instances fixed by the statement: the affine structure map from `hG.isAffineHom`, affineness of `G.X.left`, smoothness `hG.smooth`, and the canonical topology `rationalPointTopology F G.X`. It also adds the published topological-group instance `rationalPoint_isTopologicalGroup F G`, which the generic assembly needs. The statement does not mention that instance, and adding it changes neither the topology nor the conclusion.

The proof then applies the published generic theorem `normKernelTwistEquivalence_of_finiteIndex_scalar` (module `NormKernelTwistEquivalence`) to the group `GroupScheme.rationalPoints G`, the family `ν` above, `ρ = π₁.representation` and `σ = π₂.representation`. By definition, `Plancherel.rationalCommonNormKernel G` is `Plancherel.commonNormKernel ν`. So the generic conclusion is the target conclusion verbatim. `SmoothRep.IsIrreducible` is an abbreviation for `Representation.IsIrreducible` of the underlying representation, so the two irreducibility premises are passed on unchanged.

### Inputs of the generic theorem

- **Open kernel.** `Plancherel.isOpen_rationalCommonNormKernel G` (module `RationalNormKernelTopology`): `H` is open in the canonical topology.
- **Commutator containment.** `Plancherel.commutator_le_rationalCommonNormKernel G` (module `RationalCharacterValuation`): the commutator subgroup lies in `H`.
- **Finite index of the kernel joined with the centre.** `rationalCommonNormKernel_sup_center_finiteIndex F G hG`, from the helper module `RationalNormKernelCentralFiniteIndex` submitted with this proof. It states that `H ⊔ Subgroup.center` has finite index. The helper derives it from the split component `A_G` (Renard V.2.1), injectivity of character restriction along `A_G`, and the finite central quotient (Renard V.2.6). The proof installs it as a local instance.
- **Irreducibility.** The premises `h₁ : π₁.IsIrreducible` and `h₂ : π₂.IsIrreducible`.
- **Scalar centre.** `exists_scalar_rationalPoint_center F G hG π₁ h₁` and the same for `π₂` (module `RationalPointCentralCharacter`). Every element of the centre of the point group acts on each irreducible smooth representation by a scalar. This is proved for the actual group, not assumed.

### The three implications

Inside the generic theorem, the final assembly is `normKernelTwistEquivalence_of_nonzeroIntertwiner` (module `NormKernelTwistElementary`). It proves B ⇒ A and A ⇒ C directly, takes C ⇒ B as input, and combines them into `(A ↔ B) ∧ (A ↔ C)`.

**B ⇒ A** (`restrictEquivOfTwist`). Let `χ : XG` and let `e` be an equivalence from `Langlands.twist χ π₁` to `π₂`. Membership in `XG` means `H ≤ ker χ`, so `χ(h) = 1` for `h ∈ H`. The twisted action `χ(h) • π₁(h)` therefore equals `π₁(h)` on `H`. The same linear equivalence `e` then intertwines `ρ₁H` and `ρ₂H`.

**A ⇒ C** (`exists_nonzero_intertwiner_of_equiv`). The carrier of `π₁` is nontrivial because an irreducible representation is a simple module over the group algebra (`IsSimpleModule.nontrivial`). An equivalence is injective, so it is a nonzero intertwiner.

**C ⇒ B** (`unramifiedTwistEquivOfRestrictedIntertwiner`, which calls `exists_twistIntertwiningMap_of_restrictedHom_nonzero` from module `NormKernelTwistAlgebra`). Let `f : ρ₁H → ρ₂H` be a nonzero intertwiner.

1. *Conjugation action.* The group acts on linear maps `V₁ → V₂` by `g · T = π₂(g) ∘ T ∘ π₁(g⁻¹)` (Mathlib's `Representation.linHom`). Mathlib's `Representation.invariantsEquivIntertwiningMap` identifies the `H`-intertwiners with the `H`-invariant linear maps. Since `H` is normal, the action restricts to these invariants. This is the representation `restrictedHomConjugation`. Under the identification, `f` becomes a nonzero vector `x`.
2. *Commuting operators.* Every `h ∈ H` acts trivially on the invariants (`restrictedHomConjugation_trivial`). The action therefore factors through `G/H`, which is commutative because the commutator subgroup lies in `H`. So all operators commute (`restrictedHomConjugation_commute`).
3. *Scalars on a finite-index subgroup.* If central `z` acts by `b` on `V₂` and `z⁻¹` acts by `a` on `V₁`, then `z` acts by `b·a` on the invariants (`restrictedHomConjugation_center_scalar`). Hence every element of `K = H ⊔ Subgroup.center` acts by a scalar (`restrictedHomConjugation_supCenter_scalar`). `K` is normal and, by the helper, of finite index.
4. *Finite-dimensional orbit span.* `finiteDimensional_orbitSpan` shows that the span of the orbit of `x` is spanned by the vectors `g_q · x`, where `g_q` runs over representatives of the finitely many cosets `q ∈ G/K`. So it is finite-dimensional. Neither the representations nor the full restricted Hom space need be finite-dimensional.
5. *Eigencharacter.* `exists_eigencharacter_of_finiteIndex_scalar` applies `EndomorphismBound.exists_common_eigenvector` (module `EndomorphismPowerBound`) to the commuting operators on this nonzero finite-dimensional span. This gives a nonzero common eigenvector `y`. Then `EndomorphismBound.exists_character_of_forall_eigen` collects its eigenvalues into a group homomorphism `χ : G →* ℂˣ` with `g · y = χ(g) y` for all `g`.
6. *Triviality on `H`.* For `h ∈ H`, `χ(h) y = h · y = y` and `y ≠ 0`, so `χ(h) = 1`. Thus `H ≤ ker χ`.
7. *Twist direction.* `intertwinerOfConjugationEigenvector` evaluates `π₂(g) ∘ y ∘ π₁(g⁻¹) = χ(g) y` at `π₁(g) v`. This gives `π₂(g)(y v) = y(χ(g) • π₁(g) v)`. So `y` is an intertwiner from `Langlands.twist χ π₁` to `π₂`, in exactly the direction of the target, and it is nonzero.
8. *Membership in `XG`.* `unramifiedCharacterOfTrivialOnOpenKernel` (module `NormKernelTwistElementary`) uses that `H` is open. Mathlib's `QuotientGroup.discreteTopology` makes `G/H` discrete. The character `χ` descends along `QuotientGroup.lift` to `G/H`, where it is automatically continuous. `Plancherel.quotientCharacterPullback` pulls it back to an element of `Plancherel.unramifiedCharacters ν = XG`. Its underlying homomorphism equals `χ` pointwise by definition, so the intertwiner from step 7 is an intertwiner for the twist by this element of `XG`.
9. *Equivalence.* `twistEquivOfNonzeroIntertwiner` uses `Langlands.isIrreducible_twist_iff`: a twist of an irreducible representation is irreducible. Mathlib's `Representation.IsIrreducible.bijective_or_eq_zero` then makes the nonzero intertwiner between the irreducible representations `Langlands.twist χ π₁` and `π₂` bijective. Hence it is an equivalence, which proves B.

### Comparison with Renard

Renard's proof of C ⇒ B uses part (ii) and Schur's lemma to make all of `Hom_{⁰G}(V₁, V₂)` finite-dimensional, then takes a common eigenvector there. The Lean route instead uses the finite-dimensional span of the orbit of the one given intertwiner. This needs only finite index of `⁰G Z(G)`, which is Renard's Proposition V.2.6 also used in his proof of (ii), and the scalar central action. It does not use VI.3.2(ii). The eigencharacter, its triviality on `⁰G`, and the final irreducibility step are the same as in Renard. The continuity of the character, which Renard's `X(G)` gets for free because `⁰G` is open, is proved explicitly in step 8.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
