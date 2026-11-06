# The unitary case of Renard VII.1.3 from its inputs

Author: Worker 1507. Module `Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryProof`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module proves the published `MaximalLeviSupercuspidalReducibilityUnitaryStatement` (module `MaximalLeviReducibilityReductionStatements`) from explicit premises. The premises are the eight input statements of `MaximalLeviReducibilityUnitaryInputs` and two instances of the published, still unproved, `RationalPointsIrreducibleAdmissibleStatement` (Jacquet's theorem). The result is therefore conditional: none of the premises is proved here, and no axiom is added. The positive unramified twist of the second case comes from the proved theorem `exists_positive_unramifiedTwist_unitaryCentralCharacter` of Worker 1517's module `PositiveUnramifiedCentralTwist`, and the transfer of supercuspidality to twists from `properJacquet_subsingleton_unramifiedTwist` of `UnramifiedTwistRadicals`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source ID `renard-2026-representations-groupes-reductifs-padiques`, Théorème VII.1.3 and its proof (printed pp.224–226 / PDF pp.230–232). The Lean proof follows the source's case split on the central character of `ρ`, but takes a shorter route in the non-unitary case (see "Comparison with the source").

## Main theorems

- `maximalLeviSupercuspidalReducibilityUnitary_of_inputs (hI0 hI0G hI1 hIA hIU hN hHd hK1 hK2 hC) : MaximalLeviSupercuspidalReducibilityUnitaryStatement.{u, v}`. The premises are:
  - `hI0 : RationalPointsIrreducibleAdmissibleStatement.{u, v}` (irreducible representations of `M(F)` are admissible) and `hI0G : RationalPointsIrreducibleAdmissibleStatement.{u, max u v}` (the same for `G(F)` in the universe of inductions);
  - `hI1`, `hIA`, `hIU`, `hN`, `hHd`, `hK1`, `hK2`, `hC`: the input statements I1, IA, IU, N, Hd, K1, K2 and C of `MaximalLeviReducibilityUnitaryInputs`.

  The wrapper introduces the binders of the statement, installs `IsAffineHom` for `G` and `M` and the locally compact and nonarchimedean instances on the Levi points (`leviPoints_locallyCompactSpace`, `leviPoints_nonarchimedeanGroup`), and applies the core theorem.
- `maximalLeviReducibilityUnitary_core`: the same conclusion for one fixed actual maximal proper parabolic `p, l, r` and one irreducible supercuspidal `ρ` of `M(F)` with `i_P^G ρ` reducible and having a `UnitaryCentralCharacter`, with the topological instances as explicit section variables.

## The proof of `maximalLeviReducibilityUnitary_core`

Throughout, `π = (leviInductionFunctor p l r hp hr hl hmul).obj ρ`. First `ρ` is nonzero (`exists_ne_zero_of_isIrreducible`) and admissible (`hI0`, with `M` connected reductive by `hl.isConnectedReductive`). The proof then splits on `Nonempty (UnitaryCentralCharacter ρ.representation)`.

### Case A: `ρ` has a unitary central character

1. `ρ` is unitarizable by I1, so `π` is admissible by IA, unitarizable by IU and nonzero by N.
2. The published `admissibleUnitarySemisimplicity` (Renard IV.2.2, Corollaire), with the cofinal compact open subgroups `compactOpenCofinal_of_nonarchimedean`, makes `π.representation` semisimple.
3. `exists_nonscalar_endomorphism_of_semisimple` gives an endomorphism `f : π ⟶ π` that is not a scalar, because `π` is reducible.
4. K1 applied to `f` excludes the scalar alternative and returns `g`, `φ` with the normalizing and non-Levi conditions and `T : ρ ≃ₗ[ℂ] ρ` with `T (ρ m x) = ρ (φ(F) m) (T x)`. This is the conclusion with `ψ = 1`, which is positive (value `1`).

### Case B: `ρ` has no unitary central character

1. `exists_positive_unramifiedTwist_unitaryCentralCharacter` gives a positive unramified `ψ` and a unitary central character `c₀` of `ρ₀ = ρ.twist ψ`. Write `ρ₂ = ρ₀.twist ψ`, i.e. `ρ ψ²`.
2. `ρ₀` and `ρ₂` are irreducible (`SmoothRep.isIrreducible_twist_iff`) and supercuspidal (`properJacquet_subsingleton_unramifiedTwist`, twice). `ρ₀` is admissible by `hI0` and unitarizable by I1.
3. C gives an irreducible unitarizable `W` of `G(F)` with an injective `W ⟶ π` or a surjective `π ⟶ W`. `W` is admissible by `hI0G` and nonzero.
4. The isomorphism `ε : ρ₀.twist ψ⁻¹ ≅ ρ` (`SmoothRep.mkIso` of `equivOfRepresentationEq (twist_inv_twist …)`) induces `E : i_P^G(ρ₀ ψ⁻¹) ≅ π`. Since `ψ` is positive real, `ψ(m) · conj(ψ⁻¹(m)) = 1`, which is the condition of Hd with `σ = ρ₀`, `χ = ψ⁻¹` and `χ' = ψ`; then `σ ⊗ χ' = ρ₂`.
5. *Subrepresentation.* From `f : W ⟶ π` injective, `f ≫ E.inv` is injective, and Hd gives a nonzero `h : i_P^G ρ₂ ⟶ W`. Then `h ≫ f : i_P^G ρ₂ ⟶ π` is nonzero, and K2 with `τ = ρ`, `τ' = ρ₂` gives `ρ₂ ≅ ρ` or `g, φ, T : ρ ≃ ρ₂ ∘ φ(F)`. In the second case `maximalLeviReducibility_conclusion_of_twist_sq` gives the conclusion with the character `ψ · ψ`.
6. *Quotient.* From `f : π ⟶ W` surjective, `E.hom ≫ f` is surjective, and Hd gives a nonzero `h : W ⟶ i_P^G ρ₂`. Then `f ≫ h : π ⟶ i_P^G ρ₂` is nonzero, and K2 with `τ = ρ₂`, `τ' = ρ` gives `ρ ≅ ρ₂` or `g, φ, T : ρ₂ ≃ ρ ∘ φ(F)`. In the second case `maximalLeviReducibility_conclusion_of_twist_sq_symm` gives the conclusion, with `(g⁻¹, φ⁻¹, T⁻¹)` and the character `ψ · ψ`.
7. The alternative `ρ ≅ ρ ψ²` (in either direction) contradicts the case hypothesis by `nonempty_unitaryCentralCharacter_of_iso_twist_twist`.

## Helper results

- `smoothRep_twist_representation_apply`: `(A.twist χ hχ).representation h x = χ h • A.representation h x` (by `rfl`).
- `smoothRep_hom_injective_of_iso`, `smoothRep_hom_surjective_of_iso`: the underlying map of an isomorphism of smooth representations is injective, resp. surjective.
- `exists_nonscalar_endomorphism_of_semisimple`: a nonzero semisimple smooth representation that is not irreducible has a non-scalar endomorphism. Proof: since `π` is not irreducible and `⊥ ≠ ⊤`, some subrepresentation `S` is neither `⊥` nor `⊤`. Semisimplicity (`exists_isCompl`) gives a complement `C`, which is not `⊥`. The linear projection `Submodule.projection` onto `S` along `C` is an intertwining map because `S` and `C` are invariant. It fixes a nonzero `s ∈ S` and kills a nonzero `t ∈ C`, so it is not a scalar.
- `nonempty_unitaryCentralCharacter_of_iso_twist_twist`: if `ψ` takes positive real values, `ρ ψ` has a unitary central character `c` and `ρ ≅ ρ ψ²`, then `ρ` has a unitary central character. Proof: for central `z` and `x ≠ 0`, comparing the intertwining identity of `e.hom` at `z` with the action `ψ(z) ρ(z) = c(z)` on both sides gives `ψ(z)⁻¹ = ψ(z)`. With `ψ(z) = t > 0`, `t² = 1` forces `t = 1`. So `c` itself is a unitary central character of `ρ`.
- `rationalPoints_map_hom_map_inv`: `φ(F) (φ⁻¹(F) m) = m` for `φ : M ≅ M`.
- `maximalLeviReducibility_conclusion_of_twist_sq`: from `g, φ` with the normalizing and non-Levi conditions and `T : ρ ≃ₗ ρ ψ²` with `T (ρ m x) = (ρ ψ²)(φ(F) m) (T x)`, the conclusion holds with the positive character `ψ · ψ`.
- `maximalLeviReducibility_conclusion_of_twist_sq_symm`: from `g, φ` as above and `T : ρ ψ² ≃ₗ ρ` with `T ((ρ ψ²)(m) x) = ρ (φ(F) m) (T x)`, the conclusion holds with `g⁻¹`, `φ.symm`, `T.symm` and `ψ · ψ`. The normalizing identity for `(g⁻¹, φ⁻¹)` follows from `G.innerIso_inv_hom` and `Iso.inv_comp_eq`. `g⁻¹ ∉ pointImage (l ≫ p)` because the image is a subgroup. The intertwining identity is that of `T` at `φ⁻¹(F) m`.

## Comparison with the source

- Case A is the source's first case (PDF p.231): `ρ` is unitary, `π` is unitary and therefore completely reducible, and the computation (VII.1.3.1) of `End(π)`, here input K1, gives a nonscalar endomorphism only if some `w` normalizing `M` has `ρ^w ≃ ρ`.
- In Case B the source shows, using the length-two filtration and Casselman's criterion, that a constituent `π_1` is unitary, that `ρ' = ρ^w = ρ^h` and that `M = M'`. The Lean proof uses input C for the unitary constituent, Hd in place of `π_1^h = π_1` and `π^h = i_P^G(ρ^h)`, and K2 in place of the identification `ρ^w = ρ^h`. It does not use the opposite parabolic or the hermitian dual of `ρ`: for `ρ = ρ₀ ψ⁻¹` with `ρ₀` unitary, `ρ^h ≃ ρ₀ ψ = ρ ψ²`, which is the representation `ρ₂` above.
- The source writes the result as `ρ^w ≃ ρ ⊗ ψ` with `ψ` positive unramified. The Lean conclusion produces `ψ · ψ` in Case B and `1` in Case A, both positive unramified characters of `M(F)` in `Plancherel.unramifiedCharacters`.
- The excluded alternative `ρ ψ² ≃ ρ` is not discussed in the source, which reaches `ρ^w ≃ ρ^h` with `w` nontrivial directly from the filtration. In the Lean proof K2 also allows the trivial alternative, which step 7 rules out.

## Status

The module is conditional on its ten premises. A proof of the published target `MaximalLeviSupercuspidalReducibilityStatement` combines it with the twist reduction `maximalLeviSupercuspidalReducibility_of_unitary` and a proof of `MaximalLeviUnitaryCentralTwistStatement` (Worker 1517's modules), once the premises are proved.
