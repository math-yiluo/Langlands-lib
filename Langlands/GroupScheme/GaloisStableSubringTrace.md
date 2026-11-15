# Trace identities in Galois-stable subrings of unramified integer rings

Authors: Worker 47.

Let `B` be a local ring that is finite free over `R`, with a Galois group `Γ` that acts
faithfully on the residue field. This module shows that a `Γ`-stable subring `P ⊆ B` which is
large enough modulo the maximal ideal contains

- a dual family `a_j, c_j ∈ P` with `∑_j a_j · g(c_j) = δ_{g,1}` for every `g ∈ Γ`, and
- an element `θ ∈ P` of trace one: `∑_{g ∈ Γ} g(θ) = 1`.

It then applies this to the ring of integers of a finite unramified Galois extension `E/F` of a
nonarchimedean local field. There a Galois-stable subring that contains the square of every unit
is large enough. These identities feed the finite-level Galois descent of root-group jumps
(Task 6754). In that application the subring is the stabilizer ring of two subgroups of a root
group, and it contains unit squares because torus elements `ν(λ)` act on the root group by
`λ²`.

Everything is in namespace `Langlands.GroupScheme`. The module sets
`backward.isDefEq.respectTransparency false`. Without it, the coercion of `galoisAction` and
the instance `Module.Finite 𝒪[F] (integers F E)` are not found by unification.

## Residue lemmas (`GaloisRingCover`, any commutative ring `B`)

| Declaration | Content |
|---|---|
| `GaloisRingCover.exists_mem_residue_eq_of_sq_mem` | `B` local with finite residue field, `P : Subring B` containing `x ^ 2` for every unit `x`: for every `x : B` there is `p ∈ P` with `residue B p = residue B x`. |
| `GaloisRingCover.inv_mem_of_sq_mem` | (`B` any commutative ring) If `P` contains the squares of all units, then for a unit `x ∈ P` the inverse `(hx.unit⁻¹ : Bˣ).val` lies in `P`. |
| `GaloisRingCover.residue_apply_eq_of_residue_eq` | For `ρ : Γ →* (B ≃ₐ[R] B)` and `B` local: if `x` and `y` have equal residues, so do `ρ g x` and `ρ g y`. |

Proof of the first lemma: every element of a finite field is a sum of two squares. In
characteristic two every element is a square (`FiniteField.isSquare_of_char_two`). In odd
characteristic, `FiniteField.exists_root_sum_quadratic` applied to `X²` and `X² - r` gives
`a² + b² = r`. A nonzero residue `s` lifts to a unit `y`, so `s² = residue (y²)` with
`y² ∈ P`. The zero residue comes from `0 ∈ P`. Adding two such lifts gives the claim.

Proof of the second lemma: `x⁻¹ = x · (x⁻¹)²`, and `(x⁻¹)² ∈ P` because `x⁻¹` is a unit.

## Dual family and trace-one element (abstract form)

Variables: `R B Γ : Type u`, `[CommRing R] [CommRing B] [Algebra R B] [IsLocalRing B]
[Module.Free R B] [Module.Finite R B]`, `[Group Γ] [Fintype Γ]`, `ρ : Γ →* (B ≃ₐ[R] B)`.
Hypotheses shared by both theorems:

- `hcard : Nat.card Γ = Module.finrank R B`;
- `hfaithful`: an element `g` with `residue B (ρ g x) = residue B x` for all `x` is `1`;
- `P : Subring B` with `hρ : ∀ g x, x ∈ P → ρ g x ∈ P`;
- `hinv`: `P` contains the inverse of each of its units;
- `hres`: `P` meets every residue class.

| Declaration | Conclusion |
|---|---|
| `GaloisRingCover.exists_dual_family_of_subring` (also `[DecidableEq Γ]`) | `∃ (n : ℕ) (a c : Fin n → B), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧ ∀ g : Γ, ∑ j, a j * ρ g (c j) = if g = 1 then 1 else 0`. |
| `GaloisRingCover.exists_trace_eq_one_of_subring` | `∃ θ ∈ P, ∑ g : Γ, ρ g θ = 1`. |

Proof of the dual family. The published `tensorHom_bijective`
(`Langlands.GroupScheme.IntegralGaloisCocycle`) says that `B ⊗_R B → (Γ → B)`,
`x ⊗ y ↦ (g ↦ x · ρ g y)`, is bijective. Choose an `R`-basis `b_j` of `B`. Index it by `Γ`
through an equivalence `ε : J ≃ Γ`; this works because `|J| = rank = |Γ|`. The matrix
`M_{ij} = ρ (ε i) (b_j)` of this map, in the `B`-bases `1 ⊗ b_j` and the standard basis, has
unit determinant. Pick `c_j ∈ P` with the same residue as `b_j` (`hres`). The matrix
`N_{ij} = ρ (ε i) (c_j)`, read in `P`, has the same image as `M` over the residue field
(`residue_apply_eq_of_residue_eq`). So `det N` is a unit of `B`. By `hinv` it is a unit of
`P`, and `N` is invertible over `P`. Let `a = N⁻¹ e_{i₀}`, where `ε i₀ = 1`. Then
`∑_j N_{ε⁻¹ g, j} a_j = δ_{g,1}` is the claimed identity.

Proof of the trace-one element. Summing the dual identity over `g` gives
`∑_j a_j · T_j = 1` with `T_j = ∑_g ρ g (c_j)`. In the local ring `B`, some summand
`a_j · T_j` is a unit, so `T_j` is a unit. `T_j` lies in `P` and is `Γ`-fixed, and so is its
inverse `t ∈ P` (`hinv`). Then `θ = c_j · t ∈ P` has trace `T_j · t = 1`.

## Unramified integer rings (`LocalUnramified`)

Variables: `F : Type u` a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), and
`E : IntermediateField F (SeparableClosure F)` with `[FiniteDimensional F E]`. The ring of
integers is the published `integers F E = integralClosure 𝒪[F] E`. The Galois action
`galoisAction F E : (E ≃ₐ[F] E) →* (integers F E ≃ₐ[𝒪[F]] integers F E)` is the published one
from `Langlands.GroupScheme.LocalUnramifiedIntegralCocycle`.

| Declaration | Content |
|---|---|
| `LocalUnramified.finite_residueField` | `Finite (ResidueField (integers F E))`. The extension `𝒪[F] → O_E` is integral and injective, hence a local homomorphism. Then `ResidueField.finite_of_finite` applies to the finite residue field of `F`. |
| `LocalUnramified.exists_dual_family_of_sq_mem` | `[IsGalois F E]`, `hE : E ≤ inertiaFixedField F`, `P : Subring (integers F E)` stable under every `galoisAction F E g`, `hsq : ∀ x, IsUnit x → x ^ 2 ∈ P`. Conclusion: `∃ n (a c : Fin n → integers F E), (∀ j, a j ∈ P) ∧ (∀ j, c j ∈ P) ∧ ∀ g : E ≃ₐ[F] E, ∑ j, a j * galoisAction F E g (c j) = if g = 1 then 1 else 0` (decidable equality from `Classical`). |
| `LocalUnramified.exists_trace_eq_one_of_sq_mem` | Same hypotheses. Conclusion: `∃ θ ∈ P, ∑ g : E ≃ₐ[F] E, galoisAction F E g θ = 1`. |

Both are the abstract theorems with `R = 𝒪[F]` and `B = O_E`. The inputs are the published
`card_galois` (`|Gal(E/F)| = rank`) and `galoisAction_faithful` (unramified: the action on the
residue field is faithful), together with the two residue lemmas above.

## Provenance

Internal. The dual family is the standard normal-basis argument for finite étale Galois covers
of local rings. Here it is refined so that the coefficients lie in a prescribed stable subring.
The trace-one element is the surjectivity of the trace for unramified extensions. The
sum-of-two-squares fact for finite fields is classical.
