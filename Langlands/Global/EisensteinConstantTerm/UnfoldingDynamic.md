# Intersections of dynamic subgroups of two commuting cocharacters

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingDynamic`, namespace
`Langlands.GroupScheme.Dynamic`. Here `G` is an affine separated group scheme over an affine
base, `i : A → G` with `A` commutative, and `α`, `β` are cocharacters of `A`, so that
`χ = β ≫ i` and `τ = α ≫ i` commute. `P`, `Z`, `U` denote the dynamic parabolic, centralizer and
identity-limit subgroup functors `parabolic`, `centralizer`, `unipotent`.

## Results

For a commuting refinement `ψ` of `χ` by `τ` (`IsCommutingRefinement χ τ ψ`):

- `parabolic_refinement_eq_sup`: `P(ψ) = (P(χ) ∩ P(τ)) ⊔ U(χ)` on every test scheme. The proof
  uses the Library's ordered product `parabolic_inf_parabolic_eq_mul`,
  `P(α ≫ i) ∩ P(β ≫ i) = (P(α ≫ i) ∩ Z(β ≫ i)) (P(α ≫ i) ∩ U(β ≫ i))` (module
  `Langlands.GroupScheme.Rational.StandardWeylMinimalRepresentativesProof`), together with the
  product formula `P(ψ) = (Z(χ) ∩ P(τ)) U(χ)` of the refinement;
- `unipotent_inf_parabolic_le_refinement`: `U(τ) ∩ P(χ) ≤ U(ψ)`, from the Library's
  `unipotent_inf_parabolic_eq_mul` and the product formula `U(ψ) = (Z(χ) ∩ U(τ)) U(χ)`.

## Provenance

With `χ` for `P` and `τ` for `w⁻¹ Q w`, these are root-free forms of two facts about
Bernstein–Lapid's parabolic `P_w` of Lemma 6.7 (2) (journal p. 207). The first is the identity
`P_w = (P ∩ w⁻¹ Q w) U_P`, the form in which `IsGeometricLemmaDatum` prescribes the rational
points of `P'`. The second is the inclusion `w⁻¹ U_Q w ∩ P ⊆ U_{P_w}`, the conjugate by `w⁻¹` of
`U_Q ∩ w P w⁻¹ = U_Q ∩ w U_{P_w} w⁻¹` in Lemma 6.7 (3). They are derived from the dynamic method of
Conrad–Gabber–Prasad as developed in the Library's `Dynamic` modules.
