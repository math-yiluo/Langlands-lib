# Same-Levi generic irreducibility from Renard VI.8.4 and one irreducible twist

`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericInductionIrreducibilityFromInputsStatement.{u, v}`
is a closed proposition. It is an implication with two premises and one
conclusion, all three at the same universes `u` (field and group) and `v`
(Levi representation carriers):

1. `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, v}`
   (Renard VI.8.4, Proposition). Take a nonarchimedean local field `k`, a
   connected reductive `G` with its canonical point topology, and an actual
   rational parabolic `p : P ⟶ G`. The parabolic has rational Levi
   `l : M ⟶ P`, geometric unipotent radical `r : U ⟶ P`, and multiplication
   isomorphism. Let `ρ` be an irreducible smooth complex representation of
   `M(k)` (no admissibility hypothesis), and `ψ₀` an unramified character of
   `M(k)` (trivial on the common kernel of the rational-character norms) such
   that `leviInductionFunctor p l r … (ρ ⊗ ψ₀)` is irreducible. Then some
   polynomial `f` in the full rational-norm unramified-character coordinates
   of `M` has `ψ₀` in its principal open
   `Plancherel.rationalUnramifiedPrincipalOpen M … f`. Moreover every `ψ` in
   that principal open has irreducible normalized induction
   `leviInductionFunctor p l r … (ρ ⊗ ψ)`.
2. `Langlands.Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement.{u, v}`
   (the existence consequence of Konno, Theorem 4.2). For the same kind of
   data, every irreducible admissible smooth complex representation `ρ` of
   `M(k)` has an unramified character `ψ` of `M(k)` (trivial on the common
   kernel of the rational-character norms) such that
   `leviInductionFunctor p l r … (ρ ⊗ ψ)` is irreducible.

The conclusion is the published target
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericInductionIrreducibilityStatement.{u, v}`,
unchanged. In that target, `G` is a connected reductive group over a
nonarchimedean local field of any characteristic, with its canonical point
topology. Take a maximal split torus, a generic cocharacter, the
standard-cocharacter hypothesis and closed literal unipotent radicals, and
simple-root subsets `I`, `J` with `g ∈ G(k)` conjugating `levi I` to `levi J`.
Assume the Levi scheme of `J` is connected reductive, and let `σ` be an
irreducible admissible smooth complex representation of the literal Levi
`levi i ν J`. Then some nonzero polynomial `p` in the actual rational-norm
unramified-character coordinates of `L_J` has the following property. For
every literal unramified character `χ` in its principal open
`leviUnramifiedPrincipalOpen i ν J hLJ p`, two normalized inductions of
`σ ⊗ χ` are irreducible:

- the normalized induction from the standard parabolic `P_J`;
- the induction from the conjugate parabolic `g P_I g⁻¹` with Levi `levi J`
  (`conjugateInductionFunctor`).

## Provenance

The statement is derived. It records which published, still unproved inputs the
reduction in
`Langlands.Representation.Aubert.General.RationalSameLeviGenericIrreducibilityReduction`
uses to reach the target. The target's own route follows Konno, Theorem 4.2
(registered original `konno-2003-langlands-classification`, pp.402–405;
arbitrary characteristic on p.384) together with algebraic openness. It applies
the argument to both actual parabolics and intersects their polynomial loci.
Each premise has its own source provenance and its own proof task:

- Renard VI.8.4 is Task 5147 (`2113598c`);
- the twist-existence statement is owned by Worker 145, as a prerequisite of
  this task.

Neither premise mentions a particular group, parabolic or representation. The
conclusion adds no hypothesis to the target.

This is a proof target, not a theorem. It does not prove the target. The
target still needs proofs of both premises.
