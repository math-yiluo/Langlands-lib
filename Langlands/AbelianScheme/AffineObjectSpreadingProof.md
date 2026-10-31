# Spreading an abelian scheme over an affine base to a finitely generated subring: proof

## Statement proved

`Langlands.AbelianScheme.affineObjectSpreading` proves
`Langlands.AbelianScheme.AffineObjectSpreadingStatement.{u}` (module
`Langlands.AbelianScheme.AffineObjectSpreadingStatement`): for every commutative ring
`R : Type u` and every abelian scheme `A` over `Spec R`, there are a finite set `s ⊆ R` and an
abelian scheme `A₀` over `Spec (Subring.closure s)` such that the base change of `A₀` along
`Spec R ⟶ Spec (Subring.closure s)` (induced by the inclusion of the subring) is isomorphic to
`A` in `AbelianScheme (Spec R)`. The theorem takes no hypothesis.

## Proof

The proof reduces the finite-subring form to the finitely generated subalgebra form, proved in
the Library as `Langlands.AbelianScheme.subalgebraDescent` (module
`Langlands.AbelianScheme.SubalgebraDescentProof`). It uses no ring isomorphism between
subalgebras and subrings.

1. Apply `subalgebraDescent` to `CommRingCat.of R` and `A`. This gives a `ℤ`-subalgebra `R₀` of
   `R` with `R₀.FG`, an abelian scheme `A₀'` over `Spec R₀` and an isomorphism
   `e : A ≅ (baseChange (Spec.map (ofHom (algebraMap R₀ R)))).obj A₀'`.
2. By the definition of `Subalgebra.FG`, there is a finite set `s : Finset R` with
   `Algebra.adjoin ℤ s = R₀`. By Mathlib's `Algebra.adjoin_int`,
   `Algebra.adjoin ℤ s = subalgebraOfSubring (Subring.closure s)`, so
   `mem_subalgebraOfSubring` shows that every element of `R₀` lies in `Subring.closure s`.
3. Hence the inclusion `algebraMap R₀ R` corestricts (`RingHom.codRestrict`) to a ring map
   `ψ : R₀ →+* Subring.closure s`. Its composite with `(Subring.closure s).subtype` is
   `algebraMap R₀ R`, which holds pointwise by `rfl`.
4. Take `A₀ := (baseChange (Spec.map (ofHom ψ))).obj A₀'`, an abelian scheme over
   `Spec (Subring.closure s)`. The required isomorphism is the composite of three isomorphisms:
   - the inverse of `AbelianScheme.baseChangeCompIso` (module
     `Langlands.AbelianScheme.BaseChangeCoherence`), which identifies the iterated base change
     of `A₀'` with its base change along the composite
     `Spec.map (ofHom (closure s).subtype) ≫ Spec.map (ofHom ψ)`;
   - `eqToIso` for the equality of this composite with `Spec.map (ofHom (algebraMap R₀ R))`.
     It holds by `Spec.map_comp`, `CommRingCat.ofHom_comp` and the composite identity of step 3;
   - `e.symm`.

The target writes the base change on the left of the isomorphism, which is why `e` is inverted.

## Axioms

`lean_check` inspection of `Langlands.AbelianScheme.affineObjectSpreading` reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is a formal bridge, internal to the project, between two Library statements. The
mathematical content (descent of an abelian scheme to a finitely generated subring, Stacks
Project *Limits of Schemes*, Lemma 32.10.1, tag 01ZM, together with the property-descent results
cited in `Langlands/AbelianScheme/SubalgebraDescentStatements.md`) lies entirely in
`subalgebraDescent`. The only additional facts are the Mathlib identity
`Algebra.adjoin ℤ s = subalgebraOfSubring (Subring.closure s)` and the coherence of iterated
base change of abelian schemes.
