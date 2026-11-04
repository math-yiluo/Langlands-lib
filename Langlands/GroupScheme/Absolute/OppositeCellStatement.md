# The opposite open cell for a smooth affine group over a field

This is the unchanged `OppositeCellStatement` originally stated by Worker 1234
in `Absolute.BorelStatement`. Its full name, universe, hypotheses and
`Prop`-valued body are preserved. The statement is isolated so that its proof
and the connectedness and generic-centralizer consequences can be used without
importing Borel or parabolic classification statements. `BorelStatement`
continues to import it.

For `k : Type u`, write `S = Spec (CommRingCat.of k)`.
For every field `k`, every group scheme `G` over `S` with `Smooth G.X.hom` and `IsAffineHom G.X.hom`,
every cocharacter `χ : (Gm S).toGrp ⟶ G`, and all homomorphisms `iU : U ⟶ G`
and `iP : P ⟶ G` such that:

- `iU` represents `Dynamic.unipotent χ⁻¹`, where
  `χ⁻¹ = CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ` is the composite of
  `χ` with the inversion `t ↦ t⁻¹` of `𝔾_m` (`Gm.powerHom S (-1) = (-1) • 𝟙`);
- `iP` represents `Dynamic.parabolic χ`;

the morphism of schemes underlying
`(fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom) : U.X ⊗ P.X ⟶ G.X` is an
open immersion. Here `U.X ⊗ P.X` is the fibre product `U ×_S P` in `Over S`,
and the product of the two points of `G` over `U ×_S P` is the multiplication
morphism `(u, p) ↦ u p`.

Connectedness of `G` is not assumed. Smoothness and affineness of `G` imply that
`G` is of finite type over `k`.

Sources: Conrad–Gabber–Prasad, Proposition 2.1.8(3): over a field `k`, for an
affine `k`-group `G` of finite type, the multiplication map
`U_G(−λ) × P_G(λ) → G` is an open immersion. Conrad, Theorem 4.1.7(4): the same
for smooth `G` over any ring. **Derived**: the representability form. The
statement is conditional on closed subgroups representing `U(χ⁻¹)` and `P(χ)`;
their existence (Conrad, Theorem 4.1.7(1)) is a separate result.

The proof is in [`OppositeCellProof`](OppositeCellProof.md). Source identifiers
are `conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 2.1.8(3), printed
p.53 / PDF p.79, and `conrad-2014-reductive-group-schemes`, Theorem 4.1.7(4),
pp.112–113 / PDF pp.112–113. This separation introduces no new statement or
mathematical hypothesis.
