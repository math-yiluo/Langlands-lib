# Existence of coherent valued rank-one coordinates over the maximal unramified field

`Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinatesStatement` is an unproved proposition definition at arbitrary universe `u`. It quantifies over every `F : Type u` with field, valuative relation, topology and nonarchimedean local field instances; every actual affine group scheme `H` over `K = UnramifiedClosure F`; every supplied `B : MaximalUnramified.BuildingData F H`; every proof `hZ : IsTorus B.centralizer.Z`; and every `b : characterLattice B.S` belonging to `RelativeRoot.indivisibleRoots B.i`. There is no characteristic restriction.

For each such root it asserts both implications:

- If `2 • b ∉ relativeRoots B.i`, then `Nonempty (ValuedSL2RootCoordinates B hZ b)`.
- If `2 • b ∈ relativeRoots B.i`, then `Nonempty (ValuedSU3RootCoordinates B hZ b)`.

Thus actual double-root membership determines the alternative. The extension fields, both coordinate equivalences, the full-centralizer characters for both signs, the common rank-one homomorphism, the actual coroot morphism from the induced torus, and the point of the supplied apartment are conclusions. Their precise types and matrix conventions are given in [the definitions module](QuasiSplitValuedRankOneCoordinates.md).

In the SL₂ branch the same finite separable `E/K` supplies additive coordinates for `b` and `-b`. One `rho` sends the determinant-one upper and lower transvections to the two coordinate images; the coroot morphism on `K`-points sends `t : Eˣ`, through the actual Weil-restriction units equivalence and `j`, to `rho(diag(t,t⁻¹))`. At one point `origin`, both coordinate depths are the `K`-normalized henselian separable additive extension valuation on `E`.

In the SU₃ branch one compatible tower `K → E → L` has `E/K` and `L/K` finite separable and `L/E` separable quadratic. Both coordinate equivalences use the identical unitary parameter group, with separate full-centralizer characters and literal zero-first-coordinate identifications of the positive and negative double-root groups. One `rho` on the actual special unitary matrix subgroup sends the upper and opposite matrices to those coordinate images. The actual coroot morphism from `Res_{L/K} Gm`, compared through its rational-units equivalence and followed by `j`, sends `t : Lˣ` to `rho(diag(t,bar(t)/t,1/bar(t)))`. At one point `origin`, both root depths are `towerDepth K E L` and both double-root depths are `towerCentralDepth K E L`.

Every valuation in these conclusions uses `MaximalUnramified.valuation F` and its published henselianity proof. Every depth equality is in `WithTop ℝ`, including the identity. In particular neither `E` nor `L` is renormalized. The point may vary with `b`, while both signs and their doubles use the same point for a fixed root. Injectivity of `rho` is not required.

The proposition takes the building data and the torus-centralizer proof as inputs. It adds no premise asserting coordinates, an apartment existence/comparison target, local coroot or torus-root commutator estimates, S1, S2, or any further building/filtration property.

This is a derived interface from Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered source `kaletha-prasad-2023-bruhat-tits-new-approach`: Construction 6.1.17, Remark 6.1.18 and Proposition 6.1.19 (PDF pp.236–238), comparison Proposition 6.2.6 (PDF p.247), quasi-split rank-one reduction in Proposition 7.1.1 (PDF pp.268–271), and induced-torus functoriality in §7.2, especially Lemma 7.2.3 (PDF pp.276–277). The registered corrections `kaletha-prasad-2024-corrections`, PDF p.33, add AS 5 to Chapter 7 hypotheses; none of the downstream AS 5 estimates is assumed or concluded here. The exact bundled statement is internal packaging of these ingredients, rather than a literal source quotation. This module supplies no proof of existence; that is a separate proof obligation.
