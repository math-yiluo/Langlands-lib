# Standard Levi split components and root annihilators

Author: Worker 1230.

`StandardLeviCentralDirectionsStatement` is the conjunction of two proposition targets over every field `k` and every universe `u`. They concern an actual connected reductive group scheme `G`, an actual maximal split torus `i : T → G`, a generic cocharacter `ν`, and a subset `J` of the actual `simpleRelativeRoots i ν`. This file supplies statement declarations, with no proofs of the structural assertions.

`StandardRootAnnihilatorRankStatement` says that `J` is finite, that the published real cocharacter space `RealTorusSpace.V T` and its submodule `rootAnnihilator T J` are finite dimensional, and that the dimension of `V T` equals `splitTorusRank T`. It asserts the formula

`finrank ℝ (rootAnnihilator T J) + Nat.card J = splitTorusRank T`.

Here `rootAnnihilator T J` is the simultaneous kernel of the actual evaluations of the characters in `J`. Its codimension is therefore the number of selected simple roots. The ambient space is the full cocharacter space, retaining the central directions. When `J` is empty the annihilator is the entire space; when `J` is the full set of simple roots its dimension is the split-center rank.

`StandardLeviSplitCentralDirectionsStatement` uses the existing choice-free `standardLevi i ν J` subgroup functor. For every actual closed subgroup morphism `j : L → G` representing this functor, it concludes that `L` is connected reductive. `IsRepresentedBy` means monomorphism and equality of the image subgroup functor on every test scheme. Closedness is a separate premise identifying the supplied representative. The target neither constructs a replacement Levi functor nor substitutes a subgroup of rational points.

For every actual split component `a : A → L`, the second target concludes that `V A` is finite dimensional and supplies an actual morphism `f : A → T` of commutative group schemes with `groupHom f ≫ i = a ≫ j`. The underlying group-scheme map of `f` is closed. Its induced real cocharacter map is injective and has image exactly `rootAnnihilator T J`. The target further identifies the dimension of this annihilator with `splitTorusRank A` and states

`splitTorusRank T = Nat.card J + splitTorusRank A`,

as well as `rationalCharacterRank L = splitTorusRank A`. These compare the actual torus and rational-character lattices, rather than arbitrary vector spaces with the same dimension.

The intrinsic structural premises are connected reductivity, maximal splitness, genericity and the simple-root subset condition. The affine instance needed by the actual root definitions is extracted from reductivity. A supplied closed representative and a supplied split component identify the geometric objects to which the conclusions apply. There is no root-system realization, basis, reflection, Coxeter system, rank formula or existence of a standard cocharacter among the premises. The existing standard-cocharacter, dynamic representability and split-component existence targets retain their owners; their proofs may be used to prove this target. Nonreduced relative roots and rank zero are retained, with no nonemptiness assumption.

The provenance is derived. Borel–Tits, *Groupes réductifs* (1965), §5.12 (printed p.99, PDF p.46), defines the standard Levi using the torus cut out by the selected simple roots and transfers the structural description of §§4.2(i)–(ii) to the relative setting. The common-root-kernel comparison in Theorem 5.3 (printed pp.96–97, PDF pp.43–44), together with the maximal-split and product-rank comparisons in §§4.23 and 4.27 (printed pp.93–94, PDF pp.40–41), gives the algebraic split-center interpretation.

Renard, French version dated 9 July 2026, V.3.12–13 (printed pp.112–113, PDF pp.118–119), gives the simple-root basis and describes the embedded split-component space of a standard Levi as the annihilator of its selected simple roots. The codimension and displayed rank identities are finite-dimensional linear-algebra consequences of that description and independence of the selected roots. The rational-character comparison uses restriction to a split component as in V.2.5–6 (printed pp.107–108, PDF pp.113–114).

Renard works over a nonarchimedean local field. The arbitrary-field statement here is an algebraic extension derived from Borel–Tits and the actual finite split-torus lattices. Passing to real cocharacters removes finite-index lattice discrepancies; it does not assert equality of integral lattices. No topology or valuation enters these targets. The retained 2010 errata, PDF pp.8–9, correct the earlier-edition restriction and dual-space notation, and the cited 2026 version incorporates those corrections.
