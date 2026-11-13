# Reductive Kottwitz homomorphisms

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), §11.5 and Lemma 11.5.1, printed pp. 429–430 (PDF pp. 460–461), using the z-extensions of §11.4, printed pp. 428–429. The November 2024 corrections do not change these passages.

Let `F` be any nonarchimedean local field, `K = UnramifiedClosure F` and `E = SeparableClosure F`. The field `k` records a field of definition for the original group scheme; it may be `F` or `K`. `reductiveKPoints F k G` means the actual points of this original group scheme with coefficients in `K`. `ReductiveTarget F k G hG` is the integral inertia quotient of its actual algebraic fundamental group. The cocharacter quotient, its Galois action, and the induced maps are those of the companion fundamental-group modules.

`Cocenter k G` packages an actual commutative group scheme `D`, its torus property, a morphism `q : G → D`, and the full fppf quotient property for the scheme-theoretic derived subgroup. It does not supply a homomorphism on points or a Kottwitz map. `nonempty_cocenter` is proved from the Library's cocenter quotient existence theorem and the chosen simply connected derived cover. `cocenterTargetMap` is the composition of the actual induced fundamental-group inertia map and the representative-characterized torus comparison.

For a group with simply connected derived subgroup, `CocenterKottwitzLawAt c κ` is the commuting square

`cocenterTargetMap c (κ(x)) = κ_D(q(x))`.

Here `κ_D` is the norm-and-normalized-valuation torus map. `IsSimplyConnectedDerivedKottwitzHom` requires this equation for every actual cocenter. `simplyConnectedDerivedKottwitz` selects a homomorphism with that property by classical epsilon. The hypothesis that the derived subgroup is simply connected is the intended domain of this construction. Existence, uniqueness, surjectivity and independence of the cocenter are unconditional targets in the paired statement module.

For an actual z-extension `z : 1 → Z → H → G → 1`, `ZExtensionKottwitzLawAt z κ` is the equation

`κ(p(x)) = π₁(p)_I(κ_H(x))`,

where `κ_H` is the preceding simply-connected-derived construction. `IsReductiveKottwitzHom` requires that z-extensions exist and that this equation hold for every one of them. Thus its universal square condition cannot hold vacuously because there are no z-extensions. `reductiveKottwitz` selects this homomorphism by classical epsilon; no map, kernel assertion or surjectivity witness is supplied as input. Its unconditional existence, uniqueness, independence, functoriality and surjectivity obligations are in `ReductiveMapStatement`. These obligations remain to be proved and are not asserted as theorems here.

For a group over `F`, `ReductiveInvariantTarget` is `A^Γ`, with `A = π₁(G)_I` and the actual residual action of `Γ = Gal(K/F)`. `ReductiveKottwitzEquivariant` states residual equivariance. `IsReductiveKottwitzRestriction` characterizes an invariant-valued homomorphism on the Library's actual rational points by its composite with `A^Γ → A`, using the actual coefficient-extension map to `K`-points. `reductiveKottwitzRational` is selected by this property. The companion descent target asserts the unique existence and correctness of this restriction. Rational surjectivity is the later Corollary 11.7.5 target, not a consequence claimed by this definition file.
