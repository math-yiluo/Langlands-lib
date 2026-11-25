# Assembly of the cocenter construction of the Kottwitz homomorphism

The theorem
`Langlands.Geometry.Building.Kottwitz.simplyConnectedDerivedKottwitz_proof`
proves exactly the existing proposition
`Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzStatement`.
It has no additional premises. For every nonarchimedean local field `F`,
write `K = UnramifiedClosure F` and `E = SeparableClosure F`. The statement
allows every compatible coefficient tower `k → K → E` with `E` a separable
closure of `k` and `Normal k K`, and every connected reductive `k`-group
whose derived group is simply connected.

The conclusion gives unique existence of a homomorphism satisfying all actual
cocenter squares, the specification and `K`-point surjectivity of the selected
`simplyConnectedDerivedKottwitz` homomorphism, and, for every actual cocenter,
bijectivity of its target map and characterization of the selected
homomorphism by that single square. The targets are the full integral
inertia coinvariants, including their torsion.

The implemented proof applies
`simplyConnectedDerivedKottwitz_of_norm_inputs` and supplies each of its six
premises with an existing Library theorem, in order:

- `algebraicFundamentalGroupComparison`;
- `algebraicFundamentalGroupMap`;
- `torusFundamentalComparison_proof`;
- `fundamentalInertiaMapStatement`;
- `torusInertiaComparison_proof`;
- `torusKottwitzExistence`.

All six theorem modules are imported explicitly. The imported reduction
derives torus naturality from the norm characterization. Its cocenter
construction chooses an actual cocenter, proves its integral target map
bijective using cocharacters and inertia coinvariants, and composes the
inverse target map with the cocenter quotient on points and the torus
Kottwitz homomorphism. Naturality transports the resulting square to every
actual cocenter. Injectivity of each target map proves uniqueness from each
individual square, and existence justifies the selected homomorphism's
specification. Surjectivity follows by lifting through the inertia map of a
maximal torus and then through its torus Kottwitz homomorphism. This is the
route implemented by the imported reductions.

The contextual source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), section 11.5 before Lemma 11.5.1, printed pp. 429–430 / PDF pp. 460–461.
The torus norm characterization is Proposition 11.1.1, printed pp. 421–422 /
PDF pp. 452–453. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
have Chapter 11 changes at PDF pp. 43–45 concerning section 11.7 and do not
change the cited passages. This module assembles the existing Library proof
route; it introduces no new geometric construction.
