# Contracting rational points and simply connected derived covers

This internal result concerns an arbitrary field `k : Type u`, a supplied actual
derived subgroup `d : D → G` of a connected reductive group, and a supplied
simply connected cover `π : C → D`. It derives rational lifting for contracting
subgroups from the Library's actual integral Weyl actions, central shifts,
positive powers, and central-isogeny rational lifting.

For an integral cocharacter `ν` of a torus `i : T → G` with finite actual
relative Weyl group `W = N_G(T)(k)/Z_G(T)(k)`, the existing
`normKernelCocharacter i ν` is

`η = |W| ν − ∑ w∈W wν = ∑ w∈W (ν − wν)`.

Each difference is the negative of an actual normalizer commutator
cocharacter. `normKernelCocharacter_mem_cocharactersLandingIn_derived`
therefore proves that `η` lands in the scheme-theoretic derived subgroup on
every test scheme. This step does not require reductivity, splitting of the
torus, or a relative-root-system realization.
`derivedNormKernelCocharacter` factors it through the supplied actual
derived inclusion, and `derivedNormKernelCocharacter_comp` retains the
exact ambient composite.

If the Weyl sum belongs to `centralCocharacters i`, subtracting it does not
change any conjugation orbit. The positive integer `|W|` also preserves
the entire dynamic identity-limit subgroup. Thus
`Dynamic.unipotent_normKernelCocharacter` gives the equality of subgroup
functors `U_G(η) = U_G(ν)` on every test scheme.

Every contracting point already belongs to the actual derived subgroup by
`Dynamic.unipotent_le_derivedSubgroup`. Transport the point through the
represented derived inclusion, and use the closed-subgroup comparison to
see it contracts inside `D` under the factored cocharacter. The existing
`Dynamic.exists_lift_of_mem_unipotent` then lifts it through the actual
central isogeny `π`. The affineness of the semisimple groups `C` and `D`
supplies the required separatedness. The resulting point `c : C(k)` has
the exact composite `rationalPoints.map (π ≫ d) c = g`.

The main specialization,
`Dynamic.exists_derivedCover_lift_of_mem_unipotent_of_relativeRootSystem`,
assumes the actual realization `HasRelativeRootSystem i` and a split torus.
The realization gives a finite actual Weyl group and actual root
reflections. The existing Weyl-average centrality theorem, with the smooth
connected affine hypotheses from `IsSimplyConnectedDerivedCover d π`,
then supplies the centrality used above.
`Dynamic.unipotentPoints_le_derivedCoverImage_of_relativeRootSystem`
packages the same result as an inclusion of actual rational-point subgroups.

The construction works in arbitrary characteristic and at arbitrary universe
`u`; it uses no topology, valuation, root-group product decomposition, or
surjectivity of `C(k) → D(k)`. The relative-root-system realization remains
an explicit premise. This unit is a prerequisite reduction for the minimal
Levi product in Kaletha–Prasad, Fact 2.6.22, rather than a proof of that full
product statement. Its proof route is derived internally from the cited
Library declarations, using integral Weyl averaging in place of individual
root-group lifting.
