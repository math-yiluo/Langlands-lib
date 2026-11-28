# The kernel of a quaternionic spin cover is `μ₂`

Module `Langlands.GroupScheme.Rational.QuaternionicSpinKernelMu`, namespace
`Langlands.GroupScheme`.

The module proves `QuaternionicSpinKernelMuStatement` (module
`Rational/NumberFieldQuaternionicSpinKernelReduction`) at every universe, as the theorem
`quaternionicSpinKernelMu`. It also defines one auxiliary isomorphism.

## The statement proved

Let `F` be a field of characteristic zero, `D` a central division `F`-algebra with
`dim_F D = 4`, `σ` a first-kind involution of `D` with three-dimensional symmetric subspace,
`n ≥ 3` and `q : σ.QuadraticForms (Fin n)` nondegenerate. Let `G` be a simply connected group
scheme over `Spec F` and `p : G ⟶ σ.normOneIsometryGroup q` a central isogeny onto the
reduced-norm-one isometry group. Then the full scheme-theoretic kernel `kernel p` is
isomorphic, as a group scheme over `Spec F`, to `μ₂ = (mu (Spec F) 2).toGrp`.

Classically, `σ.normOneIsometryGroup q` is an `F`-form of the split group `SO_{2n}`, of
absolute type `D_n` (it need not be an inner form: its discriminant can be nontrivial). Over a
separable closure it becomes `SO_{2n}`, a simply connected central cover becomes the spin
group, and the kernel of `Spin_{2n} → SO_{2n}` is `μ₂`. The proof uses exactly this geometric
splitting and needs no condition on the discriminant.

## The auxiliary isomorphism

`HomScheme.FiniteDiagonalizable.muPowerPUnitIso R m` is the isomorphism
`muPower R PUnit m ≅ μ_m` over `Spec R`, for any commutative ring `R`, from the one-factor
power of `μ_m` (module `HomScheme/FiniteDiagonalizableHom`) to `μ_m` itself. It is built with
`isoOfPointModels` from the point descriptions of both sides as `m`-th roots of unity in
`Γ(T, ⊤)`: `muPowerPointsEquiv` followed by evaluation at the unique index on one side, and
`mu.pointsEquiv` on the other. Both are natural in the test scheme
(`muPowerPointsEquiv_naturality`, `mu.pointsEquiv_naturality`).

## The proof of `quaternionicSpinKernelMu`

Write `Ω = SeparableClosure F`. In characteristic zero `Ω` is perfect and separably closed,
hence algebraically closed (Mathlib's instance `IsSepClosed.isAlgClosed_of_perfectField`).

**Splitting.** `CentralSimple.exists_matrix_chart_reducedDegree` gives a chart
`Ω ⊗ D ≃ M_r(Ω)` with `r` the reduced degree, and `FirstKindInvolution.reducedDegree_eq_two`
reindexes it to `e : Ω ⊗ D ≃ M₂(Ω)`. Let `Q = NormOneSplit.gramQ e σ q`, the scalar quadratic
form on `Ω^{2n}` of the split Gram matrix; it is nondegenerate by
`MoritaIsometry.isNondegenerateQuadratic_gramN`. `NormOneSplit.splitIso` identifies the base
change of `σ.normOneIsometryGroup q` to `Ω` with `(scalar Ω).normOneIsometryGroup Q`. Composing
the base change of `p` with this isomorphism gives a central isogeny
`r : G_Ω ⟶ (scalar Ω).normOneIsometryGroup Q` (`IsCentralIsogeny.baseChange`,
`IsCentralIsogeny.comp_iso`), and `G_Ω` is simply connected by
`isSimplyConnectedFieldExtension`.

**The split kernel.** By `ordinaryOrthogonalGeometry` (with `n ≥ 3`) the scalar isometry group
of `Q` is smooth and its identity component is absolutely almost simple, hence semisimple, so
`scalarConnectedIsometryIso_normOne` identifies the identity component with the norm-one
group, and the norm-one group is semisimple. Composing `r` with the inverse of that
identification gives the cover of the identity component to which
`natCard_scalarEvenSpinKernel` applies. It counts two kernel points over the algebraic closure
of `Ω`, and `kernelSquareIso` transports this count to the kernel of `r`.
`CliffordSpin.exists_iso_of_simplyConnected_scalarCover` then gives an isomorphism `c` from
`G_Ω` to the Clifford lift group of `Q` with `c ≫ projection Q = r`. Hence `kernel r` is
isomorphic to the kernel of the Clifford projection, which is `μ₂` over `Ω` by
`CliffordSpin.kernelIso`. Together with `kernelBaseChangeIso` (base change of a kernel is the
kernel of the base change) and `kernelSquareIso` for the splitting isomorphism, this gives
an isomorphism of `(kernel p)_Ω` with `μ₂` over `Ω`, and then, through `muPowerPUnitIso` and
`HomScheme.FiniteDiagonalizable.diagonalizableIso`, with the diagonalizable group
`Diagonalizable.groupScheme Ω Λ` of `Λ = PUnit → ZMod 2`.

**Descent.** The kernel inclusion of `p` is central, so `IsCentral.commGroupScheme` makes
`kernel p` a commutative group scheme `Z` over `Spec F`, with the same underlying group
scheme. The isomorphism above shows that `Z` is of multiplicative type
(`IsMultiplicativeType`, split over `Ω` with character group `Λ`). Its absolute character
lattice, the characters of `Z_Ω`, is identified with `Λ` by
`DiagonalizableCharacter.evalCharacterEquiv` and `characterLattice.congr`, so it has two
elements. The Galois action of `Aut(Ω/F)` on a two-element group is trivial: each
automorphism fixes `0`, is invertible, and therefore fixes the unique nonzero element.
`characterLattice.isoOfConstantAbsoluteEquiv` then identifies `Z` with the diagonalizable
group `Diagonalizable.groupScheme F Λ` over `F`. Finally
`MultiplicativeTypeGaloisExactness.grpIso`, `diagonalizableIso F PUnit 2` and
`muPowerPUnitIso F 2` give the required isomorphism `kernel p ≅ μ₂` of group schemes over
`Spec F`.

## Provenance

The result is the statement that the spin group of a nondegenerate quadratic form of
dimension at least five is a double cover of the special orthogonal group with kernel `μ₂`,
here for the quaternionic forms of type `D_n` with `n ≥ 3` (Kneser, *Lectures on Galois
Cohomology of Classical Groups*, 1969, §5.11, exact sequence (4), printed p. 101). The proof
is derived from the Library results named above: the Morita splitting of the quaternionic
norm-one group, the degree of the scalar even spin cover, the Clifford comparison of simply
connected scalar covers, and the anti-equivalence between groups of multiplicative type and
their Galois character modules.
