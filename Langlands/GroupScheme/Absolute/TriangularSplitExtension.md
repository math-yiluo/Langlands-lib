# Group sections of solvable extensions of split tori

This module proves a conditional form of Milne 2017, Theorem 16.26(a), for
smooth connected solvable groups. It also builds the group section behind it.
Let `k` be algebraically closed, and let `H` be a group over `k` with a closed
upper triangular embedding. Suppose `q : H → D` is a quotient by a unipotent
normal subgroup `U`, with `D` a split torus, and suppose `q` has a section as
a morphism of schemes. Then `q` has a homomorphic section. The final theorem
`solvableSplitExtension_of_perfectFieldUnipotentSplit` supplies the
triangular embedding and the scheme section for the published
`SolvableSplitExtensionStatement`. It assumes the published but unproved
`PerfectFieldUnipotentSplitStatement`.

## Upper triangular group scheme

In the namespace `Langlands.GroupScheme.TriangularLayer`:

- `upperScheme k N` is the published block parabolic subgroup scheme
  `GeneralLinear.blockParabolicScheme (Fin N) k (fun i => -i)` of `GL_N`.
  These are the upper triangular matrices. This is the target of the
  published `SolvableTriangularEmbeddingStatement`.
- `upperMatrix A : Lie.AffinePoints (upperScheme k N) A →* GL_N(A)` takes
  the matrix of an affine point, through the published
  `GeneralLinear.affinePointsEquiv`. It is natural (`upperMatrix_naturality`)
  and lands in `upper A N` (`upperMatrix_mem_upper`, via
  `Corepresented.groupSchemeMap_affinePoints`). `upperMatrix_eq_map`
  compares it with the matrix of the point over the global sections.
- `mem_W_of_diagPart_eq_one`: a triangular matrix with trivial diagonal part
  is unitriangular. `upperMatrix_mem_W`: a point whose image under the
  published diagonal-limit map `GeneralLinear.blockLimitHom` is trivial has a
  unitriangular matrix (by `GeneralLinear.pointsEquiv_blockLimitHom`).
- `isSplitTorus_blockLeviScheme`: the diagonal subgroup scheme for the
  distinct weights `i ↦ -i` is a split torus, by the published
  `GeneralLinear.diagonalTorusIso`.

## The triangular lift

Fix a finite type `I` and write `𝔻 = splitTorus (Spec k) I`. The data are:

- homomorphisms `i : U → H`, `q : H → 𝔻`, `j : H → upperScheme k N`;
- a morphism of schemes `s : 𝔻.X → H.X`;
- `hU : IsUnipotent U` and `hn`: the range of `i` is normal;
- `hker`: on every test scheme a point of `H` is in the range of `i` exactly
  when its composite with `q` is `1`;
- `hs : s ≫ q = 𝟙`.

The section declarations below also assume `Mono j.hom.hom`.

- `matrixOf j A h` is the matrix of `h ≫ j`. It is multiplicative and natural
  (`matrixOf_naturality`). It is injective when `j` is a monomorphism
  (`matrixOf_injective`).
- `torusPoint I A t` is the affine point of `𝔻` with unit coordinates `t`, by
  the published `splitTorus.algebraPointsEquiv`.
- `torusLift I i q j s hU hn hker hs : TorusLift k I N` is the structure of
  `Absolute/TriangularTorusLift` with `lift A t = matrixOf j A (torusPoint t ≫ s)`.
  `kernel A` is the image under `matrixOf j A` of the points of the range of
  `i` over `Spec A`. The axioms are checked as follows.
  - Naturality comes from `torusPoint_naturality` and `matrixOf_naturality`.
  - Unitriangularity of the kernel (`kernel_le`): `U → H → upperScheme →
    blockLeviScheme` is trivial, by the published
    `IsUnipotent.comp_eq_one_of_isSplitTorus` and
    `isSplitTorus_blockLeviScheme`.
  - Multiplicativity modulo the kernel: `hker`, `hs`, and multiplicativity of
    `torusPoint`.
  - Normalization: the normality hypothesis `hn`.

## The section

Assume also that `k` is algebraically closed.

- `corrector` is a unitriangular `x ∈ GL_N(k)` given by
  `TorusLift.exists_deviation_mem` for the lift above.
  `deviation_corrector_mem` records its property.
- `deviationPoint τ` is a point of the range of `i` over `Spec A`. Its matrix
  is the deviation of the corrector at the coordinates of `τ`
  (`deviationPoint_mem`, `matrixOf_deviationPoint`).
- `sectionPoint τ = (τ ≫ s) · (deviationPoint τ)⁻¹`. Its matrix is the
  corrected diagonal part `correction x t`, which is a homomorphism in `t`
  (`matrixOf_sectionPoint`). It still maps to `τ` under `q`, because the
  deviation point lies in the kernel (`sectionPoint_comp`). Injectivity of
  `matrixOf` turns multiplicativity and naturality of the correction into
  `sectionPoint_mul` and `sectionPoint_naturality`.
- `sectionHom : 𝔻.X ⟶ H.X` is the morphism with these values on affine
  points. It uses the published `PointedCoordinateWeights.homOfAffinePoints`;
  `𝔻` is affine over `k`. `comp_sectionHom` evaluates it. `sectionHom_mul`
  proves multiplicativity on all points via the universal pair, and
  `sectionHom_comp` proves `sectionHom ≫ q = 𝟙`.
- **`splitSection I i q j s hU hn hker hs : 𝔻 ⟶ H`** is the homomorphism of
  group schemes with underlying morphism `sectionHom`, made by the published
  `homOfPoints`. `splitSection_comp` proves `splitSection … ≫ q = 𝟙 𝔻`.

## Main theorems

In the namespace `Langlands.GroupScheme`:

- `IsSplitTorus.exists_section_of_triangular`: for `k` algebraically closed,
  group schemes `H, U, D`, `i : U → H`, `q : H → D`,
  `j : H → upperScheme k N` with `Mono j.hom.hom`, `IsSplitTorus D`, `U`
  unipotent with normal range, `hker` as above, and a scheme section `s` of
  `q`, there is `σ : D ⟶ H` with `σ ≫ q = 𝟙 D`. The proof transports along
  an isomorphism `f : D ≅ 𝔻` and uses `splitSection` for `q ≫ f.hom` and
  `f.inv ≫ s`.
- `solvableSplitExtension_of_perfectFieldUnipotentSplit :
  PerfectFieldUnipotentSplitStatement.{u} → SolvableSplitExtensionStatement.{u}`.
  Given the data of `SolvableSplitExtensionStatement`, the proof runs as
  follows.
  1. The published `solvableTriangularEmbeddingStatement` (Lie–Kolchin) gives
     a closed subgroup `j : H → upperScheme k N`. Its underlying morphism is
     a monomorphism.
  2. `U` and `D` are affine, by `HomogeneousQuotient.affine_subgroup_of_closed`
     and `IsSplitTorus.isAffineHom`.
  3. The premise, applied to `U` over the perfect field `k`, makes `U` split
     unipotent.
  4. The published `HomogeneousQuotient.fppf_section_of_split_unipotent_torsors`,
     with the published `splitUnipotentAffineTorsorStatement`, gives a
     scheme section `s` of the fppf quotient `q`.
  5. `hker` comes from the quotient hypothesis: the kernel of `q` is the range
     of `i`, by `mem_range_kernelι_iff`.
  6. `IsSplitTorus.exists_section_of_triangular` concludes.

## Scope

The theorem is conditional. `PerfectFieldUnipotentSplitStatement` is an
explicit premise, used only to obtain the scheme section of `q`. The
group-theoretic splitting itself, `splitSection` and
`IsSplitTorus.exists_section_of_triangular`, has no such premise. It needs
the triangular embedding, the unipotent normal kernel, the split torus
quotient and a scheme section. No conjugacy theorem (Milne 16.27) and no
structure theorem 16.33 enters the proof.

## Provenance

The statement proved is Milne 2017, Theorem 16.26(a) (printed pp. 332-333,
zero-based PDF pages 347-348), for smooth connected solvable `H`, unipotent
part `U` and split torus `D`, in the form of the published
`SolvableSplitExtensionStatement`. The route differs from Milne's. Milne
splits along a `D`-stable normal series of `G_u` with quotients embedded in
`G_a`, using Theorem 15.34(d) at each step. Here a triangular embedding is
used instead, with induction along the superdiagonal filtration of the
unitriangular group (`Absolute/TriangularTorusLift`), and each step is
averaged over the torus (`Torus/LaurentRootAverage`). `splitSection` and the
other definitions are internal constructions for this route.
