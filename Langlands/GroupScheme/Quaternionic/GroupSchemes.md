# Symplectic, orthogonal and spin groups of quaternionic forms

Authors: Worker 5197.

Module `Langlands.GroupScheme.Quaternionic.GroupSchemes`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`. It defines the groups of family
(iii) of Prasad–Raghunathan (1985), §2, as group schemes over `Spec K`. It proves only the
structural facts listed below; no smoothness, connectedness, reductivity or simple
connectedness is asserted.

## Setting

`K D : Type u`, with `[Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]`.
`σ : FirstKindInvolution K D`, and `n : Type` is a finite index type with decidable equality.
Forms on `D^m` use `n = Fin m`. Gram matrices, antihermitian forms and quadratic forms follow
the conventions of `Langlands.GroupScheme.Quaternionic.Forms` (row vectors; the same Gram
matrix as the sources' column convention). For a commutative `K`-algebra `R`, `ᵗu^σ` denotes
`(σ.matrix n).baseChange R u` for `u ∈ R ⊗[K] M_n(D)`.

## Unitary and symplectic groups

- `σ.unitaryGroup H` is the unitary group `U(h)` of the form with Gram matrix
  `H ∈ M_n(D)`. It is the isometry group scheme of
  `Langlands.GroupScheme.Quaternionic.IsometryCut` for `τ = σ.matrix n`, `M = ⊥` and `Q = H`:
  an actual affine group scheme `Spec (B ⧸ I)`.
- `σ.unitaryGroupι H` is its inclusion into the unit group scheme
  `FiniteAlgebraUnits.groupScheme (Module.finBasis K (M_n(D)))` of `M_n(D)`. It is a closed
  subgroup (`isClosedSubgroup_unitaryGroupι`).
- `mem_range_unitaryGroupι_iff`: on every test scheme `T` over `Spec K`, with `R = Γ(T)`, a
  point `u ∈ (R ⊗[K] M_n(D))ˣ` of the unit group lies in `U(h)` exactly when
  `u (1 ⊗ H) ᵗu^σ = 1 ⊗ H`. This is the isometry condition `h(x u, y u) = h(x, y)` for the
  row action, over every coefficient algebra.
- `σ.symplecticGroup H`, for `[Algebra.IsCentral K D] [Nonempty n]`, is the group of
  *special* isometries. It is the Library group-scheme kernel `kernel` of
  `σ.unitaryGroupι H ≫ CentralSimpleUnits.reducedNormHom K (M_n(D))`, the reduced norm of
  the central simple algebra `M_n(D)` restricted to `U(h)`. The instances make `M_n(D)`
  central simple, as `reducedNormHom` requires. `σ.symplecticGroupι H` is the kernel
  inclusion into `U(h)`.

Sources. Prasad–Raghunathan, §2 (iii), printed p. 111 / PDF p. 6, call this group "the
symplectic group of a σ-antihermitian form". Tits 1966, Table II, type `C_n`, printed p. 56 /
PDF p. 61, describes it as the "Special unitary group SU_{2n/d}(D, h)" of a nondegenerate
antihermitian form relative to `σ` with `dim D^σ = ½d(d + 1)`. That is the reduced-norm-one
subgroup of the unitary group, which is what `symplecticGroup` formalizes. For these forms the
unitary group is already connected of type `C`, so the reduced-norm condition does not shrink
it. This fact is neither used nor proved here; the definition keeps the literal "special"
condition.

## Orthogonal groups

- `σ.isometryGroup q`, for a `σ`-quadratic form `q : σ.QuadraticForms n`, is the isometry
  group `O(q)`. It is the isometry group scheme of `IsometryCut` for `τ = σ.matrix n`,
  `M = σ.quadraticKernel n = {x - ᵗx^σ}` and the representative `Q = Quotient.out q`.
- `σ.isometryGroupι q` is its inclusion into the unit group scheme of `M_n(D)`, a closed
  subgroup (`isClosedSubgroup_isometryGroupι`).
- `mem_range_isometryGroupι_iff`: for every representative `Q` of `q` and every test scheme
  `T` with `R = Γ(T)`, a point `u` of the unit group lies in `O(q)` exactly when
  `u (1 ⊗ Q) ᵗu^σ - 1 ⊗ Q ∈ R ⊗ {x - ᵗx^σ}`. So `O(q)` does not depend on the chosen
  representative. The condition says that `u` preserves `q` over `R`: the value
  `x ↦ x Q ᵗx^σ` modulo `{a - σ a}` is unchanged under `x ↦ x u`. For `D = K` and `σ = id` it
  is the usual orthogonal group scheme of a quadratic form, in every characteristic.
- The instance `isAffineHom_isometryGroup` records that `O(q)` is affine over `Spec K`.
- `σ.connectedIsometryGroup q`, under the instance `[Smooth (σ.isometryGroup q).X.hom]`, is
  the Library's actual identity component `identityComponent (σ.isometryGroup q)` (module
  `Langlands.GroupScheme.IdentityComponent`, which constructs `H⁰` for smooth affine `H`).
  This is the connected isometry group `O(q)⁰`; when `2` is invertible it is the special
  orthogonal group. The smoothness hypothesis is required by the Library's identity-component
  construction. Smoothness of `O(q)` for nondegenerate `q` is a known fact (`O(q)` is a form of
  the orthogonal group of a nondegenerate quadratic form of dimension `2m`). It is not proved
  here; the statements assert it through `IsSpinCover`, see below.

Sources. Tits 1977, 1.1.6, printed p. 220 / PDF p. 4, attaches to every nondegenerate
quadratic form `q` the group `Spin q`, "une forme de D_n avec n = ½md". Tits 1966, Table II,
type `¹D_n`, printed p. 57 / PDF p. 62, describes the corresponding (special) orthogonal
groups: unitary groups of hermitian forms relative to `σ` with `dim D^σ = ½d(d + 1)` in
characteristic not 2, and "special orthogonal groups" of nondegenerate nondefective quadratic
forms in characteristic 2.

## Spin groups

`σ.IsSpinCover q π`, for a group scheme `S` over `Spec K` and `π : S ⟶ σ.isometryGroup q`, is a
structure with three fields:

- `isSimplyConnected : IsSimplyConnected S` (the Library's algebraic simple connectedness,
  which includes semisimplicity, hence smoothness, connectedness and affineness);
- `smooth : Smooth (σ.isometryGroup q).X.hom`;
- `exists_centralIsogeny`: with that smoothness, there is `p : S ⟶ σ.connectedIsometryGroup q`
  with `IsCentralIsogeny p` and `p ≫ identityComponentι (σ.isometryGroup q) = π`.

So `S` is a spin group of `q` exactly when it is simply connected and `π` is a central isogeny
onto the connected isometry group `O(q)⁰`, followed by the inclusion `O(q)⁰ ⊆ O(q)`. The task
allows a spin group to be "given by an explicit construction or characterized by such a
central isogeny". We characterize it, for the following reasons.

- Tits 1977, printed p. 218 / PDF p. 2, defines a universal cover of a group `G` as
  `p : G̃ → G` with "G̃ simplement connexe et p une isogénie centrale". The spin group `Spin q`
  of 1.1.6 is the universal cover of `O(q)⁰` in this sense. The classical Clifford-algebra spin
  group of Tits's 1968 paper is simply connected and maps onto `O(q)⁰` by a central isogeny,
  so it satisfies `IsSpinCover`. That paper is not available here, and no Clifford algebra is
  formalized.
- The Library has no Clifford algebras of quadratic forms over division algebras with
  involution. A characterization uses only `IsSimplyConnected` and `IsCentralIsogeny`.
- When `O(q)⁰` is semisimple, two spin groups of `q` are isomorphic over `O(q)⁰`, by the
  universal property of simply connected central covers (compare the Library's
  `IsSimplyConnectedCover` and `IsSimplyConnectedCover.iso`). This module proves neither
  existence nor uniqueness. The rank-one statement asserts existence.

The smoothness of `O(q)` is a field of `IsSpinCover` rather than a hypothesis of the
statements. Any statement asserting that a spin group exists therefore asserts that `O(q)` is
smooth.
