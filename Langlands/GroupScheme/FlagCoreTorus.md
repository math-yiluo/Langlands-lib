# Maximal tori on rational points: diagonalization and torus-fixed lines

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. The core's linear
algebra (`Langlands.GroupScheme.FlagCoreLinear`) works with an abstract group `Γ` (here the
rational points of `G`) and a torus given by a parametrization `τ : (I → kˣ) → Γ`. It needs
two hypotheses about this torus. First, `ρ(τ s)` is `P · diag(charValue wt s) · P⁻¹` for a
fixed change of basis `P` and integral weights `wt`. Second, a line through an orbit vector
that is fixed by the torus is stable under the group `U`. This module proves both
statements for an actual maximal torus of `G` over an algebraically closed field.

Notation. `pt` is the base test `Over.mk (𝟙 (Spec k))`; a morphism `pt ⟶ G.X` is a
rational point of `G`. For a matrix representation `ρ`, `ρ.rationalMatrix` is the
homomorphism from rational points to `GL m k` (from
`Langlands.GroupScheme.MatrixRepresentationRationalPoints`). `e_j` is the coordinate vector
`Pi.single j 1`. `orbitVec ρ' e g = ρ'(g) e` and
`charValue wt s i = ∏ a, s a ^ wt i a` are from `FlagCoreLinear`. Also from
`FlagCoreLinear`, `IsTorusFixed ρ' τ u` says that every `ρ'(τ s)` maps `u` to a scalar
multiple of `u`.

All declarations are in the namespace `Langlands.GroupScheme.FlagCore`.

## The base test as an affine test

Here `R` is a commutative ring and `G` a group scheme over `Spec R`.

- `baseAffineTestIso` (definition): the isomorphism
  `Over.mk (𝟙 (Spec R)) ≅ (algSpec R).obj (op (CommAlgCat.of R R))` in
  `Over (Spec R)`. It is `Gm.affineTestIso` applied to the equality
  `𝟙 (Spec R) = Spec.map (𝟙 R)`, so both components are identities.
- `rationalMatrix_baseAffineTestIso ρ x`: for a point `x` of `G` on the affine test of the
  `R`-algebra `R`, the rational matrix of `baseAffineTestIso.hom ≫ x` is the affine matrix
  `ρ.affineMatrix (CommAlgCat.of R R) x`. Proof: compare entries, using
  `pointMatrix_naturality`, `pointMatrix_eq_affineMatrix` and
  `Corepresented.affineSectionsIso_inv_ringHom`. The identity of `Spec R` acts trivially on
  global sections (`Scheme.Hom.id_appTop`), and the inverse and forward maps of
  `Scheme.ΓSpecIso R` cancel.

## Diagonalization of a maximal torus

- `exists_torusDiagonal hsplit ht ρ`: let `k` be algebraically closed. Let `t : T ⟶ G` be a
  maximal torus (`IsMaximalTorus t`) of a group scheme `G` over `Spec k`, and let
  `ρ : MatrixRepresentation G n`. Assume `hsplit : TorusFiniteGaloisSplittingStatement`,
  taken as a hypothesis and not proved here. Then there are:
  - a finite type `I : Type u`;
  - `P : GL n k` and weights `wt : n → I → ℤ`;
  - `τ : (I → kˣ) → (pt ⟶ G.X)`;

  such that `ρ(τ s) = P · diagonal (charValue wt s) · P⁻¹` for every `s`, and the range of
  `τ` is the set of rational points `z ≫ t.hom.hom` of the image of `t`. Proof:
  - `IsTorus.isSplitTorus_of_finiteGaloisSplitting` gives a finite `I` and an isomorphism
    `e` from `T` to the split torus `splitTorus I`.
  - Restrict `ρ` along `e.inv ≫ t` to a representation `σ` of the split torus. The Library
    theorem `GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix` gives `P` and
    `wt` such that `P⁻¹ · matrixAt I σ s · P` is the diagonal matrix of
    `splitTorus.exponentValue I s (ofAdd (wt i))` for every `k`-algebra `A` and every
    `s : I → Aˣ`. Use it with `A = k`, where mapping `P` along `algebraMap k k` changes
    nothing.
  - Define `τ s` as `baseAffineTestIso.hom`, then the point
    `(splitTorus.algebraPointsEquiv I k).symm s` of the split torus, then `e.inv ≫ t`. By
    `rationalMatrix_baseAffineTestIso` and `MatrixRepresentation.affineMatrix_restrict`,
    `ρ(τ s) = matrixAt I σ s`. This gives the first claim, since
    `exponentValue s (ofAdd w) = ∏ a, s a ^ w a` is `charValue` by definition.
  - The range claim holds because `algebraPointsEquiv` is a bijection and `e` is an
    isomorphism. A rational point `z` of `T` is `τ` of
    `algebraPointsEquiv (baseAffineTestIso.inv ≫ z ≫ e.hom)`.

## Torus-fixed lines are stable under `U`

Here `k` is algebraically closed and `ρ : MatrixRepresentation G m`.

- `exists_unit_pointMatrix_iff ρ j x`: for a rational point `x` (this one does not need
  `k` algebraically closed), two conditions are equivalent. The first is that the point
  matrix `ρ.pointMatrix pt x` maps `e_j` to a unit multiple of `e_j` over `Γ(Spec k, ⊤)`.
  The second is that `ρ.rationalMatrix x` maps `e_j` to a multiple `c • e_j` with
  `c ∈ k`. Proof: the rational matrix is the point matrix with its entries mapped by
  `Scheme.ΓSpecIso`, and this map sends `e_j` to `e_j`. For the reverse direction, `c` is
  nonzero because an invertible matrix does not send `e_j` to zero
  (`FlagCore.mulVec_ne_zero`), so `c` is a unit. Its image under the inverse of
  `Scheme.ΓSpecIso` is the required unit.
- `stable_of_isTorusFixed ht hb hthrough ρ j hstab τ hτ g hg x`: the hypotheses are as
  follows.
  - `t : T ⟶ G` is a maximal torus.
  - `b : B ⟶ G` is a Borel subgroup.
  - `i : U ⟶ G` satisfies `hthrough`: for every Borel subgroup `b'` of `G` whose range
    contains the range of `t`, the range of `i` is contained in the range of `b'`.
  - `hstab`: on every test `Z`, a point `x : Z ⟶ G.X` lies in the range of `b` if and
    only if `ρ.pointMatrix Z x` maps `e_j` to a unit multiple of `e_j`. Thus `B` is the
    stabilizer of the coordinate line `j`.
  - `τ` has range equal to the rational points of the image of `t` (`hτ`). The line of
    `ρ(g) e_j`, for a rational point `g`, is torus-fixed:
    `hg : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix e_j g)`.

  Then for every rational point `x` of `U`, the matrix `ρ(x ≫ i.hom.hom)` maps
  `ρ(g) e_j` to a multiple of itself. Proof:
  1. By `hstab` and `exists_unit_pointMatrix_iff`, a rational point `y` lies in `B` if and
     only if `ρ(y) e_j ∈ k e_j`. Hence `ρ(y)` maps `ρ(g) e_j` to a multiple of itself if
     and only if `g⁻¹ y g` lies in `B`.
  2. The torus conjugated by `g⁻¹`, that is `t ≫ (G.innerIso g⁻¹).hom`, has range inside
     the range of `b`. `T` is smooth (`IsTorus.smooth`), so it is reduced
     (`SmoothReducedProof.isReduced_of_smooth_over_field`) and locally of finite type.
     Then `SubgroupFunctor.range_le_of_algClosed_points` reduces the inclusion to rational
     points. A rational point of the torus is `τ s` by `hτ`, and `hg s` together with step
     1 places `g⁻¹ (τ s) g` in `B`. The point lemmas `comp_innerIso_hom`,
     `constantPoint_inv` and `constantPoint_self` identify the conjugated point.
  3. The previous inclusion is transported to an inclusion of the range of `t` in the
     range of `b ≫ (G.innerIso g).hom`. The rewriting is the same as in
     `BruhatCovering.range_le_conj_of_range_conj_le`.
  4. `b ≫ (G.innerIso g).hom` is a Borel subgroup (`IsBorelSubgroup.comp_iso`) whose range
    contains the range of `t`. By `hthrough`, `x ≫ i.hom.hom = g (w ≫ b) g⁻¹` for a
    rational point `w` of `B`. Then `g⁻¹ (x ≫ i.hom.hom) g = w ≫ b` lies in `B`, and step
    1 concludes.

## Provenance

These are internal helper results for the proof of task 877d0194. They supply hypotheses
of `FlagCore.exists_semiInvariant_form` (in `FlagCoreLinear`), which replaces part of the
proof of Milne, *Algebraic Groups* (2017), Theorem 17.65 (printed pp. 374-375). Two steps
of that proof correspond to this module:

- Milne decomposes `V` into eigenspaces for the action of `T`. Here this is
  `exists_torusDiagonal`, obtained from the Library's simultaneous diagonalization of
  representations of split tori after splitting `T`.
- Milne shows that the stabilizer of a `T`-fixed line contains a Borel subgroup containing
  `T`, hence contains `I_u(T)`, and so fixes the line. Here this is
  `stable_of_isTorusFixed`. For the line of `ρ(g) e_j` the stabilizer contains the
  conjugate Borel subgroup `g B g⁻¹`, which contains `T`. The group `U` enters only
  through the hypothesis that it lies in every Borel subgroup containing `T`.

The formulation on rational points and the base-test comparison `baseAffineTestIso` are
internal infrastructure; they do not come from a source.
