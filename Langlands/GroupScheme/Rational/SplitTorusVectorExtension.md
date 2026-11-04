# Group sections of split-torus extensions by linear vector groups

This module proves that a Hochschild extension of a split torus by a vector
group with linear conjugation action splits. Concretely: if the quotient map
has a section as a morphism of schemes, it also has a section that is a
homomorphism of group schemes. In Milne's language (Milne 2017, Proposition
15.10 and Remark 15.17 with Proposition 15.31, the case behind Theorem
15.34(a)), every Hochschild extension of a group of multiplicative type by
`V_a` is trivial, because `H²_0(G, V_a) = 0`. The Lean proof is an internal
construction. It invokes no external vanishing theorem. Instead it averages the
Hochschild two-cocycle of the given section over the torus. The average is the
exponent-zero Laurent coefficient against the universal torus point.

## Setting and hypotheses

Let `k : Type u` be any field and let `I : Type u` be finite with decidable
equality. Write `𝔻 = splitTorus (Spec k) I`. Let `E` and `N` be group schemes
over `Spec k`, with `N` affine over `Spec k` (`IsAffineHom N.X.hom`). The data
are as follows.

- `i : N ⟶ E` is a homomorphism whose underlying morphism of schemes is a
  monomorphism (`Mono i.hom.hom`).
- `hn` says that the range of `i` is normalized by all of `E`.
- `q : E ⟶ 𝔻` is a homomorphism.
- `hker` says that on every test scheme `T`, a point `g : T ⟶ E.X` lies in the
  range of `i` exactly when `g ≫ q = 1`. So `N` is the kernel of `q` on
  points.
- `s : 𝔻.X ⟶ E.X` is a morphism of schemes with `s ≫ q = 𝟙`. This is the
  Hochschild hypothesis: the extension has a section as a morphism of schemes.
  The module does not prove that such a section exists.
- `e` gives natural vector coordinates
  `e T : (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))`, and `he`
  says that they are `RelativeRoot.IsLinearVectorCoordinates` for the
  conjugation action `splitTorus.conj i hn` of `E` on `N`. That is, they are
  natural, and conjugation by each point of `E` acts linearly over the ring of
  global functions of the test scheme. The weights are arbitrary and the
  characteristic of `k` is arbitrary.

## Main results

- `splitTorus.extensionSection I i hn q hker s hs e he : 𝔻 ⟶ E` is a
  homomorphism of group schemes, and `splitTorus.extensionSection_comp`
  proves `extensionSection … ≫ q = 𝟙 𝔻`.
- `splitTorus.exists_extensionSection` states the existence form
  `∃ φ : 𝔻 ⟶ E, φ ≫ q = 𝟙 𝔻`.
- `IsSplitTorus.exists_extensionSection` proves the same conclusion for any
  quotient `q : E ⟶ D` with `IsSplitTorus D`, under the same hypotheses with
  `D` in place of `𝔻`. The proof chooses an isomorphism `f : D ≅ 𝔻`, applies
  the split-torus result to `q ≫ f.hom` and the scheme section
  `f.inv ≫ s`, and precomposes the resulting section with `f.hom`.

## The construction

On points, the homomorphic section is
`σ(t) = i(ρ(t))⁻¹ · s(t)`. Here `ρ(t)` is the average of the section defect
`δ(t, r)` over the torus variable `r`.

1. **Affine points.** `PointedCoordinateWeights.affine_hom_ext`,
   `homOfAffinePoints` and `comp_homOfAffinePoints` are general helpers for a
   scheme `V` that is affine over `Spec k`. A morphism out of `V` is determined
   by its values on affine points. A family of maps on affine points that is
   natural in the coefficient algebra comes from the morphism
   `homOfAffinePoints`. Both use the published isomorphism `coordinateIso V`
   from the spectrum of a chosen coordinate algebra of `V`.
2. **The section defect and its cocycle law.** `sectionDefect` is
   `s(x) s(y) s(xy)⁻¹` on the universal pair of torus points, as in the proof
   of Milne's Proposition 15.10. `sectionDefect_mem` shows that it is killed
   by `q`, so it lies in the range of `i`. `kernelDefect` chooses a lift to
   `N`, and `defect t r` is that lift at a pair of points. Later proofs use
   only `kernelDefect_comp` and cancel the monomorphism `i`. `defect_comp` and `comp_defect` give the defining
   formula and naturality. `conj` is the published normalized conjugation
   action (`AutomorphicAction.ofNormalizedConjugation`), and `conj_act_comp`
   identifies it with conjugation in `E`. `defect_cocycle` is the Hochschild
   two-cocycle identity
   `δ(t, r) · δ(tr, w) = s(t)·δ(r, w) · δ(t, rw)`.
3. **Laurent averaging.** For a `k`-algebra `A`, `laurentConst` includes
   `A` into the Laurent polynomials `A[I → ℤ]` (`AddMonoidAlgebra A (I → ℤ)`).
   `laurentScalars` extends the scalars of `k[I → ℤ]`. `laurentPoint` is the
   universal torus point over `A[I → ℤ]`. `laurentTranslation r` is the
   `A`-algebra map that multiplies the monomial of exponent `m` by `r^m`.
   `coeff_laurentTranslation` and `coeff_zero_laurentTranslation` show that it
   fixes the exponent-zero coefficient. `laurentTranslation_laurentPoint`
   shows that it carries the universal point to `r ·` the universal point,
   using the published `universalPoint_translatedEvaluation`. Constant points
   are fixed (`laurentTranslation_laurentConst`).
4. **The average.** `averageVector t` is the vector of exponent-zero
   coefficients of the coordinates of `δ(t, universal point)`.
   `averagePoint t` (written `ρ(t)`) is the point of `N` with these
   coordinates. With `he`:
   - `averageVector_translate`: replacing the universal point by its
     translate by an actual point `r` does not change the average.
   - `coeff_zero_laurentConst`: constant points have their own coordinates
     as exponent-zero coefficients.
   - `coeff_zero_act`: the conjugation action by a constant point commutes
     with taking exponent-zero coefficients. It uses the published
     `coordinateAction_coeff` and `IsLinearVectorCoordinates.coordinateAction_eq`.
   - `defect_add_averageVector`: taking the exponent-zero coefficient of the
     cocycle identity at `(t, r, universal point)` gives, in additive
     coordinates, `δ(t, r) + β(tr) = s(t)·ρ(r) + β(t)`. So the cocycle is the
     coboundary of `ρ`.
   - `averagePoint_mul`: in multiplicative form,
     `ρ(tr) = δ(t, r)⁻¹ · s(t)·ρ(r) · ρ(t)`.
5. **The corrected section.** `sectionPoint t = i(ρ(t))⁻¹ · s(t)`.
   `sectionPoint_mul` derives `σ(tr) = σ(t) σ(r)` from `averagePoint_mul`,
   `defect_comp` and `conj_act_comp`. `averageVector_naturality`,
   `averagePoint_naturality` and `sectionPoint_naturality` show that `σ`
   commutes with every change of coefficients `A →ₐ[k] B`. `sectionHom` is
   the resulting morphism of schemes `𝔻.X ⟶ E.X` (`homOfAffinePoints`). The
   split torus is affine over `Spec k` by the published
   `isAffineHom_splitTorus_spec`. `comp_sectionHom` evaluates it on affine
   points.
6. **Group section.** `sectionHom_mul_universal` checks multiplicativity on
   the universal pair through `affine_hom_ext`. `sectionHom_mul` extends it to
   all points, and `sectionHom_comp` proves `sectionHom ≫ q = 𝟙`, because
   `i ≫ q = 1`. `extensionSection` is the homomorphism built from
   `sectionHom` by the published `homOfPoints`, and `extensionSection_comp`
   follows by `hom_ext_points`.

## Provenance and scope

This is an internal construction for the split-torus extension step of
Milne 2017, Theorem 16.26(a) (`SolvableSplitExtensionStatement`). It follows
Milne's correspondence between Hochschild extensions and `H²_0`
(Proposition 15.10), with the same cocycle convention, and the vanishing of
Hochschild cohomology of groups of multiplicative type with coefficients in a
linear representation (Remark 15.17, Proposition 15.31). Milne deduces the
vanishing from linear reductivity. Here the vanishing in degree two is proved
directly by the exponent-zero averaging above, as in the published
`SplitTorusVectorCocycle` for degree one.

The module does not prove the following:

- the existence of the scheme section `s` (torsor triviality);
- linearity of an action on a vector group;
- splitting over a nonsplit torus, or for a diagonalizable group with
  torsion;
- splitting for kernels that are proper subgroups of `G_a`
  (Milne 15.34(b)–(e)).
