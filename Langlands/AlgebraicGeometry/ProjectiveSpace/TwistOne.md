# The twisting sheaves `𝒪(d)` on `Proj` and `𝒪(1)` on projective space

This module constructs the twisting sheaf `𝒪(d) = S(d)~` on `Proj 𝒜` for every `ℕ`-graded commutative ring and every `d : ℕ` as an actual object of `(Proj 𝒜).Modules`. It defines the global section `a / 1` for each homogeneous `a` of degree `d`. It then specializes to `d = 1` on the published polynomial projective space `ProjectiveSpace R n` and defines the homogeneous coordinates `X i` as actual global sections of `𝒪(1)`.

Sources:

- registered original `stacks-projective-space-twists-morphisms-2026-10-26`, file `01MM.html`: Section 27.10, Definition 27.10.1, Equation 27.10.1.3 and Lemma 27.10.2. File `01ND.html`, Definition 27.13.2 and Lemma 27.13.3, gives the polynomial projective space and its coordinate opens. These are already used by the imported `Langlands.AlgebraicGeometry.ProjectiveSpace`.
- registered original `stacks-proj-graded-ring-27-8-2026-10-27`, file `01M3.html`: Section 27.8, Definition 27.8.3 and Lemma 27.8.4. These define the sheaf `M~` of a graded module on `Proj(S)`.

The comment threads of both pages contain only typo and reference corrections. None of them changes these definitions or lemmas.

## Convention

Stacks Definition 27.10.1 sets `𝒪_X(n) = S(n)~`, where `S(n)` is the shifted graded module with `S(n)_k = S_{n+k}`. Here the twist is `d : ℕ`, and the elements of `S(d)` of degree `k` are the elements of `𝒜 (k + d)`. So `𝒪(1)` is built from `S(1)`, with `S(1)_k = S_{k+1}`. Its sections are locally fractions with numerator of degree one more than the denominator. This is `𝒪(1)`, not its dual `𝒪(-1)`. The coordinate section `X i` is a section of it, as in Equation 27.10.1.3.

Only twists `d : ℕ` are constructed. Negative twists, and in particular `𝒪(-1)`, are not defined in this module, and the task needs only `d = 1`.

## Construction of `S(d)~`

All declarations are in namespace `Langlands.AlgebraicGeometry`. The auxiliary ones are in `Langlands.AlgebraicGeometry.ProjTwist`.

The construction follows the same pattern as Mathlib's structure sheaf of `Proj` (`ProjectiveSpectrum.Proj.structureSheaf`). Sections are dependent functions that are locally given by a single fraction.

- `ProjTwist.Localizations 𝒜 x` is the ordinary localization `A_𝔭` of the ambient ring at the homogeneous prime `𝔭` of the point `x`.
- `ProjTwist.IsFraction d f` says that a dependent function `f` on an open `U` is a fixed fraction `a / b` on `U`. Here `b ∈ 𝒜 i` is homogeneous of some degree `i` and lies outside every prime of `U`, and `a ∈ 𝒜 (i + d)`.
- `ProjTwist.isFractionPrelocal` records that this predicate is stable under restriction. `ProjTwist.isLocallyFraction d` is its sheafification as a local predicate: around every point of `U` the function is such a fraction on a smaller open.
- `ProjTwist.sectionsInType 𝒜 d` is the `Type`-valued sheaf `subsheafToTypes (isLocallyFraction 𝒜 d)`. `ProjTwist.sectionsAddSubgroup` shows that these sections are closed under zero, sums (`a/b + a'/b' = (b'a + ba')/(bb')`) and negation. This gives the additive group structure.
- `ProjTwist.smul_mem` shows that multiplying pointwise by a section of the structure sheaf of `Proj 𝒜` preserves the predicate: `(c/e) · (a/b) = ca/(eb)`, where `c` and `e` have equal degree. The resulting `Module` instance over the structure-sheaf sections is checked directly. `sectionsInType_add_apply`, `sectionsInType_zero_apply` and `sectionsInType_smul_apply` record that the operations are pointwise. At a point, the action is multiplication in `A_𝔭` by the value of the structure-sheaf section, viewed in `A_𝔭`.
- `ProjTwist.presheafInAb` is the presheaf of abelian groups on these sections. `ProjTwist.presheafOfModules` packages it with the module structure as a presheaf of modules over `(Proj 𝒜).ringCatSheaf`, by Mathlib's `PresheafOfModules.ofPresheaf`. Restriction is restriction of functions, so compatibility with scalars holds by `rfl`.
- `projTwistingSheaf 𝒜 d : (Proj 𝒜).Modules` is this presheaf of modules. Its sheaf condition is the sheaf condition of `sectionsInType`, transferred along the forgetful functor by Mathlib's `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`.

No sheafification functor, gluing datum or structure field is assumed. The sheaf property comes from the local-predicate construction itself.

### Relation with Stacks' `M~` (explanation, not formalized)

Stacks Section 27.8 first defines `M~` on the standard opens by `Γ(D₊(f), M~) = M_(f)`. Definition 27.8.3 extends it to all opens, and Lemma 27.8.4(5) gives its stalk `M_(𝔭)` at a point `𝔭`. For `M = S(d)`, an element of `S(d)_(𝔭)` is a fraction `a/b` with `b` homogeneous outside `𝔭` and `a ∈ S_{deg b + d}`. The map `S(d)_(𝔭) → A_𝔭` sending `a/b` to `a/b` is injective. If `c · m = 0` in `A` with `c ∉ 𝔭` and `m` homogeneous, then each homogeneous component of `c` kills `m`, and some component lies outside the homogeneous prime `𝔭`. So the values of `projTwistingSheaf 𝒜 d` at a point are exactly elements of `S(d)_(𝔭)`, viewed inside `A_𝔭`. Mathlib's `HomogeneousLocalization`, used by its structure sheaf of `Proj`, uses the same embedding into `A_𝔭`. For `d = 0` the construction becomes Mathlib's structure sheaf, composed with this embedding.

The module does **not** formalize this comparison. It does not formalize the identification `Γ(D₊(f), 𝒪(d)) = S(d)_(f)` of Lemma 27.8.4(2), the stalk description, or uniqueness of the extension in Definition 27.8.3. These are statements about the constructed sheaf. They belong to the later local-description, local rank-one and generation successors, which Worker 404 coordinates.

## Global sections `a / 1`

`projTwistingSheafSection 𝒜 d a ha : Γ(projTwistingSheaf 𝒜 d, ⊤)` is the global section with constant value `a / 1`, where `ha : a ∈ 𝒜 d`. Its local fraction witness is `a / 1` itself, with denominator `1 ∈ 𝒜 0` and numerator `a ∈ 𝒜 (0 + d)`. `projTwistingSheafSection_apply` records its value at every point. This is the canonical map `M_0 → Γ(Proj(S), M~)`, `x ↦ x/1`, of Lemma 27.8.4(6) and its proof for `M = S(d)`, so `M_0 = S_d`. Equivalently, it is the degree-`d` part of the graded ring map `S → ⊕_{n ≥ 0} Γ(X, 𝒪_X(n))` of Equation 27.10.1.3. The global-section type is the actual one: `Γ(M, U)` is Mathlib's notation for `(Scheme.Modules.presheaf M).obj (op U)`.

`projTwistingSheafSection_restrict_basicOpen` proves the following. Let `f, a ∈ 𝒜 d`. On the basic open `Proj.basicOpen 𝒜 f = D₊(f)`, the restriction of `a / 1` equals the structure-sheaf section `a / f` times the restriction of `f / 1`. The section `a / f` is the image of `HomogeneousLocalization.Away.mk 𝒜 hf 1 a _` under Mathlib's `Proj.awayToSection`. This is the multiplication-by-`f` identification from the proof of Stacks Lemma 27.10.2, in the case `n = 1` and degree `d`, evaluated on these sections. The proof is an equality of fractions in each `A_𝔭`.

## `𝒪(1)` and the coordinate sections on projective space

These declarations use the published `ProjectiveSpace R n = Proj (projectiveSpaceGrading R n)` with its total-degree grading, the variable-degree lemma `projectiveSpace_X_mem` and the coordinate opens `projectiveSpaceCoordinateOpen R n i = D₊(X i)`. None of these is changed.

- `twistOne R n : (ProjectiveSpace R n).Modules` is `projTwistingSheaf (projectiveSpaceGrading R n) 1`, the degree-one twist `𝒪(1) = S(1)~` of `S = MvPolynomial (Fin (n + 1)) R` (Definition 27.10.1 with `n = 1`, on the projective space of Definition 27.13.2).
- `twistOneCoordinate R n i : Γ(twistOne R n, ⊤)` is the global section `X i / 1`, that is `projTwistingSheafSection _ 1 (X i) (projectiveSpace_X_mem R n i)`. It is the image of `X i ∈ S_1` under Equation 27.10.1.3. It is an actual section, not a polynomial standing in for one.
- `projectiveSpaceCoordinateRatio R n i j : Γ(ProjectiveSpace R n, projectiveSpaceCoordinateOpen R n i)` is the structure-sheaf section `X j / X i` on `D₊(X i)`. It is the degree-zero element `X j / X i` of the localization away from `X i`, mapped by `Proj.awayToSection`.
- `twistOneCoordinate_restrict_coordinateOpen R n i j` proves that, on `D₊(X i)`, the restriction of `X j` equals `projectiveSpaceCoordinateRatio R n i j` times the restriction of `X i`. This is the convention stated in the task: on `D₊(X i)` the section `X j` is represented by `X j / X i` in the symbol `X i`. On overlaps the coordinate sections therefore satisfy `X j = (X j / X i) X i`. The lemma is `projTwistingSheafSection_restrict_basicOpen` with `f = X i`, `a = X j` and `d = 1`.

Every declaration works for every commutative ring `R : Type u` in the same universe and every `n : ℕ`, with no hypotheses. This includes `n = 0` and the zero ring, where `Proj` has no points.

## Not claimed

This is a definitions unit. It does not state or prove any of the following:

- that `𝒪(1)` is invertible or locally free of rank one, or that `X i` is a local basis on `D₊(X i)` (the module-level content of Lemmas 27.10.2 and 27.10.3);
- that the coordinate opens cover `ProjectiveSpace R n`;
- any bundling as `Langlands.AlgebraicGeometry.Picard.LineBundle`;
- ampleness, or the tensor comparisons `𝒪(1)^{⊗ m} ≅ 𝒪(m)` of Equation 27.10.1.1 and Lemma 27.10.3;
- that `S(d)_(f) → Γ(D₊(f), 𝒪(d))` is an isomorphism.

The tensor-product twist `ℱ(n) = ℱ ⊗ 𝒪_X(n)` of Definition 27.10.1 is not defined here. Those properties are left to later Prop statements and proofs.

## Lean notes

The file sets `backward.isDefEq.respectTransparency.types false` for the whole file. Mathlib's `ProjectiveSpectrum/StructureSheaf.lean` sets the same option on its corresponding declarations. `ProjTwist.Localizations` takes the point as an element of `ProjectiveSpectrum 𝒜` rather than of the topological space `ProjectiveSpectrum.top 𝒜`, so that instance search finds that the homogeneous prime is prime. The private lemma `ProjTwist.mem_of_eq` transports graded membership along a degree equality. The definitions use no proof holes and no axioms beyond Lean's standard ones.
