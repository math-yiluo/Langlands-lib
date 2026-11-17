# Proof: homomorphisms agreeing on a Borel subgroup agree (Milne 17.21)

Worker 5655.

`Langlands.GroupScheme.borelHomomorphismRigidity` proves exactly
`Langlands.GroupScheme.BorelHomomorphismRigidityStatement.{u}`
([statement](BorelHomomorphismRigidityStatement.md)), in every universe and with no
additional hypotheses. The statement is as follows. Let `k : Type u` be an algebraically closed
field. Let `G` and `G'` be smooth, affine, connected group schemes over `Spec k`, let
`i : B ⟶ G` be a Borel subgroup, and let `R : Type u` be a commutative `k`-algebra with
`b : Spec R ⟶ Spec k` the induced map. Then any two homomorphisms
`φ₁ φ₂ : G_R ⟶ G'_R` with `i_R ≫ φ₁ = i_R ≫ φ₂` are equal. The module also contains two
general helper lemmas, in namespace `Langlands.GroupScheme.BorelHomomorphismRigidity`. It
adds no definitions or axioms.

The proof follows Milne's argument for Proposition 17.21 (Milne, *Algebraic Groups*, 2017,
p.358). The difference map `x ↦ φ₁(x) φ₂(x)⁻¹` is constant on cosets of `B_R`. So it factors
through `(G/B)_R`, and as `G/B` is proper and `G'` is affine, it is constant with value `e`.
Milne gives the last step through affine coordinates and global functions over `R`.
The implementation expands that argument, as described below.

## Helper lemmas

- `exists_factor_of_isIso_appTop`: let `h : P ⟶ P'` be a morphism of schemes such that
  `h.appTop : Γ(P', ⊤) ⟶ Γ(P, ⊤)` is an isomorphism, and let `Y` be an affine scheme. Then every
  `ρ : P ⟶ Y` factors as `h ≫ τ`. Proof: take
  `τ = P'.toSpecΓ ≫ Spec.map (ρ.appTop ≫ inv h.appTop) ≫ inv Y.toSpecΓ`. The equation
  `h ≫ τ = ρ` is checked after composing with the isomorphism `Y.toSpecΓ`, using naturality of
  `toSpecΓ` twice.
- `toSpecΓ_comp_eq`: let `k` be an algebraically closed field, `X` an integral scheme with
  `p : X ⟶ Spec k` and a section `e : Spec k ⟶ X` (`e ≫ p = 𝟙`), and `f : Z ⟶ Spec k` a proper
  morphism. Then every `q : X ⟶ Z` over `k` satisfies
  `q ≫ Z.toSpecΓ = p ≫ e ≫ q ≫ Z.toSpecΓ`, that is, `X → Z → Spec Γ(Z)` factors through the
  `k`-point given by `e`. Proof: both sides land in an affine scheme, so by `ext_of_isAffine` it
  is enough to show that `q.appTop` equals `q.appTop ≫ e.appTop ≫ p.appTop`. Take
  `a ∈ Γ(Z, ⊤)`. Since `f` is proper, `Γ(Z, ⊤)` is a finite `k`-algebra
  (`Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions.finite_algebra`), so `a` is integral
  over `k`. Hence `q.appTop a ∈ Γ(X, ⊤)` is integral over `k`, by `IsIntegral.map_of_comp_eq`,
  since `q` is over `k`. As `X` is integral, `Γ(X, ⊤)` is a domain. So the minimal polynomial of
  `q.appTop a` is irreducible, and of degree one because `k` is algebraically closed. Hence
  `q.appTop a` is the image `p.appTop c` of a constant `c ∈ k`
  (`minpoly.mem_range_of_degree_eq_one`), and `e ≫ p = 𝟙` gives
  `p.appTop (e.appTop (p.appTop c)) = p.appTop c`.

## The main theorem

After introducing the hypotheses (with `b` the base-change map), the proof does the following.

1. **The quotient `G/B` and its properness.** `smoothSubgroupQuotientExistence` gives a
   homogeneous quotient `q : G.X ⟶ Q` by `B`. It applies because a Borel subgroup is a smooth
   closed subgroup. The quotient is packaged as
   `Q₀ : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i`. The Borel subgroup is
   parabolic (`IsParabolicSubgroup i`): by `borelAlgClosedFieldExtensionStatement`, its base
   change to `AlgebraicClosure k` is again a Borel subgroup, which factors through itself by the
   identity. Then `parabolicSubgroupQuotientProper` gives `IsProper Q.hom`.
2. **Base change.** `Q₁ := Q₀.baseChange b` is a homogeneous quotient of `G_R` by the subgroup
   `j := i_R`. Its projection `Q₁.projection` is smooth, hence flat, and also surjective and
   quasi-compact.
3. **The difference map.** Let `δ := φ₁.hom.hom * φ₂.hom.hom⁻¹ : G_R.X ⟶ G'_R.X`, the product
   in the group of morphisms into the group object `G'_R`. On `T`-points it is
   `x ↦ (x ≫ φ₁) (x ≫ φ₂)⁻¹`. If `g⁻¹ h` lies in the range of `j`, then `h = g · (y ≫ j)`.
   Since `φ₁` and `φ₂` are homomorphisms that agree after `j` (the hypothesis), this gives
   `g ≫ δ = h ≫ δ` by a `group` computation. By `ParabolicQuotient.exists_factor` (fpqc
   descent along the flat, surjective, quasi-compact projection, whose fibres are the cosets of
   `j`), there is `ρ : Q₁.scheme ⟶ G'_R.X` with `Q₁.projection ≫ ρ = δ`.
4. **Global functions of `Q_R`.** The proof works with the underlying scheme maps
   `P : pullback G.X.hom b ⟶ pullback Q.hom b`, `r := ρ.left` and `d := δ.left`, with
   `P ≫ r = d`. Let `hmap : pullback Q.hom b ⟶ pullback b (algebraSchemeMap Q.hom)` be the base
   change along `b` of the canonical map `Q → Spec Γ(Q, ⊤)` over `k`. It is the composite of the
   symmetry `pullbackSymmetry Q.hom b` with
   `Langlands.AlgebraicGeometry.FieldGlobalUnits.schemeMap Q.hom (Over.mk b)`. Since `Q.hom` is
   proper, `isIso_schemeMap_appTop` shows that `hmap` induces an isomorphism on global functions.
   The symmetry's inverse on global functions is given explicitly. `G'_R` is affine, because
   `G'` is affine over `k` and affine morphisms are stable under base change. So
   `exists_factor_of_isIso_appTop` gives `τ` with `hmap ≫ τ = r`.
5. **Constancy.** `G` is integral (`CoverPreimage.isIntegral_of_smooth_connected`) and has the
   unit section `e := η[G.X].left`. By `toSpecΓ_comp_eq` applied to `q.left`,
   `q.left ≫ Q.left.toSpecΓ` factors through the point `e`. Let
   `s : Spec R ⟶ pullback b (algebraSchemeMap Q.hom)` be the section with components `𝟙` and
   `b ≫ e ≫ q.left ≫ Q.left.toSpecΓ`. Checking both pullback projections, using
   `HomogeneousQuotient.baseChange_projection_fst` and `pullback.condition`, gives
   `P ≫ hmap = pullback.snd G.X.hom b ≫ s`. Hence `d = pullback.snd G.X.hom b ≫ s ≫ τ`, so `δ`
   factors through the structure map of `G_R`.
6. **Value at the unit.** Since `φ₁` and `φ₂` preserve the unit, `η[G_R] ≫ δ = η[G'_R]`.
   Composing the factorization of step 5 with the unit section of `G_R` gives
   `s ≫ τ = η[G'_R].left`. So `d` is the structure map followed by the unit of `G'_R`,
   that is, `δ = 1` (`Hom.one_def`, `Over.toUnit_left`). Then `mul_inv_eq_one` gives
   `φ₁.hom.hom = φ₂.hom.hom`, and `Grp.hom_ext` gives `φ₁ = φ₂`.

## Library results used

- `Langlands.GroupScheme.smoothSubgroupQuotientExistence` (`HomogeneousQuotientProof`).
- `Langlands.GroupScheme.parabolicSubgroupQuotientProper` (`ParabolicQuotientProperProof`).
- `Langlands.GroupScheme.borelAlgClosedFieldExtensionStatement`
  ([`Absolute.BorelAlgClosedFieldExtensionProof`](BorelAlgClosedFieldExtensionProof.md)).
- `HomogeneousQuotientFromEmbedding.HomogeneousQuotient.baseChange` and
  `baseChange_projection_fst` (`HomogeneousQuotientBaseChange`).
- `Langlands.GroupScheme.ParabolicQuotient.exists_factor` (`ParabolicQuotientProperReduction`).
- `Langlands.AlgebraicGeometry.FieldGlobalUnits.schemeMap`, `schemeMap_fst`, `schemeMap_snd`,
  `isIso_schemeMap_appTop`, `toSpecΓ_over` (`AlgebraicGeometry.Units.FieldGlobalFunctions`).
- `Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions.finite_algebra` and
  `GlobalFunctionsAlgebra.algebra` (`AlgebraicGeometry.Modules.FieldGlobalFunctionsAlgebra`).
- `Langlands.GroupScheme.CoverPreimage.isIntegral_of_smooth_connected`
  (`SimplyConnected.CoverPreimageDerived`).

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
