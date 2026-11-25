# Valuative lifting for conjugates of the image torus

This module proves `Langlands.GroupScheme.SelfCentralizingConjugacyValuationLiftStatement.{u}`
as `Langlands.GroupScheme.selfCentralizingConjugacyValuationLift`. The statement, its
hypotheses and its source correspondence are explained in
`SelfCentralizingConjugacyValuationLiftStatement.md`. This file describes the Lean
proof, whose route differs from the one sketched there (see "Comparison with the
source route" below).

Notation. `S = Spec R`, `L = GeneralLinear.groupScheme (Fin m) R`,
`s = Spec.map (CommRingCat.ofHom (algebraMap A Ω)) : Spec Ω ⟶ Spec A`,
`a = b ≫ M.hom : Spec A ⟶ S`, and `k` is the residue field of `A`. A subscript `_A`
means base change along `a`, and `_Ω`, `_k` mean further base change along `s` and
along `v = Spec.algebraMap A k`. `B = (baseChange b).obj K` is the subtorus of `L_A`
classified by `b`. Its inclusion is `familyHom j b₀`, where
`b₀ = Over.homMk b rfl : Over.mk a ⟶ M`.

## The graph quotient

The proof never uses a quotient `G/ker ρ`. It uses the smooth, separated,
quasi-compact group `Q = F.quotient` from
`TorusGraphQuotient.groupFactorization ρ t π e …`
(module `Langlands.GroupScheme.Torus.TorusGraphGroupQuotient`). Here `Q` is the
quotient of `G × D` by the graph of `T`, and `F` also provides:

- a monomorphism `F.embedding : Q ⟶ L` through which `ρ` and `e` factor,
- a smooth surjective cover `F.smoothCover : G × D ⟶ Q` with
  `F.smoothCover ≫ F.embedding = (g, d) ↦ ρ(g) e(d)` (`F.cover_fac`),
- a projection `G ⟶ Q` that is flat, surjective and locally of finite
  presentation,
- the image torus `F.torus : D ⟶ Q` with `F.torus ≫ F.embedding = e`.

The construction needs the central-kernel hypothesis on `ρ`, the
representability of the centralizer of `T` by `t`, the fppf properties of `π`, and
`π ≫ e = t ≫ ρ`. These are hypotheses of the statement. Smoothness and
quasi-compactness of `D` come from `RelativeTorus.IsTorus.smooth` and
`RelativeTorus.IsTorus.isAffineHom`. `e` is a monomorphism because it is a closed
immersion.

## Steps 1–3: the integral factor

These steps are carried out in `Langlands.GroupScheme.Torus.ValuationIntegralFactor`, by
`TorusGraphQuotient.GroupFactorization.integralFactor A F he j hj hK f hf g b hgb`; that
module's Markdown has the details. It returns a
`TorusSubgroupModuli.IntegralFactor A D.toGrp F.embedding j a b₀`, whose four fields
are the data used below:

- `factor`, written `c : B ⟶ Q_A`,
- `fac : c ≫ (F.embedding)_A = familyHom j b₀`, written `hc`,
- `isClosedSubgroup_factor : IsClosedSubgroup c`, written `hcl`,
- `genericIso : B_Ω ≅ (D_A)_Ω`, written `σ`.

1. **Generic factor.** The given point `g : Spec Ω ⟶ G.X.left` satisfies
   `s ≫ b = g ≫ f.left`, so over `Ω` the family classified by `b` is the conjugate
   of `e(D)` by `ρ(g)`. `restrictedFamilyFactorization`
   (module `Langlands.GroupScheme.HomScheme.ConjugateFamilyFactorization`) turns
   this into a factor `B_Ω ⟶ (Q_A)_Ω` of the family inclusion through
   `F.embedding`, together with the isomorphism `B_Ω ≅ (D_A)_Ω` given by conjugation.
2. **Extension over `A`.** `genericGroupMonoLift` (module
   `Langlands.GroupScheme.GenericGroupMonoLift`) extends the generic factor to a
   homomorphism `c : B ⟶ Q_A` with `c ≫ (F.embedding)_A = familyHom j b₀`. It
   uses that `A` is an integrally closed domain with fraction field `Ω`, that `B`
   is smooth with geometrically connected fibres (it is a torus), and that
   `(F.embedding)_A` is a quasi-compact monomorphism locally of finite type.
3. **Closedness.** `familyHom j b₀` is a closed immersion because `j` is, and the
   monomorphism `(F.embedding)_A` is separated, so `c` is a closed immersion.

Algebraic closedness of `Ω` is not used in these steps.

## Steps 4–5: `ValuationLift.exists_lift_of_integralFactor`

The lemma takes any `F : TorusGraphQuotient.GroupFactorization ρ e` and any integral
factor `(c, hc, hcl, σ)` as above, and returns `h : Spec A ⟶ G.X.left` with
`h ≫ f.left = b`.

1. **The valuation ring is strictly henselian.** `A` is henselian
   (`Langlands.LocalGalois.Separable.sepClosed_henselian`) and its residue field is
   algebraically closed (`Langlands.LocalGalois.residue_isAlgClosed`).
2. **The residue fibre of the quotient.** `torusImageMaximal_fieldPoint`
   (module `Langlands.GroupScheme.Torus.TorusImageFieldFibre`), applied to the
   graph-quotient data and to the field point `v ≫ a` of `S`, shows that the fibre
   of `Q` over `k` is connected and affine, and that `F.torus` is a maximal torus
   of it. It uses the connected affine residue fibres of `G` (`hfib`) and the
   fibrewise maximality of `t`. These properties are moved from the direct pullback
   along `v ≫ a` to the iterated pullback `(Q_A)_k` through
   `baseChangeCompIso'`, and with `isMaximalTorus_baseChange_comp` for maximality.
3. **Both tori split.** Over the henselian ring `A` with separably closed residue
   field, the tori `D_A` and `B` are split
   (`RelativeTorus.IsTorus.isSplitTorus_of_henselian`).
4. **`c` is maximal in the residue fibre.** `isMaximalTorus_fieldFibre_of_split_of_fieldIso`
   applies to the split tori `D_A` and `B`, their closed embeddings
   `(F.torus)_A` and `c` into `Q_A`, the generic isomorphism `σ.symm`, and the
   maximality of `(F.torus)_k` from step 2. Split tori with isomorphic generic
   fibres have the same rank, so `c_k` is also a maximal torus of `(Q_A)_k`.
5. **Integral conjugacy.** `exists_henselian_splitTorus_conjugacy_of_separated`
   (module `Langlands.GroupScheme.Torus.SeparatedTransporter`) applies to the
   smooth separated group `Q_A` over the henselian ring `A` and its two split
   tori, which are maximal in the closed fibre. It gives a point `z` of `Q_A` and
   an isomorphism `ε` of tori with `(F.torus)_A ≫ inner(z) = ε ≫ c`. The ambient
   group `Q_A` need not be affine.
6. **Conjugate family.** `evaluate_eq_range_conjugatePullback_of_factor`
   (module `Langlands.GroupScheme.HomScheme.ConjugateFamilyProductLift`), with `hc`
   and this conjugacy, shows that the subtorus family classified by `b₀` is the
   `z`-conjugate of the family `F.embedding ∘ F.torus`. That composite is `e` by
   `F.torus_fac`.
7. **Lift along the smooth cover.** `exists_parameter_of_conjugate_of_smooth_product`
   lifts `z` along the smooth surjective cover `F.smoothCover : G × D ⟶ Q` over
   the strictly henselian base. It discards the `D`-coordinate, which normalizes
   the range of `e`. The result is `h : Over.mk a ⟶ G.X` with `h ≫ f = b₀`, using
   the universality of `j` and `hf`. The underlying scheme morphism `h.left` is the
   required lift.

## The theorem `selfCentralizingConjugacyValuationLift`

After introducing the hypotheses, the proof installs the instances listed in
"The graph quotient", fixes `F := TorusGraphQuotient.groupFactorization ρ t π e …`,
builds the integral factor of steps 1–3, and applies
`ValuationLift.exists_lift_of_integralFactor`.

## Comparison with the source route

The route in the statement's Markdown follows SGA 3: it first identifies the scheme
of maximal tori of `G` with a closed subscheme of `M` (Exposé XVI, Lemma 3.2,
through `G/ker ρ`), then applies conjugacy of maximal tori over strictly henselian
local rings (Exposé XII, Theorem 7.1(b)). The Lean proof replaces the closed
subscheme with the graph quotient `Q`, which is a group with a monomorphism into
`GL_m` and need not be affine. The closedness argument becomes the extension of the
generic factor over the integrally closed ring `A` (steps 1–3). Conjugacy takes
place in `Q_A`, and the lift to `G` goes through the smooth cover `G × D ⟶ Q`
rather than through a quotient by the central kernel. The residue-fibre maximality
argument is Exposé XII, Theorem 7.1, together with the rank comparison of split
tori.
