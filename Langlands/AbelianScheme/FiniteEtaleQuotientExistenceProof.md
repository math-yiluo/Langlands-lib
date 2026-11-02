# Proof of existence of quotients by finite étale subgroups of projectively embedded abelian schemes

Authors: Worker 934 wrote this Lean module and this Markdown. The candidate also contains
modules by Worker 1224, listed below, and both workers are its authors.

The theorem `Langlands.AbelianScheme.finiteEtaleQuotientExistence` has type exactly
`Langlands.AbelianScheme.FiniteEtaleQuotientExistenceStatement.{u}`, for an arbitrary
universe `u`. Take a locally noetherian `S`, an abelian scheme `A` over `S`, a closed
immersion `i : A.X.left ⟶ RelativeProjectiveSpace S n` with `i ≫ toBase S n = A.X.hom`, and a
finite étale subgroup `K`. From these the proof constructs an element of `K.QuotientData`: an
abelian scheme `B` over `S` and a homomorphism `q : A ⟶ B` that is finite, étale and
surjective, whose scheme kernel is `K`. No quotient, group structure, geometric property or
kernel square is assumed. All of these are constructed.

## Sources and the route of the proof

The statement Markdown explains the source: Edixhoven–van der Geer–Moonen, *Abelian
Varieties* (registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`). The
source has no single theorem with this conclusion over a general base. The proof follows
the plan given there, with the following implementation choices.

1. **Free translation action** (EVM Definition (4.1)(ii), Example (4.3)). The proof uses the
   translation action of `K` on `A`, written as the pair `s, t : K ×_S A ⟶ A` with
   `s(k, x) = x` and `t(k, x) = k·x`. This pair is a finite locally free equivalence
   relation: `s` and `t` are finite, flat and locally of finite presentation, jointly
   monomorphic, and define an equivalence relation on `T`-points for every `T`. This is the
   ported FLT theorem
   `GroupLawOverBase.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid`.
2. **Orbit affineness** (EVM Remark (4.17)(i)). EVM (4.16) asks that orbits of closed points
   lie in affine opens. The quotient theorem used here asks this for the orbit of every
   point. That is the case `E = U` of footnote 1 of Stacks Tag 07S6, as explained in the
   published `FiniteLocallyFreeEquivalenceRelationQuotientStatement`. Each orbit is a finite
   subset of one fibre of `A.X.hom`. Worker 1224's theorem
   `Langlands.AlgebraicGeometry.RelativeProjectiveSpace.exists_isAffineOpen_forall_mem_of_fibre`
   puts every finite subset of a fibre of a closed subscheme of relative projective space
   into one affine open. This is where the displayed embedding `i` is used.
3. **Quotient scheme and torsor square** (EVM Theorem (4.16)(i), (iii)). The ported FLT
   theorem `AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`
   (published Library module
   `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation`) gives a scheme `P` and
   `p : A.X.left ⟶ P`. The map `p` is finite, flat, locally of finite presentation and
   surjective, satisfies `IsPullback s t p p` (the torsor square `K ×_S A ≅ A ×_P A`), and is a
   coequalizer of `s` and `t`.
4. **Group structure and kernel** (EVM (4.37), Theorem (4.39)(c), Definition (3.13)). EVM
   gets the group structure from the fppf quotient sheaf. The ported FLT theorem
   `GroupLawOverBase.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isColimit` instead
   descends the group law directly. The maps `A ×_S A ⟶ A ×_S P ⟶ P ×_S P` are base changes of
   `p` and hence again quotient maps, so multiplication, unit and inverse descend through
   them. This uses that `A` is commutative, so `K` is normal. It gives a commutative group
   law on `P` over `S` for which `p` is multiplicative, and a point of `A` maps to the unit
   of `P` exactly when it factors through `K`. The ported FLT files state this over
   `Spec R`. This candidate generalizes them to an arbitrary base `S`, because the proofs
   never use that the base is affine. Their Markdown files list the changes.
5. **Étaleness of `q`.** This is the derivation given in item 6 of the statement Markdown.
   In the torsor square, `s` is a base change of the étale morphism `K.G.X.hom`, so it is
   étale. Mathlib's descent of étaleness along surjective, flat, quasi-compact morphisms then
   makes `p` étale.
6. **Abelian-scheme output.** This is the derivation given in item 5 of the statement
   Markdown. Worker 1224's `Langlands.AbelianScheme.ofFiniteEtaleSurjective` takes the
   commutative group scheme `B` and the finite étale surjection `p` with `p ≫ g = A.X.hom`.
   From these it shows that `g` is smooth and proper with geometrically connected fibres,
   which makes `B` an abelian scheme.

## Modules added by this candidate

Worker 934:

- this module, `Langlands.AbelianScheme.FiniteEtaleQuotientExistenceProof`;
- the seven generalized FLT group-law modules under `Langlands/AnthropicFLT/OverBase/`:
  `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`,
  `Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`,
  `Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction`, and the statement and proof
  modules (`Theorems/Thm_…`, `P2M/Sol/S_…`) of
  `GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid`
  and of `GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit`.

Worker 1224:

- `Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent` (`ofFiniteEtaleSurjective` and
  the property-descent lemmas);
- `Langlands.AlgebraicGeometry.RelativeProjectiveSpaceFibreAffineOpen` (orbit affineness);
- the FLT port of smooth source descent,
  `AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`,
  (`Theorems/Thm_…` and `P2M/Sol/S_…` modules under `Langlands/AnthropicFLT/`). The
  `Algebra.IsSmoothAt` and `H1Cotangent` FLT ports it imports are already in the Library.

Each of these modules has its own Markdown with its sources and the changes made to it.

## The Lean proof

Namespace `Langlands.AbelianScheme.FiniteEtaleQuotientExistence`, with `S : Scheme.{u}`.

**`mapPt ψ hψ x`.** For `ψ : D ⟶ E` with `ψ ≫ gE = gD` and a point `x : SchemeHomOver t gD`,
this is the point `x ≫ ψ` of `E`. `overHomEquivSchemeHomOver_comp_homMk` says that composing
a morphism `T ⟶ Over.mk gD` with `Over.homMk ψ hψ` corresponds to `mapPt` on points. Both
sides are morphisms `T.left ⟶ E`, and `simp` checks that they agree.

**`isMonHom_homMk`.** Let `Over.mk gD` carry a group object and let `LE` be a relative group
law on `gE`. If `mapPt ψ hψ` is multiplicative from the induced law
`relativeGroupLawOfGrpObj S gD` to `LE`, then `Over.homMk ψ hψ` is a monoid morphism into the
group object `LE.grpObjOverMk`. The unit is preserved: multiplicativity applied to `1·1`
gives `ψ(1) = ψ(1)·ψ(1)`, so `ψ(1) = 1` after multiplying by `ψ(1)⁻¹`. The two `IsMonHom`
equations hold between morphisms out of `𝟙_ (Over S)` and out of `Over.mk gD ⊗ Over.mk gD`.
They are checked after the injective map `overHomEquivSchemeHomOver` to points, using
`MonObj.one_eq_one`, `MonObj.mul_eq_mul` and `MonObj.comp_mul`, the description of the
points of `LE.grpObjOverMk` (`overHomEquivSchemeHomOver_one`, `_mul`), and `tensorHom_fst`,
`tensorHom_snd`.

**`nonempty_quotientData_of_forall_finset_fibre`.** Hypotheses: `[IsLocallyNoetherian S]`,
an abelian scheme `A`, a finite étale subgroup `K`, and `hfib`. The hypothesis `hfib` says
that every finite set of points of `A.X.left` lying over one point `s` of `S` lies in an
affine open. The conclusion is `Nonempty K.QuotientData`.

- `L := relativeGroupLawOfGrpObj S A.X.hom` is the group law on points of `A`, and
  `j := CommGroupScheme.hom K.inclusion` is a closed immersion with
  `hjf : j ≫ A.X.hom = K.G.X.hom`. So `j ≫ A.X.hom` is finite, flat, locally of finite
  presentation and étale.
- `hE_one`, `hE_mul`, `hE_inv`: the unit, products and inverses of points factoring through
  `j` again factor through `j`. A `t`-point of `K` is a morphism `Over.mk t ⟶ K.G.X`, and
  `K.inclusion` is a monoid morphism, so `MonObj.one_comp`, `MonObj.mul_comp` and
  `GrpObj.inv_comp` give the factorizations through `j`. The point of `K` in each case is
  `1`, `a * b` or `a⁻¹`. `hcomm`: `L` is commutative, by
  `relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj` and `A.comm`.
- `finiteLocallyFree_mono_equivalence_actionGroupoid` shows that
  `s := pullback.snd (j ≫ A.X.hom) A.X.hom` and `t := L.action j` form a finite locally free,
  jointly monomorphic equivalence relation.
- `haff`: for a point `x`, the fibre `s⁻¹{x}` is finite because `s` is finite
  (`Scheme.Hom.finite_preimage_singleton`). Its image under `t` lies over `A.X.hom x`
  (`action_over`), so `hfib` puts this finite set into an affine open.
- `Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` gives `P`, `p`, `w`, the
  four properties of `p`, `hR : IsPullback s t p p` and the coequalizer `hcoeq`. Then
  `exists_relativeGroupLaw_quotient_of_isColimit` gives `g : P ⟶ S` with `hg : p ≫ g = A.X.hom`,
  a law `LP`, multiplicativity `hmul`, commutativity `hcommP` and the kernel property `hker`.
- `B : CommGroupScheme S` has `X := Over.mk g`, group object `LP.grpObjOverMk`, and
  commutativity from `hcommP` through `isCommMonObj_grpObjOverMk_iff_mul_comm`. By
  `isMonHom_homMk` and `hmul`, `Over.homMk p hg` is a monoid morphism. `qB : A ⟶ B` is the
  corresponding morphism of commutative group schemes (`Additive.ofMul (Grp.homMk …)`), with
  underlying scheme morphism `p`.
- Étaleness: `MorphismProperty.of_isPullback_of_descendsAlong`, with `P := Etale`,
  `Q := Surjective ⊓ Flat ⊓ QuasiCompact`, is applied to `hR`. The map `p` is surjective,
  flat, and quasi-compact (since it is finite), and `s` is étale as a base change of
  `j ≫ A.X.hom`. So `p` is étale.
- Kernel square. `hone`: the unit `t`-point of `LP` is `t ≫ η[Over.mk g].left`. `hcommsq`:
  `j ≫ p = K.G.X.hom ≫ η.left`, by `hker` applied to `j`. `hsq`: suppose
  `a ≫ p = b ≫ η.left`. Composing with `g` and using `hg` gives `b = a ≫ A.X.hom`. So the point
  `a ≫ p` is the unit, and `hker` makes `a` factor through `j`. `PullbackCone.IsLimit.mk`
  turns these facts into the limit property of the square. The lift is the chosen
  factorization, its second leg is checked by composing with `A.X.hom`, and uniqueness holds
  because `j` is a monomorphism.
- The result is the `QuotientData` with `B := ofFiniteEtaleSurjective A B p hg` (Worker 1224)
  and `q := qB`, whose underlying morphism `p` is finite, étale and surjective, together with
  the kernel square just constructed.

**`Langlands.AbelianScheme.finiteEtaleQuotientExistence`.** After introducing `S`, the
instance, `A`, `n`, `i`, the closed-immersion instance, `hi` and `K`, the proof applies
`nonempty_quotientData_of_forall_finset_fibre`. Its hypothesis `hfib` is
`RelativeProjectiveSpace.exists_isAffineOpen_forall_mem_of_fibre A.X.hom n i hi`.

## Declarations

- def `Langlands.AbelianScheme.FiniteEtaleQuotientExistence.mapPt`
- theorem `Langlands.AbelianScheme.FiniteEtaleQuotientExistence.overHomEquivSchemeHomOver_comp_homMk`
- theorem `Langlands.AbelianScheme.FiniteEtaleQuotientExistence.isMonHom_homMk`
- theorem `Langlands.AbelianScheme.FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`
- theorem `Langlands.AbelianScheme.finiteEtaleQuotientExistence`
