# The affine-test Hom scheme of an H-projective abelian scheme

Authors: Worker 1042.

Module `Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces`. Written for task
`6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism
functor of a projective abelian scheme). It proves the internal interface
`Langlands.AbelianScheme.AffineHomSchemePiecesStatement.{u}` (module
`Langlands.AbelianScheme.RelativeEndomorphismAffineHomScheme`) from the ported FLT Hom scheme. All
declarations are in namespace `Langlands.AbelianScheme.AffineHomSchemePieces`. The module adds no
axioms.

The mathematical input is the theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`
of the Anthropic Fermat's Last Theorem formalisation, ported in this contribution in universe-
generalized form and with the strengthened pieces clause (see its Markdown file). For commutative
group schemes `A`, `B` over `Spec S` with FLT's abelian-scheme property bundle and with invertible
modules giving closed immersions by sections, it gives a scheme `H ⟶ Spec S`, separated, locally of
finite type and of finite presentation and formally unramified, with a natural assignment `pt` of
`S`-points of `H` to morphisms `A ×_S Spec S' ⟶ B` over `S`, surjective onto points from
homomorphisms and injective on homomorphisms, and a family of pairwise disjoint, covering, closed
pieces quasi-compact over `Spec S` indexed by `Polynomial ℚ`. This module translates the data of a
Library abelian scheme into the FLT hypotheses and the FLT conclusion into the Library's relative
homomorphism functor on affine test objects.

## The FLT data of an abelian scheme

Fix a commutative ring `R : Type u` and `A : Langlands.AbelianScheme (Spec R)`.

- Instances `grpObjOverMk`, `isCommMonObjOverMk`: the group object structure of `A.X` on
  `Over.mk A.X.hom` (the same object).
- `groupLaw A`: FLT's relative group law `relativeGroupLawOfGrpObj R A.X.hom` (Library) given by
  the group structure of `A`; `groupLaw_isCommutative A`: it is commutative (the group of points
  over each test scheme is commutative, `mul_comm`).
- `propertyBundle A`: FLT's `AbelianSchemePropertyBundle R A.X.hom` holds: `A` is smooth and
  proper, its fibres are connected (Library `Scheme.Hom.isConnected_preimage_singleton` for
  abelian schemes), and it has the group law `groupLaw A`.
- `exists_lineBundle A h`: if `A.X.hom` is H-projective (`Langlands.AlgebraicGeometry.IsHProjective`:
  a closed immersion `i` into `ℙⁿ_R` over `Spec R`), there is an invertible module `L` on `A`
  (`Scheme.Modules.IsInvertible`) whose sections give a closed immersion
  (`Scheme.Modules.ClosedImmersionBySections L A.X.hom`). Proof: the ported FLT
  `ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial` applied to `i` gives `L = i^*𝒪(1)`
  with a projective presentation `𝔓` whose morphism to `ℙⁿ` is `i`, and local triviality of `L`; the
  composite of `i` with `ProjSpace.π R n` is `A.X.hom` (the structure morphism of `ℙⁿ_R` in the
  definition of `IsHProjective` is `ProjSpace.π R n`, by `rfl`).

## Relative homomorphisms and FLT homomorphisms

- `IsFLTHom A s φ hφ` (a `Prop`): FLT's condition that a morphism `φ : A ×_R Spec S' ⟶ A` over
  `Spec R` is a homomorphism, i.e. it is compatible with the group law `groupLaw A` on all points
  over all `T ⟶ Spec S'`.
- `isFLTHom_iff`: `IsFLTHom A s φ hφ` is equivalent to the multiplicativity condition `IsPtMul` of
  the gluing module `Langlands.AbelianScheme.RelativeEndomorphismOfAffineHomSchemeGluing`, for the
  test object `Over.mk s`. Proof: translate points over a scheme between FLT's `SchemeHomOver` and
  morphisms in `Over` (Library `overHomToSchemeHomOver`, `schemeHomOverToOverHom`).
- `isFLTHom_fstMap s χ`: the first projection `fstMap χ` of a relative homomorphism `χ` over
  `Over.mk s` satisfies `IsFLTHom` (from `isPtMul_fstMap`).

## Points of the Hom scheme over spectra

For a scheme `H` with `πH : H ⟶ Spec R` and an assignment `pt` with FLT's signature:

- `pt_congr`: `pt` respects equality of morphisms. `homPt pt s χ := pt S' s (fstMap χ) _`: the point
  of `H` attached to a relative homomorphism over `Over.mk s`.
- `PtNat pt`, `PtSurj pt`, `PtInj pt` (`Prop`s): FLT's naturality of `pt` along ring maps,
  surjectivity of `pt` on homomorphisms (every point is `pt` of some `φ` with `IsFLTHom`), and
  injectivity of `pt` on homomorphisms; these are the corresponding clauses of the FLT theorem.
- `homPt_injective hinj s` and `homPt_surjective hsurj s`: `homPt pt s` is a bijection from relative
  homomorphisms over `Over.mk s` to points of `H` over `s`. Proof: a relative homomorphism is
  determined by its first projection (`relativeHom_ext`), and a morphism with `IsFLTHom`
  (equivalently `IsPtMul`) is the first projection of the relative homomorphism `ofFstMap`
  (`fstMap_ofFstMap`).
- `homPt_restrict hnat c χ`: for `c : Over.mk s'' ⟶ Over.mk s`, the point of the restriction
  `restrict _ _ c χ` (Library `Langlands.GroupScheme.Cartier.restrict`) is `c.left` composed with the
  point of `χ`. Proof: `c.left = Spec.map ψ` for the ring map `ψ = Spec.preimage c.left`
  (`Spec.map_preimage`); by `fstMap_restrict` the first projection of the restriction is the
  canonical projection `baseChangeProj` followed by `fstMap χ`, and `baseChangeProj` is the pullback
  lift appearing in FLT's naturality clause (`baseChangeProj_fst`, `baseChangeProj_snd`).

## Affine test schemes

For `T : Over (Spec R)` with `T.left` affine:

- `coordRing T := Γ(T.left, ⊤)`, `isoSpec T : T.left ≅ Spec (coordRing T)` (Mathlib's
  `Scheme.isoSpec`), `specHom T := (isoSpec T).inv ≫ T.hom`, and the mutually inverse morphisms
  `toSpec T : T ⟶ Over.mk (specHom T)`, `ofSpec T` in `Over (Spec R)` (`toSpec_ofSpec`,
  `ofSpec_toSpec`).
- `restrictEquiv A T`: restriction along `ofSpec T` is a bijection from relative homomorphisms over
  `T` to relative homomorphisms over `Over.mk (specHom T)`, with inverse restriction along `toSpec T`
  (`restrict_comp`, `restrict_id`).
- `pointEquiv T πH`: points of `H` over `specHom T` correspond to morphisms `T ⟶ Over.mk πH`
  (composition with `toSpec T` and `ofSpec T`).

## The natural bijection on affine test schemes

- `homEquiv hsurj hinj T`: for affine `T`, the composite bijection
  `RelativeHom A A T ≃ (T ⟶ Over.mk πH)` of `restrictEquiv`, `homPt` and `pointEquiv`;
  `homEquiv_left` computes its underlying morphism.
- `homEquiv_restrict hnat b χ`: for `b : T' ⟶ T` between affine test objects,
  `homEquiv T' (restrict _ _ b χ) = b ≫ homEquiv T χ`. Proof: restriction along `ofSpec T'` of the
  restriction along `b` is the restriction along `ofSpec T' ≫ b ≫ toSpec T` of the restriction
  along `ofSpec T`; apply `homPt_restrict`.
- `natIso hnat hsurj hinj`: on the full subcategory of affine test objects
  (`ObjectProperty.ι`), the relative endomorphism functor
  `relativeHomFunctor A.toCommGroupScheme A.toCommGroupScheme ⋙ forget AddCommGrpCat` is naturally
  isomorphic to `yoneda.obj (Over.mk πH)`; components `homEquiv`, naturality `homEquiv_restrict`
  (`NatIso.ofComponents`).

## Main theorem

- `affineHomSchemePieces : AffineHomSchemePiecesStatement.{u}`. Given a noetherian `R : Type u` and
  an abelian scheme `A` over `Spec R` with `A.X.hom` H-projective, take `L` from `exists_lineBundle`
  and apply the ported FLT Hom-scheme theorem to `A`, `A` (both with `groupLaw A`,
  `groupLaw_isCommutative A`, `propertyBundle A` and `L`). Its scheme `H` gives `Over.mk πH`, which
  is separated, locally of finite type and formally unramified; its `pt` gives the natural
  isomorphism `natIso` on affine test objects; and its pieces `U : Polynomial ℚ → H.Opens`, reindexed
  by `ULift.{u} (Polynomial ℚ) : Type u`, are closed, quasi-compact over `Spec R`, pairwise disjoint
  and cover `H` (the supremum is unchanged by reindexing, `Equiv.ulift.surjective.iSup_comp`).

## Dependencies

- Same contribution: `Langlands.AbelianScheme.RelativeEndomorphismAffineHomScheme` (the interface),
  `Langlands.AbelianScheme.RelativeEndomorphismOfAffineHomSchemeGluing` (`IsPtMul`, `fstMap`,
  `ofFstMap`, `relativeHom_ext`, `fstMap_restrict`, `isPtMul_fstMap`), and the ported FLT modules
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial`
  and
  `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`.
- Library: `Langlands.AlgebraicGeometry.ProjectiveSpace.Charts`,
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`, and the
  relative-Hom interface `Langlands.GroupScheme.Cartier.Restriction` (through the gluing module).
