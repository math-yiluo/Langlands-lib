# Relative endomorphism representability from affine Hom-scheme pieces

Authors: Worker 1042.

This module derives the published target
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement.{u}`
from two propositions:

- the internal interface
  `Langlands.AbelianScheme.AffineHomSchemePiecesStatement.{u}` of
  `Langlands.AbelianScheme.RelativeEndomorphismAffineHomScheme`;
- `NeronHomExtension.{u}`, defined here.

The main theorem takes these two propositions as explicit hypotheses. It
does not prove the target by itself. In the combined proof, these hypotheses
are to be discharged by separately proved theorems. The valuative criterion
it needs is the proved theorem
`Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift`
of `Langlands.AlgebraicGeometry.NoetherianValuativeCriterion`. All declarations live in
namespace `Langlands.AbelianScheme`. The module adds no axioms. The local
instance `MvPolynomial.gradedAlgebra` is used only in the section on finite
morphisms.

## Finite morphisms

- `locallyQuasiFinite_of_formallyUnramified f`: a morphism of schemes
  `f : X ⟶ Y` that is formally unramified and locally of finite type is
  locally quasi-finite. Proof: all three properties are given by ring-map
  properties on affine opens (`HasRingHomProperty`). On each `f.appLE U V e`
  the formally unramified, finite type algebra is quasi-finite by Mathlib's
  instance in `Mathlib.RingTheory.Unramified.LocalStructure`, applied via
  `RingHom.quasiFinite_algebraMap`.
- `isHProjective_of_isFinite p`: for a commutative ring `R : Type u` and a
  finite morphism `p : X ⟶ Spec R`, `p` is
  `Langlands.AlgebraicGeometry.IsHProjective`, i.e. it factors as a closed
  immersion into the published projective space
  `Langlands.AlgebraicGeometry.ProjectiveSpace R n` followed by
  `projectiveSpaceToSpec R n`. Proof:
  1. `X` is affine (`isAffine_of_isAffineHom`), and `p` is
     `X.toSpecΓ ≫ Spec.map φ` for the finite ring map `φ : R → Γ(X, ⊤)`
     (Mathlib's `Scheme.Hom.finite_appTop`).
  2. Choose finitely many module generators of `Γ(X, ⊤)` over `R`, say `n`
     of them, and put `b = (1, generators) : Fin (n + 1) → Γ(X, ⊤)`. The
     published theorem
     `AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq` (from
     the Library's port of the Anthropic Fermat's Last Theorem source) gives
     an `R`-algebra map `θ` from the degree-zero localization of
     `MvPolynomial (Fin (n + 1)) R` at `X 0` that sends the ratio
     `X (k + 1) / X 0` to `b (k + 1)`. Hence `θ` is surjective, and
     `Spec.map θ` is a closed immersion
     (`IsClosedImmersion.spec_of_surjective`).
  3. Compose with the chart of index `0` of the published
     `ProjectiveSpace.affineOpenCover R n`. Its composite with
     `projectiveSpaceToSpec R n` is `Spec` of the structure map
     (`affineOpenCover_comp_toSpec`), so the composite `i` lies over `p`.
  4. `i` is finite, because `p` is finite and projective space is separated
     over `Spec R` (`isProper_π`, `IsFinite.of_comp`). It is a monomorphism,
     being a composite of a closed immersion, an open immersion and the
     isomorphism `X.toSpecΓ`. A finite monomorphism is a closed immersion
     (`IsClosedImmersion.iff_isFinite_and_mono`).

## Hypothesis

- `NeronHomExtension.{u}` (a `Prop`): take any base `S : Scheme.{u}`,
  actual abelian schemes `A B : Langlands.AbelianScheme S`, a discrete
  valuation ring `V : Type u` with fraction field `K : Type u`, and
  `t : Spec V ⟶ S`. Let `Spec K` lie over `S` through
  `Spec K ⟶ Spec V ⟶ S`. Then the published restriction
  `Langlands.GroupScheme.Cartier.restrict A.toCommGroupScheme B.toCommGroupScheme`
  along `Spec K ⟶ Spec V`, from relative homomorphisms `A_V ⟶ B_V` to
  relative homomorphisms `A_K ⟶ B_K`, is surjective. Classically this is
  part of the Néron mapping property of an abelian scheme over a discrete
  valuation ring. It is proved as `Langlands.AbelianScheme.neronHomExtension`
  in `Langlands.AbelianScheme.RelativeHomNeronExtension`, from the Néron
  mapping property in the Library's port of the Anthropic Fermat's Last
  Theorem formalisation.

## Lifts for valuative squares

Fix an actual `A : Langlands.AbelianScheme S`, `E : Over S` and a natural
isomorphism `β` from
`relativeHomFunctor A.toCommGroupScheme A.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}`
to `yoneda.obj E` on all of `Over S`.

- `hasLift_of_iso_yoneda A β hN sq hR`: every valuative square `sq` over
  `E.hom` whose valuation ring is a discrete valuation ring has a lift.
  Proof: consider `TV = Spec sq.R` and `TK = Spec sq.K` over `S`, the
  inclusion `jK : TK ⟶ TV`, and the top map `gK : TK ⟶ E` of the square.
  By `NeronHomExtension`, `β⁻¹ gK` is the restriction along `jK` of some
  `χ` over `TV`. Naturality of `β` gives `jK ≫ β χ = gK`. Hence the
  underlying morphism of `β χ : TV ⟶ E` is the lift: the upper triangle is
  this identity, and the lower one is `Over.w`.
- `hasLift_of_iso_yoneda_of_isClosed A β hN U hU sq hR`: the same holds for
  `(U.ι ≫ E.hom)`, if `U` is an open subset of `E.left` that is also
  closed. Proof: compose `sq` with `U.ι` and lift to `l : Spec sq.R ⟶ E.left`
  by the previous lemma. The image of `Spec sq.K` is dense in `Spec sq.R`,
  because `sq.R ⟶ sq.K` is injective
  (`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`). It lies in the
  closed set `l⁻¹ U`, so `l` lands in `U`. `IsOpenImmersion.lift` then
  factors `l` through `U.ι`.

## Main theorem

`relativeEndomorphismRepresentability_of_affineHomSchemePieces hP hN`,
for `hP : AffineHomSchemePiecesStatement.{u}` and
`hN : NeronHomExtension.{u}`, proves `RelativeEndomorphismRepresentabilityStatement.{u}`.

Proof. Take a noetherian ring `R` and an H-projective abelian scheme `A`
over `Spec R`. The interface `hP` gives a separated, locally finite type,
formally unramified `H` over `Spec R`, an isomorphism `α` on affine tests,
and closed open pieces `U i` that are quasi-compact over `Spec R`, pairwise
disjoint and covering. Then:

1. `Langlands.GroupScheme.Cartier.nonempty_iso_yoneda_of_affine α` (module
   `Langlands.AbelianScheme.RelativeEndomorphismAffineExtension`) extends `α`
   to an isomorphism `β` on all of `Over (Spec R)`. Whiskering `β` with the
   inclusion of locally noetherian test objects gives the required
   representation by `E = H`.
2. `H.left` is locally noetherian, because `H.hom` is locally of finite type
   over the noetherian `Spec R` (`LocallyOfFiniteType.isLocallyNoetherian`).
3. Each piece `P i = Over.mk ((U i).ι ≫ H.hom)` is H-projective:
   - It is universally closed by
     `Langlands.AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_hasLift`
     (`P i` is quasi-compact and locally of finite type over the noetherian
     `Spec R`), whose lift hypothesis is `hasLift_of_iso_yoneda_of_isClosed`. It is also separated and locally
     of finite type, hence proper.
   - It is locally quasi-finite by `locallyQuasiFinite_of_formallyUnramified`
     (open immersions are locally quasi-finite).
   - It is therefore finite by Mathlib's
     `IsFinite.of_isProper_of_locallyQuasiFinite`, and H-projective by
     `isHProjective_of_isFinite`.
4. Mathlib's `nonempty_isColimit_cofanMk_of`, applied to the covering,
   pairwise disjoint open immersions `(U i).ι`, makes
   `Sigma.desc (fun i => (U i).ι)` an isomorphism
   (`Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`). Its inverse is an
   isomorphism over `Spec R` from `H` to
   `Over.mk (Sigma.desc fun i => (P i).hom)`. Compatibility with the
   structure morphisms is checked on each coproduct inclusion
   (`Sigma.hom_ext`).
