# Finite and finite étale morphisms through full-recognition pair systems

Author: Worker 36.

This module defines Berkovich's finite morphisms, finiteness at a point, and
quasifinite morphisms. It also defines a finite étale variant. All of these are
stated for strong maps of local-domain enlargements, through their pair systems
on the two full recognition atlases from `FullRecognitionPairSystems`. It proves
the identity and composition laws, the latter through the composition law of
`FullRecognitionPairComposition`.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Lemma 1.3.7 and the following definition, printed pp.27–28 / PDF pp.24–25.
  A morphism `φ : Y → X` is *finite* if, for any Φ-affinoid domain `V ⊂ X`,
  `φ⁻¹(V) → V` is a finite morphism of k-affinoid spaces (condition b);
- Definition 1.3.1, printed p.23 / PDF p.20: the affinoid domains of an
  analytic domain are the affinoid domains of `X` contained in it;
- Definition 3.1.1, printed p.54 / PDF p.51. `φ` is *finite at a point* `y` if
  there exist open neighborhoods `𝒱` of `y` and `𝒲` of `φ(y)` such that `φ`
  induces a finite morphism `𝒱 → 𝒲`; `φ` is *quasifinite* if it is finite at
  every point;
- Definition 3.3.4, printed p.63 / PDF p.60, for comparison of scope only. A
  quasifinite morphism is étale if it is unramified (`Ω_{Y/X} = 0`) and flat in
  the sense of Definition 3.2.5, which uses local rings.

The notion of a finite morphism of k-affinoid spaces is Berkovich's 1990
convention, which the 1993 paper uses. The 1990 source is Berkovich, *Spectral
theory and analytic geometry over non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`, with
PDF SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The relevant passages are:

- §1.1, printed p.11 / PDF p.25: a bounded homomorphism is admissible when the
  residue (quotient) norm on its image is equivalent to the given norm;
- printed p.24 / PDF p.38: a Banach module `M` over an affinoid algebra `𝒜` is
  *finite* if there is an admissible epimorphism `𝒜ⁿ → M`. The same page shows
  that a Banach module finite as an abstract module need not be a finite Banach
  module. For a trivially valued `k` and `0 < p < q < 1`, the canonical map
  `k{q⁻¹T} → k{p⁻¹T}` is bijective, but its inverse is unbounded;
- printed p.25 / PDF p.39: a commutative Banach `𝒜`-algebra is *finite* if it
  is a finite Banach `𝒜`-module;
- Corollary 2.3.2(i) and the following definition, printed p.33 / PDF p.47: a
  morphism `𝓜(ℬ) → 𝓜(𝒜)` of k-affinoid spaces is *finite* when `ℬ` is a
  finite Banach `𝒜`-module.

The finite and quasifinite definitions here transcribe Lemma 1.3.7(b) and
Definition 3.1.1 for the constructed affinoid domains, the recognized subsets
of the full recognition atlases. The affinoid maps are required to be finite
Banach algebra maps in the 1990 sense, not merely finite ring maps. The finite
étale variants are derived notions: they additionally require algebraic
étaleness of the affinoid maps. They are **not** claimed to be Berkovich's étale morphisms
of Definition 3.3.4. That definition requires flatness at local rings and the
vanishing of the sheaf of differentials, and its comparison with these
variants is not proved here.

## Finite Banach algebra maps

For normed commutative algebras `R`, `S` over a normed field `K` and
`f : BoundedAlgHom K R S`, the published `f.coefficientMap b` sends
`c : Fin n → R` to `∑ i, f (c i) * b i`. It is a continuous `K`-linear map,
hence bounded, from the finite free module `Fin n → R` with its maximum norm.
It is `R`-linear for the module structure on `S` given by `f`.

`BoundedAlgHom.IsFiniteBanach f` asks for `n`, a tuple `b : Fin n → S` and a
constant `C > 0` such that every `y : S` has coefficients `c` with
`f.coefficientMap b c = y` and `‖c‖ ≤ C * ‖y‖`. Such a coefficient map is
surjective, and the lifting bound bounds the residue norm of every `y` by
`C * ‖y‖`. Boundedness of the coefficient map gives the reverse comparison up
to a constant. So this is exactly the existence of an admissible epimorphism
`Rⁿ → S`, that is, a finite Banach algebra in the 1990 sense. No completeness,
open mapping theorem or nontrivial valuation is used.

- `IsFiniteBanach.finite` shows that a finite Banach algebra map is finite as
  a ring map, by the published `finite_iff_exists_surjective_coefficientMap`.
  The converse fails in general, by the source counterexample above.
- `isFiniteBanach_id` uses the single generator `1` and the constant `1`.
- `IsFiniteBanach.comp` composes finite Banach maps `R → S → T`. It uses the
  products `g (b i) * d j` of the two generating tuples, indexed through
  `finProdFinEquiv`, and the product of the two lifting constants. A target
  element lifts first through the second coefficient map. Each resulting
  coefficient then lifts through the first one, and the maximum-norm estimates
  multiply.

## Definitions

Let `A`, `B` be presentations in universes `u,v,w` and
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`. Write `P` for
`g.fullRecognitionPairs`. Its bounded maps are defined on pairs of recognized
subsets `V'` of `A.atlas.saturatedAtlas` and `W` of `B.atlas.saturatedAtlas`
with `g(V') ⊆ W`.

`IsFiniteOver g V U`, for subsets `V` of `A.space` and `U` of `B.space`, means
that `g.baseMap '' V ⊆ U` and the following holds for every recognized subset
`W` with `W.locus ⊆ U`. There is a recognized subset `V'` of the source with
`V'.locus = V ∩ g.baseMap ⁻¹' W.locus`, admissible for `W`, whose bounded map
`P.pullback V' W` satisfies `IsFiniteBanach`. Thus the preimage of every
affinoid domain of `U` in `V` is an affinoid domain, and the induced morphism
of affinoid spaces is finite in Berkovich's sense. A recognized subset is
determined by its locus, so `V'` is unique.

`IsFiniteEtaleOver g V U` is the same condition where the bounded map
satisfies both `IsFiniteBanach` and the published
`BoundedAlgHom.AlgebraicallyFiniteEtale`, the conjunction of Mathlib's
`RingHom.Finite` and `RingHom.Etale`.

- `IsFinite g` is `IsFiniteOver g univ univ`, which is Lemma 1.3.7(b).
- `IsFiniteEtale g` is `IsFiniteEtaleOver g univ univ`.
- `IsFiniteAt g y` asks for open `V ∋ y` and open `U` with
  `IsFiniteOver g V U`. The image of `y` lies in `U` because `g(V) ⊆ U`.
- `IsQuasifinite g` asks for `IsFiniteAt g y` at every point `y`, which is
  Definition 3.1.1.
- `IsLocallyFiniteEtaleAt g y` is the corresponding open-neighborhood
  condition for `IsFiniteEtaleOver`.

## Basic relations

`IsFiniteEtaleOver.isFiniteOver` forgets the étale conjunct, and
`IsFiniteEtale.isFinite` specializes it. `IsFinite.isFiniteAt` uses the open sets `univ`, so finite maps
are quasifinite (`IsFinite.isQuasifinite`). `IsLocallyFiniteEtaleAt.isFiniteAt`
forgets étaleness at a point.

## Identity

`AdmissiblePairSystem.pullback_congr` transports bounded maps along an equality
of pair systems. `fullRecognitionPairs_id_pullback_self` combines it with the
identity law `fullRecognitionPairs_id`. Together with `restriction_self`, it
shows that the identity of the local-domain enlargement has the identity bounded
map on every pair `W`, `W`.

For every subset `V`, `isFiniteEtaleOver_id` proves the condition for the
identity from `V` to `V`. For `W ⊆ V`, the preimage is `W` itself. The
identity bounded map is a finite Banach map by `isFiniteBanach_id` and is
algebraically finite étale by the published `algebraicallyFiniteEtale_id`. `isFiniteOver_id`, `isFiniteEtale_id` and
`isFinite_id` follow.

## Composition

Let `g' : StrongHom B.saturatedPresentation C.saturatedPresentation`, and write
`gg'` for the saturated composite. `IsFiniteOver.comp` proves that
`IsFiniteOver g V U` and `IsFiniteOver g' U T` imply
`IsFiniteOver gg' V T`.

- The image condition is the composite of the two image conditions.
- For a recognized `W ⊆ T`, the second hypothesis gives `V1` with
  `V1.locus = U ∩ g'⁻¹(W)`, which lies in `U`.
- The first hypothesis then gives `V2` with `V2.locus = V ∩ g⁻¹(V1.locus)`.
  Since `g(V) ⊆ U`, this is `V ∩ gg'⁻¹(W)`.
- The pair `(V2, W)` is admissible for `gg'`. By `fullRecognitionPairs_comp`,
  its bounded map is the composite of the maps of `g` on `(V2, V1)` and of `g'`
  on `(V1, W)`. `IsFiniteBanach.comp` gives finite Banach finiteness.

`IsFiniteEtaleOver.comp` is the same argument, using `IsFiniteBanach.comp` and
the published `AlgebraicallyFiniteEtale.comp`. `IsFinite.comp` and `IsFiniteEtale.comp` are the
global cases.

## Scope

These notions are defined for strong maps of the constructed local-domain
enlargements. Their extension to arbitrary morphisms of the localized category,
which are fractions with quasi-isomorphisms, is not constructed here. Nor are
Berkovich's Lemma 3.1.2 on shrinking neighborhoods, composition of quasifinite
morphisms (Corollary 3.1.3), base change, flatness at local rings,
unramifiedness, or the étale morphisms of Definition 3.3.4. The analytic étale
and quasi-étale sites and the Harris specializations also remain further work.
