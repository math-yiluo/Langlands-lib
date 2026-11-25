# Proof of the parahoric contraction statement (contraction clause of KP 13.6.4)

This module proves the published target
`Langlands.Geometry.Building.ParahoricContractionInApartmentStatement` of
`Langlands/Geometry/Building/KPParahoricContractionStatement.lean`. The theorem
`Langlands.Geometry.Building.parahoricContractionInApartment` is stated at an arbitrary
universe `u`. Its type is exactly `ParahoricContractionInApartmentStatement.{u}`, so no
hypothesis is changed or added. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Take a nonarchimedean local field `F` and an affine group scheme `G` over `F` with
`P : ParahoricBuildingData G` satisfying `P.SatisfiesApartmentAxioms`. Let `c` be a point of
the apartment on no affine root hyperplane, and let `x` lie in the closed facet
`AffineRootSystem.facetClosure P.affineRoots c`. Suppose `X : GenericLie 𝒪[F] G` is contracted
by some `F`-cocharacter `λ : 𝔾ₘ → G`, i.e. `X ∈ 𝔤_{>0}(λ)`. Then there are
`p ∈ P.parahoricAt x` and a cocharacter `ν` of the apartment torus `P.S` with
`Ad(p) X ∈ 𝔤_{>0}(ν)` for the cocharacter `𝔾ₘ → P.S → G` given by `ν` and `P.i`. Here `Ad` is
the published `GenericLie.adjoint`, `𝔤_{>0}` is the published `cocharacterPositiveLie`, and
`P.parahoricAt x = P.parahoric {x}` is the connected parahoric of the supplied data.

## Auxiliary lemmas

The file proves four lemmas, all over a field `k` and an affine group scheme `G` over `k`.

* `cocharacterPositiveLie_eq_iSup_succ`. For `ν : 𝔾ₘ → G`, the space `cocharacterPositiveLie ν`
  equals `⨆ n : ℕ, weightSpace ν (Gm.powerHom _ (n + 1))`. It is defined as the supremum of
  the weight spaces for the characters `n • 𝟙` with `0 < n`, and these are the power characters
  `t ↦ t^n`. The proof reindexes the supremum by `n ↦ n - 1`.
* `constantPoint_eq_sectionsCoeffEquiv`. For a rational point `g` of `G`, the constant point
  of `g` on the test algebra `k` equals `AffineWeil.sectionsCoeffEquiv k G g`. Both have
  underlying morphism `g.left` after the identity of `Spec k`.
* `adjoint_mem_cocharacterPositiveLie_innerIso`. If `GenericLie.equiv R G Y ∈ 𝔤_{>0}(ν)` and
  `h ∈ G(k)`, then `GenericLie.equiv R G (GenericLie.adjoint R h Y) ∈ 𝔤_{>0}(ν ≫ int(h))`.
  Here `int(h) = (G.innerIso h).hom` is conjugation by `h`. By `GenericLie.adjoint_apply`
  and the previous lemma, the adjoint action is `Lie.targetMapLinear (G.innerIso h).hom k`
  (`Lie.targetMapLinear_innerIso`). Postcomposition with `int(h)` carries each weight space of
  `ν` into the weight space of `ν ≫ int(h)` for the same character
  (`lieKernelHomLinear_mem_weightSpace`). Taking suprema with the previous description of
  `𝔤_{>0}` gives the claim.
* `adjoint_mem_cocharacterPositiveLie_of_mem_parabolic`. Assume that `G` is locally of finite
  type over `k` (the instance `LocallyOfFiniteType G.X.hom`). If `h ∈ G(k)` lies in the
  dynamic parabolic `P(ν)`, then `Ad(h)` preserves `𝔤_{>0}(ν)`. The main theorem does not
  add this assumption as a hypothesis: there it follows from the smoothness of the connected
  reductive group `G`. The published `dynamicLie`
  identifies `⨆ n, weightSpace ν (t ↦ t^{n+1})` with the tangent vectors that lie in the
  dynamic unipotent `U(ν)`. Then `Dynamic.conj_mem_unipotent` shows that conjugation by a
  point of `P(ν)` preserves `U(ν)`. The constant point of `h` on the dual numbers is a
  pullback of `h`, so it lies in `P(ν)` by two applications of `comp_mem`.

## The main proof

Let `λ` be the contracting cocharacter of `X`. Since `G` is connected reductive
(`P.isConnectedReductive`), `G` is smooth and `P.S` is a split torus. Choose a generic
cocharacter `ν₀` of `P.S` (`IsSplitTorus.exists_genericCocharacter`).

1. **Standard conjugate.** The theorem `exists_innerIso_comp_eq_standardCocharacter` gives
   `g ∈ G(F)`, a set `J` and a standard cocharacter `ζ` of `P.S` for `(ν₀, J)` with
   `λ ≫ int(g) = ζ ≫ P.i`. Its inputs are the published theorems
   `smoothMaximalSplitTorusConjugacy` and `relativeRootSystem`. By
   `adjoint_mem_cocharacterPositiveLie_innerIso`, `Ad(g) X ∈ 𝔤_{>0}(ζ ≫ P.i)`.
2. **Iwasawa decomposition.** The facet of `c` is a chamber, because `c` lies on no affine
   root hyperplane. The published `iwasawaDecomposition` uses `henselianLocalRing_integer`,
   the perfect residue field, `P.SatisfiesApartmentAxioms` and the generic `ν₀`. It writes
   `g = u * n * p` with `u ∈ standardUnipotentPoints P.i ν₀ ∅`, `n` a point of the normalizer
   of `P.S`, and `p ∈ P.parahoric (facet c)`.
3. **`p ∈ P_x`.** The facet of `c` contains `c`, so `parahoric_anti` gives
   `P.parahoric (facet c) ≤ P.parahoric {c}`. By definition, `P.parahoric Ω` is the supremum
   of a fixed factor and the sharp fixer `P.sharpFixer Ω`. The fixed factor does not depend on
   `Ω`. It is the image of the Iwahori subgroup `P.centralizerZero = Z(F)^0` of `Z(F)` under
   `P.centralizer.j`, where `Z = Z_G(P.S)` (KP Definition 7.4.1(4)). It is not the image of
   all of `Z(F)`. Since `x` is in the closed facet of `c`,
   `sharpFixer_singleton_le_of_mem_facetClosure` gives `sharpFixer {c} ≤ sharpFixer {x}`.
   Its axiom AS4 input is the field `hP.mem_or_two_smul_mem`. Taking the supremum of both
   sides with the same fixed factor (`sup_le_sup_left`) gives
   `P.parahoric {c} ≤ P.parahoric {x}`. Hence `p ∈ P.parahoric {x} = P.parahoricAt x`.
4. **`u⁻¹` preserves the contraction.** `u` lies in the standard parabolic
   `standardParabolic P.i ν₀ ∅` (`standardUnipotent_le_standardParabolic`). That subgroup lies
   in the dynamic parabolic `P(ν₀ ≫ P.i)` (`standardParabolic_empty_le`). Every relative root
   pairs nonzero with the generic `ν₀`. So a root with `0 ≤ ⟨α, ν₀⟩` is positive, and the
   standard `ζ` pairs nonnegatively with it (`IsStandardCocharacter.pairing_nonneg_of_positive`).
   By the parabolic clause of `relativeRootSignInclusions`, `P(ν₀ ≫ P.i) ≤ P(ζ ≫ P.i)`. Thus
   `u⁻¹ ∈ P(ζ ≫ P.i)`, and `adjoint_mem_cocharacterPositiveLie_of_mem_parabolic` gives
   `Ad(u⁻¹ g) X ∈ 𝔤_{>0}(ζ ≫ P.i)`.
5. **Transport by `n⁻¹`.** By `adjoint_mem_cocharacterPositiveLie_innerIso` with `h = n⁻¹`,
   `Ad(n⁻¹ u⁻¹ g) X ∈ 𝔤_{>0}((ζ ≫ P.i) ≫ int(n⁻¹))`. The published
   `groupHom_cocharacterAut_comp` rewrites this cocharacter as `ν ≫ P.i`, where
   `ν = cocharacterAut (normalizingAut P.i n⁻¹) ζ`. This is the conjugate of `ζ` under the
   Weyl action of `n⁻¹`.

Finally `p = n⁻¹ * u⁻¹ * g` by `g = u * n * p`, and `GenericLie.adjoint_mul` gives
`Ad(p) X = Ad(n⁻¹) (Ad(u⁻¹) (Ad(g) X))`. So the witnesses are `p` and `ν`.

## Relation to the literature

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023), Proposition 13.6.4,
printed p. 480 / PDF p. 511, contains the contraction clause. KP prove it with integral models.
This proof follows instead a group-scheme route. It uses the
rational conjugacy of maximal split tori and the Iwasawa decomposition
`G(F) = U_∅(F) N(F) P_C` for the chamber `C` of `c` (KP 5.3.3). It also uses the fact that
the minimal parabolic `P_∅` normalizes `𝔤_{>0}` of a dominant cocharacter. The proof does not
give the parts of KP 13.6.4 that the target omits: compatibility with the integral model at
`x`, and the dominance inequalities on `Δₓ`.
