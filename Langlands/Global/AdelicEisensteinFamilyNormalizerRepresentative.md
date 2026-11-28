# A normalizer representative matching the simple roots

Module `Langlands.Global.AdelicEisensteinFamilyNormalizerRepresentative` replaces an arbitrary
Weyl conjugation between standard parabolics by one given by a point of the normalizer of the
maximal split torus, as required by `StandardEisensteinFamilyComparisonStatement` (module
`Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement`).

## Statement

- `FamilyRegularComparison.exists_normalizerRepresentative fam I J hw hproj hKI hKJ`: let
  `(w, c)` be a Weyl conjugation from `P_I` to `P_J`, `proj` a Levi projection of `P_J`, and `K`
  with Iwasawa coverage for `P_I` and `P_J`. There are a rational point `n` of the normalizer of
  the maximal split torus (`normalizerPoints fam.i`) and `c' : M_J → M_I` such that `(n, c')` is
  a Weyl conjugation from `P_I` to `P_J`, the Weyl class of `n` maps the simple roots in `I`
  into `J`, its inverse maps those in `J` into `I`, and the family comparison (module
  `Langlands.Global.AdelicEisensteinFamilyRegularComparison`) for `(n, c')` implies the family
  comparison for `(w, c)`, both with the standard presentations.

  Here `I.val` and `J.val` are the standard index sets: the simple roots on which the standard
  cocharacters of `I` (resp. `J`) vanish, that is, the simple roots of the standard Levi
  subgroups `M_I` and `M_J`. They are not the roots `Δ_P` of the positive chamber, which come
  from the complementary simple roots.

## Proof of the main theorem

1. `weylTorusAlignment` (module `Langlands.Global.AdelicWeylTorusAlignment`), applied to the
   standard presentations of `P_I` and `P_J`, gives a rational point `z` of `M_I` and an
   automorphism `e` of the torus such that, for `n₀ = w · z`, conjugation by `n₀⁻¹` restricts
   to `e` on the torus:
   `fam.i ≫ (G.innerIso n₀⁻¹).hom = e.hom ≫ fam.i`. (The lemma states this as
   `fam.i ≫ (G.innerIso n₀).inv = e.hom ≫ fam.i`, and `innerIso_inv_hom` converts between the two
   forms.) So `n₀⁻¹` lies in the normalizer, with witness `CommGroupScheme.isoOfGroupIso e`, and
   since the normalizer is closed under inversion, `n₀` lies in it too. Then
   `(n₀, c ≫ Int(z)⁻¹)` is a Weyl conjugation (`IsWeylConjugation.mul_right_levi`).
2. `standardWeylRepresentative` (module `Langlands.Global.AdelicStandardWeylRepresentative`),
   with `I` and `J` written as root sets of finite sets of simple-root labels
   (`StandardParabolicFamily.exists_rootSet_eq`, module `Langlands.Global.AdelicStandardWeylSteps`,
   using that the simple roots are finite by `finite_simpleRelativeRoots`), gives a rational point `z'` of
   `M_I` and a normalizer point `n' = n₀ · z'` whose Weyl class maps the simple roots of `I` into
   `J` and whose inverse maps those of `J` into `I`. Put
   `c' = (c ≫ Int(z)⁻¹) ≫ Int(z')⁻¹`; `(n', c')` is a Weyl conjugation by `mul_right_levi`.
3. Right multiplication by rational Levi points does not change the parameter map
   (`weylParameter_comp_innerIso_inv`, module
   `Langlands.Global.AdelicIntertwiningRightLeviRepresentative`), so
   `weylParameter l_I c proj = weylParameter l_I c' proj`.
   `FamilyRegularComparison.of_weylRepresentative` (module
   `Langlands.Global.AdelicEisensteinFamilyWeylRepresentative`) concludes.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. §2.1, p. 190 defines `W(P, Q)` as
the set of cosets `w M_P(F)`, `w ∈ G(F)`, with `w M_P w⁻¹ = M_Q`. §6.1, p. 200 defines the set
`Δ₀ᴾ` of simple roots of the maximal split torus on `U₀ ∩ M_P` (the simple roots of the Levi
subgroup), and the chamber roots `Δ_P` as the projections of the complementary simple roots
`Δ₀ \ Δ₀ᴾ`. In §6.7, pp. 206–207, `W(P, Q)` is identified with the standard representatives
`w ∈ ᑫWᴾ` with `w M_P w⁻¹ = M_Q`, and each such `w` carries `Δ₀ᴾ` bijectively onto `Δ₀ᑫ`. In the
theorem above, `I.val` and `J.val` play the roles of `Δ₀ᴾ` and `Δ₀ᑫ`. The theorem produces a
representative with this property for an arbitrary Weyl conjugation in the Library's sense.
