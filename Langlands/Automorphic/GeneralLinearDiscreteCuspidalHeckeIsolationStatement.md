# Discrete automorphic representations of `GL_n` with the Hecke eigenvalues of a cuspidal one

Module `Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement`, namespace
`Langlands.Automorphic.DiscreteHeckeIsolation`. It makes five definitions and states one
proposition, `GeneralLinearDiscreteCuspidalHeckeIsolationStatement`. It contains no proof.

In words: let `S` be a cuspidal automorphic representation of `GL_{r+1}` over a number field `F`,
trivial on the positive split centre, and let `Π` be an irreducible closed invariant subspace of
`L²([GL_{r+1}])`. If at almost every finite place `p` the spherical Hecke algebra of
`GL_{r+1}(F_p)` acts on nonzero spherical vectors of `Π` and of `S` by the same character, then
`Π` is the closure `V_S` of the `L²` classes of the forms of `S`. This is strong multiplicity one
for the discrete spectrum relative to a cuspidal representation, together with multiplicity one.

## Library notation

Throughout, `F : Type` is a number field, `r : ℕ`, and

* `GLG = GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)` is the group
  scheme `GL_{r+1}` over `F`, and `hG = isConnectedReductive_generalLinear F (Fin (r + 1))` is the
  published proof that it is connected reductive. The module declares local instances `IsAffine`
  (from `GroupScheme.GeneralLinear.isAffine_groupScheme`) and `LocallyOfFiniteType` (from the
  smoothness contained in `hG`), and the `AddCommGroup` structures on the Library's spaces of
  functions on `GL_n(𝔸_F)` and on the spaces of operator realizations, as the modules it imports do.
* `[G] = RestrictionSplitCentre.CanonicalQuotient F GLG` is the Library's canonical quotient
  `A_G GL_{r+1}(F) \ GL_{r+1}(𝔸_F)`, where `A_G` is the group of positive real points of the chosen
  split component of the Weil restriction `Res_{F/ℚ} GL_{r+1}`
  (`Langlands/Global/AdelicRestrictionSplitCentreCanonical.lean`). It carries the measure
  `RestrictionSplitCentre.canonicalMeasure F GLG`, and `L²([G])` is
  `Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F GLG)`.
* `R = RestrictionSplitCentre.canonicalL2RightAction F GLG centralSplitTorusCharacter hG` is the
  right regular representation of `GL_{r+1}(𝔸_F) = AdelicGroupPoints F GLG` on `L²([G])`. Here
  `centralSplitTorusCharacter` is the published proof of `CentralSplitTorusCharacterStatement`;
  the representation does not depend on which proofs are supplied. The discrete spectrum
  `AdelicGroupPoints.discreteSpectrum F GLG hG` is `Langlands.Analysis.discretePart R`, the closure
  of the sum of all `V` with `Langlands.Analysis.IsIrreducibleSubrepresentation R V`.
* `FiniteLocalGL F (r + 1) p = GL_{r+1}(F_p)` in the matrix model, for a finite place `p`.
  `CompletionPadic.padicField p` is the completion `F_p` as a `PadicField`. Following
  `Langlands/Automorphic/LocalSphericalHecke.lean`, the module gives `GL_{r+1}(F_p)` the canonical
  topology of `GL_{r+1}` over that field (equal to the default topology of `FiniteLocalGL` by
  `FiniteAdelicGL.localGL_topology_eq`), its Borel σ-algebra and the Haar measure
  `Unramified.sphericalHaar (padicField p) r`, which gives `GL_{r+1}(𝒪_p)` mass one.
* `K_p = Correspondence.sphericalSubgroup (padicField p) r` is `GL_{r+1}(𝒪_p)`, and
  `Unramified.sphericalOpenSubgroup (padicField p) r` is the same subgroup as an open compact
  subgroup. `Unramified.SphericalHeckeAlgebra (padicField p) r` is the spherical Hecke algebra
  `C_c^∞(GL_{r+1}(F_p) // GL_{r+1}(𝒪_p))`: the Library's corner `Hecke.HeckeAlgebra.Corner` of
  bi-`K_p`-invariant functions, with convolution for `sphericalHaar`. Its unit is the normalized
  characteristic function of `K_p`.
* `S : CuspidalOperatorRealization F r` is a cuspidal realization of `GL_{r+1}`: an irreducible
  space `S.Space` of cusp forms on `GL_{r+1}(𝔸_F)` in the matrix model, invariant under the finite
  adelic group, the standard maximal compact subgroup at the infinite places and the enveloping
  algebra (`Langlands/Automorphic/CuspidalOperatorRealization.lean`).
  `S.realization.toContinuous f` is the continuous function of a form `f`, and
  `S.realization.localRepresentation p` is the action of `GL_{r+1}(F_p)` on `S.Space` by right
  translation at `p` (`Langlands/Automorphic/OperatorLocalRestriction.lean`).
* `CuspidalPairPoles.IsTrivialOnSplitCentre S` says that every form of `S` is invariant under the
  scalar matrices `a I` for which the idele `a` has finite component `1` and the same positive real
  component at every infinite place. These scalar matrices form `A_G`: the published
  `GeneralLinearGroupPoints.mem_splitCentre_iff` identifies the canonical split centre of `GLG`,
  transported to the matrix model, with `AdelicGL.splitCentre F (r + 1)`, the scalar matrices of
  the positive real ideles (finite component `1`, one positive real at all infinite places).

## The definitions

### `smoothSphericalHeckeAction σ`

For any representation `σ` of `GL_{r+1}(F_p)` on a complex vector space `V`, this is the algebra
homomorphism

`Unramified.SphericalHeckeAlgebra (padicField p) r →ₐ[ℂ] Module.End ℂ (fixedVectors (smoothPart σ) K_p)`

given by the Library's `Hecke.cornerAction` for the smooth representation `smoothPart σ` (the
vectors of `V` fixed by some open subgroup; `isSmooth_smoothPart` shows it is smooth), the measure
`sphericalHaar` and the open compact subgroup `sphericalOpenSubgroup`. A vector fixed by the open
subgroup `K_p` is smooth, so `fixedVectors (smoothPart σ) K_p` is the space of `K_p`-fixed vectors
of `σ` (the Library's `smoothPartFixedVectorsEquiv`). On such a vector `x` an element `h` acts as
`∫ h(g) σ(g) x dg`; since `h` is bi-`K_p`-invariant with compact support, this is a finite
weighted sum of translates `σ(g_i) x`. For a unitary representation it is the usual integrated
action. For a smooth `σ`, `smoothPart σ` is all of `σ` (`smoothEquiv`), and the action is the one
of `Hecke.cornerAction` on `σ` itself, as in `LocalRealization.sphericalHeckeAction`.

### `HasSphericalHeckeCharacterOn σ W χ`

For `σ` as above, a subspace `W ≤ V` and an algebra homomorphism
`χ : Unramified.SphericalHeckeAlgebra (padicField p) r →ₐ[ℂ] ℂ`, this says:

* some nonzero vector of `W` is fixed by `GL_{r+1}(𝒪_p)`; and
* for every `h` in the spherical Hecke algebra and every vector `x` of `W` fixed by
  `GL_{r+1}(𝒪_p)`, `smoothSphericalHeckeAction σ h x = χ h • x`.

That is, `W` has nonzero spherical vectors at `p`, and the spherical Hecke algebra acts on all of
them by the character `χ`.

### `canonicalL2LocalAction F r p`

The restriction of `R` to `GL_{r+1}(F_p)` in the matrix model. A matrix `g` is sent to the point of
`GLG` over the completion `F_p` with matrix `g` (the inverse of the Library's
`GroupScheme.GeneralLinear.affinePointsEquiv` for `placeCompletion F (.inr p)`), this point is
inserted at the place `p` with identity components elsewhere (`AdelicGroupPoints.ofPlace`), and
`R` is applied.

### `IsCanonicalGeneralLinearFormClass F r φ f`

For `φ ∈ L²([G])` and a continuous function `f : ContinuousRationalFunctions F (r + 1)` on
`GL_{r+1}(𝔸_F)` in the matrix model, this says that `φ` is the `L²` class of `f`. It reuses two
Library identifications:

* `RestrictionSplitCentre.canonicalL2Equiv F GLG` identifies `L²` of the positive quotient of the
  chosen split component `canonicalComponent F GLG : canonicalTorus F GLG → GLG` with `L²([G])`, by
  composition with the identity map on representatives. The two quotients are the same quotient of
  `GL_{r+1}(𝔸_F)`, because the positive image of that split component is `A_G`
  (`canonicalSubgroup_eq_imageSubgroup`).
* `IsGeneralLinearFormClass` (`Langlands/Automorphic/GeneralLinearCuspidalSummandRealizationStatement.lean`)
  says that a class on that positive quotient is the class of `f`. There is a continuous function
  `h` on the quotient whose pullback to `GL_{r+1}(𝔸_F)`, transported to the matrix model by
  `continuousGeneralLinearEquiv`, is `f`, and the class agrees with `h` almost everywhere.

So `IsCanonicalGeneralLinearFormClass F r φ f` holds when `f` is left invariant under `A_G` and the
rational points, descends to a continuous function `h` on `[G]`, and `φ` is the class of `h`.
For a given `f` such a `φ` is unique: `h` is determined by `f`, because the quotient map is
surjective, and `φ` corresponds to the class of `h`.

### `cuspidalRealizationClosure F r S`

The subspace `V_S` of `L²([G])`: the closure of the span of all `φ` with
`IsCanonicalGeneralLinearFormClass F r φ (S.realization.toContinuous f)` for some form `f` of `S`.
When every form of `S` has a class, as the statement asserts, the span is just the set of classes,
since the class map is linear.

## The statement

`GeneralLinearDiscreteCuspidalHeckeIsolationStatement` says: for

* every number field `F : Type` whose adele quotient is compact (an instance argument, which
  `CuspidalOperatorRealization` requires), every `r : ℕ`, and every cuspidal realization
  `S : CuspidalOperatorRealization F r` with `CuspidalPairPoles.IsTrivialOnSplitCentre S`;
* every subspace `P` of `L²([G])` with `Langlands.Analysis.IsIrreducibleSubrepresentation R P`:
  `P` is closed, nonzero and invariant under `GL_{r+1}(𝔸_F)`, and every closed invariant subspace
  of `L²([G])` contained in `P` is `0` or `P`; the Markdown writes `Π` for `P`;
* every finite set `E` of finite places such that for every finite place `p ∉ E` there is a
  character `χ` of `Unramified.SphericalHeckeAlgebra (padicField p) r` with
  `HasSphericalHeckeCharacterOn (canonicalL2LocalAction F r p) P χ` and
  `HasSphericalHeckeCharacterOn (S.realization.localRepresentation p) ⊤ χ`,

the following two conclusions hold.

1. Every form `f` of `S` has an `L²` class on `[G]`: there is `φ` with
   `IsCanonicalGeneralLinearFormClass F r φ (S.realization.toContinuous f)`.
2. `P = cuspidalRealizationClosure F r S`, that is, `Π = V_S`.

The hypothesis at `p` says: `Π` and `S` both have nonzero vectors fixed by `GL_{r+1}(𝒪_p)`, and
the spherical Hecke algebra acts on all of these vectors, in `Π` and in `S`, through the same
character `χ`. Nothing is assumed at the places of `E` or at the infinite places, and `Π` is not
assumed to be cuspidal.

Conclusion 1 does not depend on `Π`. It makes `V_S` the closure of the classes of all the forms of
`S`, not only of those forms that happen to have a class. It holds because the forms of `S` are
cusp forms invariant under `A_G`. Such forms are rapidly decreasing on Siegel domains, hence
bounded (Getz–Hahn, Theorem 9.7.1), and `[G]` has finite volume, so the descended functions are
square integrable.

### Consequences

When some `Π` satisfies the hypotheses, the statement gives: `V_S = Π` is irreducible, and it lies
in `L²_disc([G]) = discreteSpectrum F GLG hG`, because `discreteSpectrum` is the closure of the sum
of all irreducible subrepresentations of `R`. Any two subspaces `Π`, `Π'` satisfying the
hypotheses, with possibly different finite sets `E`, `E'`, are equal, since both are `V_S`. So `V_S`
occurs in `L²_disc([G])` with multiplicity one, and no other irreducible closed invariant subspace,
cuspidal or residual, carries the Hecke eigenvalues of `S` at almost all places.

## The local condition: Hecke characters, and the equivalent embedding form

The statement uses the Hecke form of the local condition. A common alternative, used by
`IsobaricStrongMultiplicityOneStatement`, is the embedding form: one irreducible unramified
representation `A` of `GL_{r+1}(F_p)` has injective intertwining maps into the restrictions of
`Π` and of `S` to `GL_{r+1}(F_p)`. For irreducible `Π` and `S` the two forms are equivalent at
each place `p`, by the following standard arguments. This module does not formalize them.

* **Factorization.** `S.Space` is an irreducible admissible representation, so its restriction to
  `GL_{r+1}(F_p)` is a direct sum of copies of the local component `S_p` (Getz–Hahn, Theorems 5.7.1
  and 5.7.2, p. 152). Likewise `Π`, an irreducible unitary representation of
  `GL_{r+1}(F_p) × GL_{r+1}(𝔸_F^p)`, is a completed tensor product `Π_p ⊗̂ Π^p`, because
  `GL_{r+1}(F_p)` is of type I (Getz–Hahn, Theorem 3.10.2, p. 97), and its restriction to
  `GL_{r+1}(F_p)` is a multiple of the irreducible unitary representation `Π_p`. Hence the
  `K_p`-fixed vectors of `Π` are `Π_p^{K_p} ⊗̂ Π^p`, those of `S` are `S_p^{K_p} ⊗ S^p`, and when they
  are nonzero the spherical Hecke algebra acts on them by the Hecke character of the unramified
  representation `Π_p`, resp. `S_p` (the `K_p`-fixed space of an unramified representation is a
  line).
* **Hecke form ⇒ embedding form.** If both fixed spaces are nonzero with the same character `χ`,
  then the smooth vectors of `Π_p` and the representation `S_p` are irreducible unramified with
  Hecke character `χ`, hence isomorphic (Getz–Hahn, Proposition 7.1.2, p. 184). Call this
  representation `A`. It embeds into `S` as `S_p ⊗ s` and into `Π` as `Π_p^∞ ⊗ w`, for nonzero `s`
  and `w`.
* **Embedding form ⇒ Hecke form.** If an irreducible `A` with `A^{K_p} ≠ 0` embeds into both
  restrictions, then by the factorization `A ≅ S_p` and `A ≅ Π_p^∞`. So both fixed spaces are
  nonzero, and the spherical Hecke algebra acts on both by the Hecke character of `A`.

The Hecke form is the one a trace-formula argument produces after separating Hecke eigencharacters
at the unramified places. It also needs no choice of the representation `A`.

## Why the statement is true

The following proof route uses results that the Library states, as named below, and the theorem of
Mœglin–Waldspurger, which this module does not state.

1. `Π` lies in `L²_disc([G])`, by the definition of `discreteSpectrum` recalled above. By Langlands'
   spectral decomposition (Getz–Hahn, Theorem 10.5.1, p. 282; the Library's
   `SpectralDecompositionStatement`), `L²_disc([G])` is the part of `L²([G])` attached to the
   association class of `G` itself.
2. By Mœglin–Waldspurger (*Le spectre résiduel de `GL(n)`*, Théorème, p. 606; Getz–Hahn,
   Theorem 10.8.1, p. 290), `Π` is isomorphic to a Speh representation `(σ, m)` with `md = r + 1`
   and `σ` a cuspidal representation of `GL_d`, trivial on `A_{GL_d}`. If `m = 1`, `Π` is cuspidal.
3. At almost every finite place `p`, the unramified component of `(σ, m)` is the unramified
   constituent of the representation induced from `σ_p |·|^{(m-1)/2} ⊗ ⋯ ⊗ σ_p |·|^{(1-m)/2}`
   (Getz–Hahn, p. 290: `(σ, m) = ⊞_i σ ⊗ |·|^{(m+1)/2 - i}`). If `m ≥ 2`, this pair of a parabolic
   subgroup with `m` blocks and a cuspidal datum is not associate to `(S, GL_{r+1})`, so by
   Jacquet–Shalika (*Euler products II*, Theorem 4.4, p. 809) its unramified components cannot be
   those of `S` at almost every place. The hypothesis, read in the embedding form above, says that
   they are. So `m = 1`. The Library's numerical form of this step is
   `Langlands.Automorphic.Unramified.CuspidalEulerConstituentRecoveryStatement`, with its
   consequences in `Langlands.TraceFormula.CuspidalHeckeFamilyIsolation`, for example
   `HeckeIsolation.not_carriesCuspidalHeckeFamily_of_isobaric_card_ne_one`.
4. For cuspidal `Π`, Getz–Hahn's Theorem 9.7.3 (the Library's
   `GeneralLinearCuspidalSummandRealizationStatement`) gives a cuspidal realization `T` such that
   `Π` is the closure of the classes of the forms of `T`. The local components of `T` and `S` are
   unramified with the same Hecke characters at almost every place, hence isomorphic there
   (Proposition 7.1.2). By strong multiplicity one (Getz–Hahn, Theorem 11.7.2, p. 309;
   `CuspidalStrongMultiplicityOneStatement`; more generally Corollary 11.7.3, p. 309, and
   `IsobaricStrongMultiplicityOneStatement`), `T` and `S` are equivalent.
5. By `GeneralLinearCuspidalRealizationSummandStatement`, `V_S` is an irreducible closed invariant
   subspace of the cuspidal spectrum, isomorphic to `Π`. By multiplicity one (Getz–Hahn,
   Theorem 11.4.3, p. 303, after Shalika 1974, Theorem 5.5, p. 187;
   `GeneralLinearCuspidalMultiplicityOneStatement`), `Π = V_S`.

These Library statements use the positive quotient of a central split torus `T → GL_{r+1}` and its
cuspidal subspace `fullAEL2CuspidalSubmodule`. A proof along this route also needs their comparison
with the canonical quotient, through `canonicalL2Equiv`, and the comparison of the two local
conditions above.

## Derived content and comparison with the sources

The statement is not stated in this form in the sources. It is derived from the results above: the
classification of the discrete spectrum (Mœglin–Waldspurger), the classification of isobaric
representations by their unramified components (Jacquet–Shalika), strong multiplicity one and
multiplicity one. Its formulation differs from the sources in these points.

* **Quotient.** It uses the Library's canonical quotient `[G] = A_G GL_{r+1}(F) \ GL_{r+1}(𝔸_F)`,
  as Getz–Hahn do in Theorem 10.8.1. Mœglin–Waldspurger instead use `L²(G(k)\G(𝔸), ξ)` with a
  fixed unitary central character `ξ`.
* **Spaces of the representations.** `Π` is a closed subspace of `L²([G])`. `S` is a space of
  cusp forms in the matrix model, so its relation to `L²([G])` is stated by
  `IsCanonicalGeneralLinearFormClass` and `V_S`, and conclusion 1 is added to make `V_S` the closure
  of the classes of all forms of `S`.
* **Local condition.** The hypothesis is an equality of spherical Hecke characters at the finite
  places outside a finite set, in place of an isomorphism of local components outside a finite set
  of places as in Getz–Hahn's Theorem 11.7.2 and Corollary 11.7.3. The section on the local
  condition explains the equivalence.

## Sources

1. J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations, with a view toward
   trace formulae*, Graduate Texts in Mathematics 300, Springer, 2024 (registered literature source
   `getz-hahn-2024-automorphic-representations`). Printed pages, with PDF pages:
   * Theorem 3.10.2, p. 97 (PDF p. 113): the points of an affine algebraic group over a local field
     of characteristic zero form a type I group.
   * Theorems 5.7.1 (Flath) and 5.7.2, p. 152 (PDF p. 167): factorization of irreducible admissible
     representations.
   * Definition 7.1.1 and Proposition 7.1.2, p. 184 (PDF p. 197): unramified representations, their
     Hecke characters, and the fact that an unramified representation is determined by its Hecke
     character.
   * Theorems 9.7.1 and 9.7.3, pp. 264–265 (PDF pp. 276–277): rapid decay of `A_G`-invariant cusp
     forms, and cuspidal automorphic representations as summands of `L²_cusp([G])`.
   * Theorem 10.5.1, p. 282 (PDF p. 294): Langlands' spectral decomposition, with
     `L²_G([G]) = L²_disc([G])`.
   * §10.8 and Theorem 10.8.1, pp. 289–290 (PDF pp. 301–302): Speh representations, their
     isobaric description and unramified `L`-factors, and the Mœglin–Waldspurger classification of
     the irreducible subrepresentations of `L²([GL_n])`.
   * Theorem 11.4.3, p. 303 (PDF p. 314): multiplicity one in `L²_cusp([GL_n])`.
   * Theorem 11.7.2 and Corollary 11.7.3, p. 309 (PDF p. 320): strong multiplicity one for cuspidal
     and for isobaric representations.

   The October 2026 errata (`getz-hahn-2024-errata-2026-10`) list no correction to these items.
2. H. Jacquet and J. A. Shalika, *On Euler products and the classification of automorphic forms
   II*, Amer. J. Math. 103 (1981), 777–815 (registered `jacquet-shalika-1981-euler-ii`). Setup on
   p. 808 and Theorem 4.4 with its proof on p. 809 (PDF pp. 33–34): if the representations induced
   from two cuspidal data `(σ, P)` and `(τ, Q)` have the same unramified components at almost all
   places, the pairs are associate.
3. C. Mœglin and J.-L. Waldspurger, *Le spectre résiduel de `GL(n)`*, Ann. Sci. École Norm. Sup.
   (4) 22 (1989), 605–674 (registered `moeglin-waldspurger-1989-residual-spectrum`). Introduction,
   pp. 605–606 (PDF pp. 2–3), and the Théorème on p. 606: the discrete spectrum in each cuspidal
   datum class is zero unless the datum has equal blocks `(GL_d^m, σ^{⊗m})`, and then it is the
   irreducible representation `J(V)`.
4. J. A. Shalika, *The multiplicity one theorem for `GL_n`*, Ann. of Math. (2) 100 (1974), 171–193
   (registered `shalika-1974-multiplicity-one`), Theorem 5.5, p. 187 (PDF p. 18): every irreducible
   unitary representation of `GL_n(𝔸)` occurs with multiplicity at most one in the space of cusp
   forms. Getz–Hahn cite it for Theorem 11.4.3.
