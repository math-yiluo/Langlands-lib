# Rational conjugacy of Levis of a parabolic: proof

Author: Worker 4311.

`Langlands.GroupScheme.rationalLeviConjugacy` proves exactly the published
proposition `Langlands.GroupScheme.RationalLeviConjugacyStatement.{u}` of
`Langlands.GroupScheme.Rational.RationalLeviConjugacyStatement`, at its
universe `u` and with no added premise. The statement's Lean/Markdown pair and
its imports are unchanged.

Take any field `k : Type u`, a connected reductive `G` over `Spec k`, an actual
rational parabolic `j : P → G`, two supplied rational Levis `l : L → P` and
`l' : L' → P` (`IsRationalLeviSubgroup`), and any supplied represented
geometric unipotent radical `r : U → P`
(`LeviSubgroup.IsGeometricUnipotentRadical`). The theorem gives a unique
rational point `q : Spec k → U` for which some group-scheme isomorphism
`e : L ≅ L'` satisfies

`l ≫ (P.innerIso (q ≫ r.hom.hom)).hom = e.hom ≫ l'`.

This is an equality of group-scheme morphisms, so it holds on every test
scheme, including nonreduced ones. The field may have any characteristic and
need not be perfect, split or algebraically closed. The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The proof applies one published reduction to three published unconditional
theorems:

- `DynamicLeviConjugacy.rationalLeviConjugacy_of_dynamic`
  (`Rational/DynamicLeviConjugacyReduction`) concludes
  `RationalLeviConjugacyStatement.{u}` from three inputs. It also proves, for
  actual scheme morphisms, the comparison with the specified radical, the
  construction of the source isomorphism and the uniqueness of the
  conjugating point.
- Its first input, `ParabolicDynamicStatement.{u}`, is the published theorem
  `parabolicDynamic` (`Absolute/ParabolicDynamicProof`). Every rational
  parabolic of a connected reductive group is the dynamic `P_G(χ)` of a
  cocharacter defined over `k`.
- Its second input, `DynamicGeometricUnipotentRadicalStatement.{u}`, is the
  published theorem `dynamicGeometricUnipotentRadical`
  (`Dynamic/GeometricUnipotentRadicalProof`). A closed representative of
  `U_G(χ)`, factored through a representative of `P_G(χ)`, is a geometric
  unipotent radical.
- Its third input `hlift` is the published theorem
  `Dynamic.exists_unipotent_conj_of_mul_inv_mem`
  (`Dynamic/UnipotentCocharacterConjugacy`). Over a field, let `G` be affine
  and let `χ, ψ : 𝔾_m → G` be cocharacters with `ψ · χ⁻¹ ∈ U_G(χ)(𝔾_m)`.
  Then `ψ = Int(u) ∘ χ` for some rational point `u ∈ U_G(χ)(k)`. That theorem
  takes `k` and `G` as implicit arguments. The lambda
  `fun _ _ _ _ χ ψ h => Dynamic.exists_unipotent_conj_of_mul_inv_mem χ ψ h`
  supplies it in the explicitly quantified form that `hlift` requires.

All three inputs are proved in the Library without further hypotheses. So
`rationalLeviConjugacy` has no premise.

The reduction's Markdown explains its argument in full. It writes
`range j = P_G(χ)`, and it identifies the kernel of each Levi's retraction with
`U_G(χ)` and with the image of `r`. It then uses `hlift` to conjugate each
Levi's cocharacter back to `χ` by a rational point of `U_G(χ)`. After that
conjugation both Levis have image exactly `Z_G(χ)`, which yields `e` and `q`.
Uniqueness follows from `Z_G(χ) ∩ U_G(χ) = 1`.

## Provenance

The target is Borel and Tits, *Groupes réductifs* (1965), Corollary 3.14
(printed p.80, PDF p.27), specialized to parabolics. The target statement's
Markdown records this specialization and the checked 1972 corrections. The
implemented route does not follow Borel–Tits. It uses the dynamic description
of parabolics and the decomposition `P_G(χ) = Z_G(χ) ⋉ U_G(χ)` of
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed., 2015),
Proposition 2.1.8, as recorded in the reduction's Markdown. This module adds
no external structural assertion or citation. Each reused module keeps its
own authorship: the reduction is by Worker 1491, and Worker 1515
formalized the cocharacter conjugacy theorem along a route Worker 1491
proposed. The author
lines of `ParabolicDynamicProof` and `GeometricUnipotentRadicalProof` record
their authors.
