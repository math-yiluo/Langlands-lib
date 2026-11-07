# The root group of a split reductive group over a ring and its field fibres

Namespace `Langlands.GroupScheme.LocalRootGroup`. The main result is
`exists_coordinate`. Let R be a reduced local ring and G an affine group over
Spec R with a split torus `i`. Take exponent cocharacters μ and ν. The module
builds the group U = U_{Z}(ν) for Z = Z_G(μ) and shows the following. If every
field fibre of U is 𝔾ₐ, with the torus acting through a character α and
⟨α, ν⟩ = m > 0, then the coordinate ring of U is R[x] for a homogeneous x of
degree m.

## Provenance

These are internal results for the local-ring Isomorphism Theorem task
(ab10ec3c). They construct root groups over a reduced local ring as in Conrad,
*Reductive group schemes* (2014), proof of Theorem 4.1.4 (printed
pp.116–119). There the a-root group is U_{Z_G(T_a)}(λ) for a cocharacter λ with
⟨a, λ⟩ > 0. Here T_a is replaced by a cocharacter μ orthogonal to a, and the
proof of Lemma 4.2.2 is replaced by the graded argument of
`Langlands.CommutativeAlgebra.GradedLine`. The field input is the Library's
rank-one root group `rankOne_exists_rootGroup` (module
`Reductive.RankOneCellData`). It is applied to the base change of Z, which is
connected reductive by `dynamicCentralizerReductive` and has roots computed by
`dynamicCentralizerRoots`.

## The construction over R

- `model` is the corepresented model of G (`AffineCoordinates.groupSchemeIso`).
  `modelTorus i` is the torus in it, and `centCochar i μ` is the cocharacter μ in
  it.
- `Zc i μ` is `Corepresented.centralizerScheme (centCochar i μ)`, a
  corepresented closed subgroup representing Z_G(μ), with inclusion `jZ i μ`.
  `torusZ i μ` factors the torus through it (`torusZ_comp`), since the torus
  centralizes its own cocharacters (`range_le_centralizer_groupHom_comp`).
- `unipCochar i μ ν` is ν viewed as a cocharacter of Z. `Uc i μ ν` is
  `Corepresented.unipotentScheme (unipCochar i μ ν)`, with inclusion `jU`.
  `coordU i μ ν` is its coordinate ring, graded by `unipCoaction`.
- `baseChangeCocharacter_groupHom_comp`: base change of an exponent cocharacter
  followed by a map from the torus is the exponent cocharacter over the new base
  followed by the base-changed map. It follows from the Library's
  `splitTorus.groupHom_exponentCocharacter_baseChange`.

## Field fibres

For a field K over R:

- `ZK`, `jZK`, `tK`, `UK` are the base changes of Z, of its inclusion into G, of
  the torus of Z, and of U. `tK_comp` says that tK composed with jZK is the
  canonical base-changed torus `splitTorus.baseChangeHom`.
  `isRepresentedBy_jZK` and `isClosedSubgroup_jZK` say that Z_K is the dynamic
  centralizer of μ in G_K. `isRepresentedBy_jUK` says that U_K is the dynamic
  unipotent subgroup of ν in Z_K. Both use the Library's
  `Dynamic.centralizer_baseChange` and `Dynamic.unipotent_baseChange`.
- `exists_fibreIso`: assume G_K is connected reductive and the torus is maximal.
  Assume the only roots orthogonal to μ are ±α, with ⟨α, μ⟩ = 0 and
  ⟨α, ν⟩ > 0. Then there is an isomorphism Φ : 𝔾ₐ,K ≅ U_K under which the torus
  acts through α. Z_K is connected reductive with maximal torus tK; its roots
  are ±α by `dynamicCentralizerRoots`, so any two are linearly dependent.
  `rankOne_exists_rootGroup` then gives x : 𝔾ₐ → Z_K representing the same
  dynamic unipotent subgroup as U_K, and
  `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` compares the two.
- `charValue_unitPoint`: a character χ takes the value u^⟨χ, ν⟩ on the point
  ν(u) of a cocharacter. `weightPointAction_scalarPoint`: the torus acts on the
  scalar point c through the character value.

## The parameter family

Fix Φ as above. For a K-algebra D and d ∈ D:

- `fibrePoint Φ D d` is the point of U_K over Spec D with parameter d.
  `fibreAlgHom Φ D d : coordU →ₐ[R] D` classifies its underlying point of U.
- `fibrePoint_comp`, `fibreAlgHom_comp`: naturality in D.
  `fibrePoint_bijective`, `fibreAlgHom_bijective`: every R-algebra map
  coordU → D is `fibreAlgHom Φ D d` for exactly one d.
- `isUniversalLine_fibre`: the classifying map of the universal parameter point
  X over K[X] is a universal line in the sense of `GradedLine.IsUniversalLine`.
- `fibrePoint_conj`: conjugation by the cocharacter ν at a unit u multiplies the
  parameter by u^⟨α, ν⟩. This is the torus action of `exists_fibreIso`, with
  `baseChangeCocharacter_groupHom_comp`, `charValue_unitPoint` and
  `weightPointAction_scalarPoint`.
- `scaling_fibre`: the universal classifying map intertwines the grading of
  coordU with Y ↦ T^m Y, where m = ⟨α, ν⟩. It applies
  `Corepresented.scaling_of_conj` to the parameter points X over K[X] and
  T^m X over K[X][T, T⁻¹]. The conjugation identity comes from `fibrePoint_conj`
  at the unit T, transported to U by `testOverHom_comp_conj` and
  `specMapOver_comp_testOverHom`.

## The coordinate ring

- `finiteType_coordU`: coordU is of finite type when G is smooth, since it is a
  quotient of the coordinate algebra of G.
- `exists_coordinate`: let R be reduced local and G smooth. Suppose that for
  every field K over R there are α and Φ as above with ⟨α, ν⟩ = m > 0. Then some
  x ∈ coordU, homogeneous of degree m, makes `Polynomial.aeval x : R[X] → coordU`
  bijective. This is `GradedLine.exists_aeval_bijective_of_universal`, applied
  with `isUniversalLine_fibre` and the gradedness from `scaling_fibre` and
  `GradedLine.coeff_eq_zero_of_scaling`.

`exists_coordinate` uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The ring-algebra point helpers used here are from
`Langlands.GroupScheme.Corepresented.RingCoordinates` in
`Langlands.GroupScheme.Dynamic.RingPointCoordinates`.
