# Proof: the actual apartment splitting of KP Axiom 4.1.4

The theorem `Langlands.Geometry.Building.actualApartmentSplitting` proves the published
proposition `ActualApartmentSplittingStatement.{u}`: for actual valuation-building data
`B : ValuationBuildingData G` over a nonarchimedean local field, there is
`T : B.ApartmentSplitting` with `B.SatisfiesAffineApartmentAxiom T`. The proof does not use
the premise `B.SatisfiesApartmentAxioms`; every field holds for all actual data.

## Construction of the splitting

- **Derived subgroup.** `G` is connected reductive (a field of `B`), hence smooth and of
  finite type. The proved `derivedSubgroupRepresentability` gives `d : D → G` with
  `IsDerivedSubgroup d`.
- **Derived torus.** The proved `derivedMaximalSplitTorus` gives a maximal split torus
  `j : S' → D`, a closed immersion `e : S' → S` and `j ≫ d = e ≫ i`.
- **Split component.** The proved `splitComponentStatement` gives a split component
  `a : A_G → G`. Its values are central, so they commute with those of the maximal split torus
  `i : S → G`, and `IsMaximalSplitTorus.exists_factor_of_commute` factors `a` as `c ≫ i` with
  `c : A_G → S`.

The splitting is `⟨D, d, S', j, e, A_G, c⟩`. The fields `isDerivedSubgroup`,
`isMaximalSplitTorus_j`, `isClosedSubgroup_e`, `j_comp_d` and `isSplitComponent` are the data
just obtained (the last after rewriting `c ≫ i = a`). Axiom (A 2) is the existing theorem
`ValuationBuildingData.hasAffineConjugations`.

## (A 0): `V(S) = V(S') ⊕ V(A_G)`

The proved `derivedCentralSplitTorusProduct` says that the product map
`p = RelativeRoot.centralComplementProduct e c : S' × A_G → S` is a central isogeny.
`isCompl_cocharacterRange_of_isCentralIsogeny` turns this into complementarity of the ranges
of `cocharacterMapReal e` and `cocharacterMapReal c`.

- *Spanning.* A central isogeny is flat and surjective, so the existing
  `cocharacterRange_sup_eq_top_of_centralComplement` gives that the two ranges span.
- *Independence.* A central isogeny is finite, so `cocharacterMapInt p` is injective
  (`cocharacterMapInt_injective_of_isFinite`), and so is its real scalar extension because
  `ℝ` is flat over `ℤ`. The inclusions `inl : S' → S' × A_G` and `inr : A_G → S' × A_G`
  (`prodInl`, `prodInr`) satisfy `inl ≫ p = e` and `inr ≫ p = c` (`prodInl_prodHom`,
  `prodInr_prodHom`). If `e_* w = c_* z`, injectivity gives `inl_* w = inr_* z`. Applying the
  projection `q = centralComplementProduct (𝟙 S') 0`, with `inl ≫ q = 𝟙` and `inr ≫ q = 0`,
  gives `w = 0`.

## (A 1): `N(F)` preserves `S'`

Let `n` normalize `i` through `σ = normalizingAut B.i n`, that is `i ≫ int(n) = σ ≫ i`.
`IsDerivedSubgroup.normalizing_mem_derivedSubgroup` shows that `e ≫ σ ≫ i = j ≫ d ≫ int(n)`
takes values in the derived subgroup: the points of `j ≫ d` lie in the range of `d`, which is
the derived subgroup, and the derived subgroup is normal (`derivedSubgroup_isNormal`).
`IsDerivedSubgroup.exists_factor_derivedTorus` then factors `e ≫ σ` through `e`: the factor
of `e ≫ σ ≫ i` through `d` commutes with `j` because both land in the commutative `S`, so it
factors through the maximal split torus `j` (`IsMaximalSplitTorus.exists_factor_of_commute`).
This is the argument of the existing `IsDerivedSubgroup.exists_factor_splitTorusEnd`, with
source `S'` instead of `S`. Doing the same for `n⁻¹` and `σ⁻¹`, and cancelling the closed
immersion `e`, gives mutually inverse endomorphisms, hence `τ : S' ≅ S'` with
`τ ≫ e = e ≫ σ` (`IsDerivedSubgroup.exists_derivedTorus_iso`).

## (A 1): the centre acts trivially

`innerIso_hom_eq_id_of_mem_center`: conjugation by a central base point is the identity of
`G`, since its value at every test scheme commutes with every point. If `n ∈ N(F)` is central,
so is `n⁻¹`, hence `n⁻¹` normalizes `i` through the identity of `S` and the Weyl action of
`n⁻¹` on characters is trivial (`weylAction_eq`). By the formula
`(n·φ)_a(u) = φ_{n⁻¹·a}(n⁻¹ u n)` (`RootFunctionFamily.smul_apply`) and centrality of `n` in
`G(F)`, `n·φ = φ` for every point `φ` of the apartment
(`ValuationBuildingData.normalizerAction_eq_one_of_mem_center`).

## Scope

All objects are the actual ones of `B`: its torus `S`, its `N(F)`-action on `A(S)`, the actual
derived subgroup and split component. The proof holds at every universe, in both
characteristics, with no split, quasi-split, rank or residue-field restriction. The source
statement is KP Axiom 4.1.4 (printed pp. 158–159 / PDF pp. 189–190); the proof is an internal
assembly of the Library's derived-subgroup, split-torus and split-component theorems.
