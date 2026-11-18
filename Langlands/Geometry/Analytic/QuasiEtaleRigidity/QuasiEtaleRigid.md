# Uniqueness in Berkovich's Key Lemma for compact quasi-étale spaces

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. Its main
theorem is the uniqueness in Berkovich's Key Lemma 7.2 for commutative
diagrams (*Vanishing cycles for formal schemes*, 1994, §7, printed p.560),
in the form `IsRigid` of `LiftCompatibilityDeduction`.

- `IsRigidOn.comp_mono`: postcomposition with a monomorphism preserves
  rigidity.
- `IsRigidOn.isRigid`: rigidity over the whole space is `IsRigid`.
- `IsRigidOn.iso_comp_univ`: transport along a source isomorphism, over the
  whole space.
- `arrow_hom_eq`: an isomorphism `Arrow.mk f ≅ Arrow.mk p` expresses `p` as
  `e.inv.left ≫ f ≫ e.hom.right`.
- `isRigidOn_chart_of_hasDomainEtaleFactorization`: suppose the restriction
  of a strong map `g` to a chart has a domain-étale factorization
  `e₁ ≫ domainι W D ≫ w` with `w` étale (the Library's
  `HasDomainEtaleFactorization`). Then the restriction is rigid on its whole
  source. The étale `w` is isomorphic in the arrow category to `map g₂` with
  `g₂` étale over all pieces. `domainImageIso` moves `D` to an analytic domain
  `D₂` of the source of `g₂`. `D₂` is compact and Hausdorff because it is
  homeomorphic to the chart. `isRigidOn_domainInclusion_comp_etale` gives
  rigidity of `incl_{D₂} ≫ map g₂`. Transport along the source isomorphism
  `e₁ ≪≫ domainImageIso` and postcomposition with the target isomorphism give
  rigidity of the restriction.
- `isRigid_of_quasiEtale`: a quasi-étale morphism `p : U ⟶ X` with compact
  `U` (compact and Hausdorff) is rigid. By definition of `quasiEtale`, `p` is
  isomorphic in the arrow category to `map g` for a quasi-étale strong map `g`
  between constructed saturations. The source space of `g` is homeomorphic to
  that of `U`, hence compact and Hausdorff. The Library's
  `IsQuasiEtale.exists_finite_domainEtale_chart_cover` supplies finitely many
  covering charts with domain-étale factorizations. Each restriction is rigid
  by the previous item, so `isRigidOn_of_chart_cover` makes `map g` rigid.
  Transport along the arrow isomorphism makes `p` rigid.
