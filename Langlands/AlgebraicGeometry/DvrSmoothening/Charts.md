# Affine charts, points with values in local rings, and the defect of a point

- `defectWith`, `chartDefect`, `pointDefect_eq_defectWith`, `chartDefect_algebraMap`: the defect
  `pointDefect` with explicitly chosen algebra structures; `chartDefect_comp_of_formallyEtale`
  transports it along formally étale maps.
- `AffineChart X`: an open immersion `Spec C.ring ⟶ X`. `base f` is the induced ring map from `R`
  for `f : X ⟶ Spec R`, with `Spec_base`.
- `range_subset_of_closedPoint_mem`, `liftPoint`, `liftPoint_ι`, `pointHom`, `Spec_pointHom`,
  `pointHom_eq_of_Spec`, `pointHom_comp_base`: a point `a : Spec R' ⟶ X` of a local ring whose
  closed point lies in a chart factors through the chart, and corresponds to a ring map
  `C.ring → R'` compatible with the structure maps.
- `defectAt f a C`: the defect of `a` computed in the chart `C`. `defectAt_eq_of_factor` and
  `defectAt_eq`: it does not depend on the chart. Two charts are compared through a basic open of
  the first chart lying inside the second, using that open immersions of affine schemes give
  formally étale ring maps (`formallyEtale_of_isOpenImmersion`; `Spec_map_injective` is an
  auxiliary fact).
- `ofAffineOpen`, `exists_le`, `exists_mem`: charts from affine opens, and the existence of charts
  through a point inside a given open.
- `liftPoint_closedPoint`, `ι_liftPoint_closedPoint`: the lifted point sends the closed point to the
  expected point.
- `isOpenImmersion_comp_of_isIso_restrict`, `push`, `push_mem`, `push_defectAt`: a chart of `X₁`
  inside an open over which `g : X₁ ⟶ X` is an isomorphism gives a chart of `X` with the same ring
  and the same defects.
- `mem_smoothLocus_SpecMap_iff`: membership in the smooth locus of `Spec B ⟶ Spec A` in terms of
  `Algebra.IsSmoothAt`.

Internal infrastructure for the global smoothening argument of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.4.
