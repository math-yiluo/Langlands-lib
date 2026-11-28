# Points with values in discrete valuation rings of ramification index one

- `algebraMap_injective_of_ram`: a local map `R → R'` of ramification index one between discrete
  valuation rings is injective.
- `TestPoint X f`: a point `a : Spec R' ⟶ X` over `Spec R`, where `R'` is a discrete valuation ring
  (in the same universe) with a local map `R → R'` of ramification index one
  (`IsRamificationIndexOne`). `special` is the image of the closed point.
- `TestPoint.map`, `TestPoint.lift`, `eq_of_a_eq`: composing a point with a morphism and lifting a
  point along a morphism.
- `mem_chart`, `defect`, `defect_eq`: the defect of a point, computed in any affine chart through
  its closed point (`Charts.defectAt_eq`).
- `defect_map`: the defect does not change along a morphism which is an isomorphism over an open
  containing the closed point.
- `prime_eq_bot_of_not_mem`: a prime ideal of `R` not containing a uniformizer is zero. It is used
  in `smooth_away` to see that the points of a chart where the uniformizer is invertible lie over
  the generic point of `Spec R`.
- `TestPoint.f_special`: the closed point of a test point lies over the closed point of `Spec R`.
- `mem_smoothLocus_comp_iff`: smoothness at a point is unchanged by a morphism which is an
  isomorphism over an open containing the image of the point.
- `finitePresentation_base`, `finiteType_base`: for a chart of a scheme locally of finite
  presentation (resp. locally of finite type) over `R`, the chart ring is of finite presentation
  (resp. of finite type) over `R`.
- `ι_mem_smoothLocus_iff`, `smooth_away`: for `f` locally of finite presentation, a point of a
  chart is in the smooth locus of `f` exactly when its prime is in the algebraic smooth locus of the
  chart ring; if all points of the generic fibre are smooth, the localization of every chart ring at
  a uniformizer is smooth over `R`.
- `f_generic`, `generic_range_subset`: the generic point of `Spec R'` maps to the generic fibre.
- `exists_lift`, `lift_unique`: for a proper `g : X₁ ⟶ X` that is an isomorphism over an open
  containing the generic fibre, every test point lifts uniquely along `g` (valuative criteria of
  properness and separatedness).

The family of all test points plays the role of the set `E` of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.4 (printed p. 71); the ramification-index-one condition is that of §3.6,
Definition 1 (printed p. 78).
