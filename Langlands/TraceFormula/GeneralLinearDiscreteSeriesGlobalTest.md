# A global test with prescribed local factors and nonzero cuspidal trace

## Auxiliary results

* `exists_isCompact_isClopen_mem_subset`: in a locally compact Hausdorff totally disconnected
  space every neighbourhood of a point contains a compact clopen neighbourhood.
* `IsNonnegReal` (a complex number that is a nonnegative real) with its closure under
  products, finite products, indicator functions and characteristic test functions.
* `exists_nonneg_kernel_pos`: a smooth compactly supported archimedean kernel with nonnegative
  real values that is positive at a given point, the right translate of a kernel from
  `ArchimedeanGL.normalizedCompactKernel`.
* `isRegularSemisimple_of_map`, `isRegularSemisimple_map`: separability of the characteristic
  polynomial is unchanged by a field extension.
* `regularEllipticSet_isOpen_nonempty`: the regular elliptic elements of `GL_{r+1}(K_v)` form a
  nonempty open set (`BaseChange.isOpen_regularElliptic`,
  `BaseChange.exists_regularElliptic_trace_ne_zero`).
* `characteristic_ne_zero_iff`, `characteristic_eq_one`, `tsupport_characteristic_subset`:
  values and support of `Hecke.TestFunction.characteristic`.
* `normOnePositiveAverage_orbitalIntegral_ne_zero`: the norm-one orbital integral of the
  positive average of a nonnegative compactly supported continuous function positive at `δ`
  is nonzero when orbit functions of compactly supported continuous functions are integrable.

## The main theorem

`exists_globalTest_trace_ne_zero`: let `v₀, v₁, v₂` be distinct finite places of `K` and `Φ` a family of locally constant compactly
supported functions on the groups `GL_{r+1}(K_v)` such that `Φ_{v₁}` has vanishing constant
terms and, for each `i`, the orbital integrals of `Φ_{v_i}` are nonzero (for all compatible
measures) at every point of some nonempty open set `U_i`. Then there are a finite set
`S ∋ v₀, v₁, v₂`, local tests `F` with `F_{v_i} = Φ_{v_i}` and an archimedean kernel `a` such
that the operator of `f = a ⊗ finiteTest S F` on `L²` of the positive rational quotient is
trace class, maps into the cuspidal subspace and has nonzero trace.

The proof follows Arthur–Clozel (1989), Chapter 1, proof of Lemma 6.5 (printed pp. 54–55), and
Henniart–Lemaire (2011), II.6.7–II.6.9 (printed pp. 123–125).

1. Choose a fourth finite place `v₃`. By `rationalGLWeakApproximation` there is
   `γ ∈ GL_{r+1}(K)` lying in `U_i` at `v_i` and regular elliptic at `v₃`; it is then regular
   semisimple at every place.
2. Let `S` contain the four places and every place where `γ` is not integral
   (`FiniteAdelicGL.eventually_localIntegral`). Away from `v₀, v₁, v₂` take characteristic
   functions of compact clopen neighbourhoods of `γ`, contained in the regular elliptic set at
   `v₃`, and let `a` be nonnegative and positive at the archimedean component of `γ`.
3. `positiveAverageOrbitSupport` bounds the support of positive averages by a compact set of
   regular elliptic points at `v₃`. `ordinaryOrbitIsolation` shrinks the factor at `v₃` so that
   only the rational class of `γ` meets the support.
4. `generalLinearTensorSingleOrbitTrace`, with the cuspidal factor at `v₁`
   (`finiteTest_twoBlock_vanishing`) and the Hilbert–Schmidt property from
   `generalLinearTensorCuspidalHilbertSchmidt_of_pos`, gives that `R(f)` is trace class with trace the volume
   times the orbital integral of the positive average at `γ`.
5. The orbital integral is nonzero by `threePlaceTensor_orbitalIntegral_ne_zero`: the local
   orbital integrals at `v₀, v₁, v₂` are nonzero by `localOrbitalNonvanishingAt_of_matrix`, and
   replacing the three prescribed factors by bump functions gives a nonnegative test positive at
   `γ`, whose orbital integral is nonzero by `normOnePositiveAverage_orbitalIntegral_ne_zero`
   and the integrability in `generalLinearEllipticCentralizer`. The volume is finite by the
   single-orbit trace formula and nonzero by compatibility.
6. `groupSchemeCuspidalImage`, with `generalLinearRadicalIntegralVanishing` and
   `adelicTestTensor_finiteTest_twoBlock_vanishing`, puts the image of `R(f)` in the cuspidal
   subspace.
