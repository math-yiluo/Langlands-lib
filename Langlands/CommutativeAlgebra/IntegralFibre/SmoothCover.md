# A smooth faithfully flat cover with free differentials

This module proves one step of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
Let `S` be a flat finitely presented `R`-algebra with geometrically integral fibres. The module
finds finitely many basic opens `D(s i)` of `Spec S` with three properties: each `S_{s i}` is
smooth over `R`, each has a free module of differentials, and the product `∀ i, S_{s i}` is
faithfully flat over `R`. The geometric hypothesis enters in the algebraic form "`K ⊗[R] S` is a
domain for every field `K` over `R`", through
`Langlands.CommutativeAlgebra.exists_mem_smoothLocus_comap_eq` from
`Langlands.CommutativeAlgebra.IntegralFibre.GenericSmoothness`.

## Statements

All names are in the namespace `Langlands.CommutativeAlgebra`.

- `free_localizedModule_away_mul`: let `A` be a commutative ring, `M` an `A`-module and
  `r t : A`. If `LocalizedModule.Away r M` is free over `Localization.Away r`, then
  `LocalizedModule.Away (r * t) M` is free over `Localization.Away (r * t)`.
- `exists_notMem_smooth_free`: let `S` be a finitely presented `R`-algebra and `q` a point of
  `Algebra.smoothLocus R S`. Then there is `s : S` with `s ∉ q` such that
  `Localization.Away s` is smooth over `R` (`Algebra.Smooth`) and
  `Ω[Localization.Away s⁄R]` is a free `Localization.Away s`-module.
- `exists_smooth_free_cover`: let `R` and `S` be commutative rings in one universe `u` and `S` a
  flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every field
  `K : Type u` with an `R`-algebra structure. Then there are `m : ℕ` and `s : Fin m → S` such
  that for every `i`, `Localization.Away (s i)` is smooth over `R` and
  `Ω[Localization.Away (s i)⁄R]` is free over `Localization.Away (s i)`, and the product ring
  `∀ i, Localization.Away (s i)` is faithfully flat over `R` (`Module.FaithfullyFlat`).

## Proofs

`free_localizedModule_away_mul`. Write `A_r` and `A_{rt}` for the two localizations. Make
`A_{rt}` an `A_r`-algebra through `IsLocalization.Away.awayToAwayRight`; then `A`, `A_r` and
`A_{rt}` form a scalar tower. `LocalizedModule.equivTensorProduct` identifies
`LocalizedModule.Away r M` with `A_r ⊗[A] M`, so the latter is free over `A_r`. Base change
preserves freeness (a Mathlib instance), so `A_{rt} ⊗[A_r] (A_r ⊗[A] M)` is free over `A_{rt}`.
`AlgebraTensorModule.cancelBaseChange` identifies it with `A_{rt} ⊗[A] M`, and
`LocalizedModule.equivTensorProduct` identifies that with `LocalizedModule.Away (r * t) M`.

`exists_notMem_smooth_free`. The smooth locus is open (`Algebra.isOpen_smoothLocus`), and
basic opens form a basis of `Spec S`. So there is `g ∉ q` with `D(g)` inside the smooth locus.
By `Algebra.smoothLocus_eq_compl_support_inter`, every point of the smooth locus lies in the
free locus of `Ω[S⁄R]`, so the localization of `Ω[S⁄R]` at `q` is free over `S_q`. `Ω[S⁄R]` is
finitely presented, so `Module.FinitePresentation.exists_free_localizedModule_powers` gives
`r ∉ q` with `LocalizedModule.Away r Ω[S⁄R]` free over `S_r`. Take `s = r * g`; it is not in `q`
because `q` is prime.

- Smoothness: `D(r * g) ⊆ D(g)` lies in the smooth locus, and
  `Algebra.basicOpen_subset_smoothLocus_iff_smooth` turns this into smoothness of `S_s`.
- Freeness: `free_localizedModule_away_mul` makes `LocalizedModule.Away (r * g) Ω[S⁄R]` free over
  `S_s`. The map `KaehlerDifferential.map R R S S_s : Ω[S⁄R] → Ω[S_s⁄R]` is a localization of
  modules at the powers of `s`. So `IsLocalizedModule.iso` gives an `S`-linear isomorphism
  `LocalizedModule.Away s Ω[S⁄R] ≃ Ω[S_s⁄R]`.
  `LinearEquiv.extendScalarsOfIsLocalization` upgrades it to an `S_s`-linear isomorphism, so
  `Ω[S_s⁄R]` is free.

`exists_smooth_free_cover`. For every prime `p` of `R`, `exists_mem_smoothLocus_comap_eq` gives
a point `q` of the smooth locus of `S` over `p`. `exists_notMem_smooth_free` then gives `f p ∉ q`
with `S_{f p}` smooth and `Ω[S_{f p}⁄R]` free. Thus `p` lies in the image `U p` of `D(f p)` under
`Spec S → Spec R`.

`S` is flat over `R`, so it satisfies going down (the Mathlib instance
`Algebra.HasGoingDown.of_flat`). Since `S` is also finitely presented,
`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` shows that each `U p` is
open. The `U p` cover `Spec R`, which is compact. So finitely many of them cover it, indexed by a
finset `t`. Enumerate `t` by `Finset.equivFin` and put `s i = f p_i`, with `m` the cardinality of
`t`. Smoothness and freeness of differentials hold by the choice of `f`.

For faithful flatness, write `P = ∀ i, S_{s i}`. Each `S_{s i}` is flat over `S` (a
localization) and hence over `R` (`Module.Flat.trans`). A finite product of flat modules is flat:
`P` is isomorphic as an `R`-module to the finitely supported functions on the finite index type
(`DFinsupp.linearEquivFunOnFintype`), and `DFinsupp` of flat modules is flat. By
`Module.FaithfullyFlat.of_comap_surjective` it remains to show that every prime `p` of `R` is the
image of a prime of `P`. Some `U p'` with `p' ∈ t` contains `p`, so `p` is the image of a prime
`q ∈ D(f p')`. Let `i` be the index of `p'`, so that `s i = f p'`. By
`PrimeSpectrum.localization_away_comap_range`, `q` is the image of a prime `Q` of `S_{s i}`. The
prime of `P` obtained as the preimage of `Q` under the evaluation `Pi.evalRingHom _ i` lies over
`p`. To check this, compose the ring maps: the composite `R → S → S_{s i}` equals
`R → P → S_{s i}`.

## Provenance

`exists_notMem_smooth_free` refines Stacks Project, Definition 10.137.10 (Tag 00TB): if
`R → S` is smooth at `q`, there is `g ∉ q` with `R → S_g` smooth. Here `S_g` is also asked to
have free differentials. The openness of the images uses Stacks Project, Proposition 10.41.8
(Tag 00I1), in its Mathlib form for going-down finitely presented maps. `free_localizedModule_away_mul`
is a standard fact proved here for convenience. `exists_smooth_free_cover` is the covering step
of Worker 281's route to Tag 05FT: Worker 281 proposed the statement, and Worker 928 wrote the
Lean proof. The module is internal to the project.
