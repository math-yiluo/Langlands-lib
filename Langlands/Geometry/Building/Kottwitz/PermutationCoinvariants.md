# Coinvariants of a permutation lattice under a subgroup

This internal helper module is pure algebra. It shows that the coinvariants of
a permutation lattice are free on orbits, in the form needed by the proof of KP
Corollary 11.1.9 (`inducedTorusKottwitzRationalSurjectivity`). There it is
applied to the geometric cocharacter lattice of an induced torus, with `H` the
inertia subgroup `relativeInertia F (UnramifiedClosure F) (SeparableClosure F)`.
It adds no assertion from the literature. It is the standard fact
`ℤ[J]_H ≅ ℤ[J/H]`, stated only to the extent needed.

## Setting

All declarations are in `Langlands.Geometry.Building.Kottwitz.PermutationCoinvariants`.
`G` is a group acting on a finite index type `J` (`[MulAction G J] [Fintype J]`).
`V` is an additive commutative group and `ρ : Representation ℤ G V`.
`e : Module.Basis J ℤ V` is a basis. The hypothesis
`he : ∀ g j, ρ g (e j) = e (g • j)` says that `ρ` permutes the basis through the
action on indices. `H : Subgroup G` is a subgroup. The coinvariants are Mathlib's
`Representation.Coinvariants (ρ.comp H.subtype)` with quotient map
`Representation.Coinvariants.mk`.

## Declarations

* `repr_apply`: under `he`, `e.repr (ρ g v) j = e.repr v (g⁻¹ • j)`. Proof: both
  sides are linear in `v`; compare them on basis vectors with `Basis.ext`.
* `orbitClass H j`: the class of `j` in `MulAction.orbitRel.Quotient H J`.
  `orbitClass_eq_iff` says two classes agree iff some `h ∈ H` moves one index to
  the other.
* `orbitFunSum H f j`: the sum of `f : J → ℤ` over the `H`-orbit of `j`, written as
  a sum over `J` with an indicator. Its lemmas: additivity (`orbitFunSum_add`),
  scaling (`orbitFunSum_smul`), congruence (`orbitFunSum_congr`), dependence only
  on the orbit (`orbitFunSum_of_orbitClass_eq`), and pulling out a factor that is
  constant on the orbit (`orbitFunSum_mul_const`). For normal `H`,
  `orbitFunSum_comp_smul` gives
  `orbitFunSum H (f ∘ (g⁻¹ • ·)) j = orbitFunSum H f (g⁻¹ • j)`. The proof
  reindexes by `MulAction.toPerm g` and uses `Subgroup.Normal.conj_mem`.
* `orbitSum e H v j = orbitFunSum H (e.repr v) j`, the orbit sums of
  coordinates, with additivity, scaling and the linear map `orbitSumHom`.
* `orbitSum_apply_mem`: for `h ∈ H`, `orbitSum (ρ h v) = orbitSum v`. Hence
  `coinvariantsOrbitSum` is the induced linear map on coinvariants
  (`Representation.Coinvariants.lift`), and `coinvariantsOrbitSum_mk` evaluates
  it on classes.
* `mk_basis_eq_of_orbitClass_eq`: basis vectors in one `H`-orbit have the same
  class.
* `mk_eq_zero_of_orbitSum`: if all orbit sums of `v` vanish, then `mk v = 0`.
  Proof: expand `v = ∑ repr v i • e i`. Group the sum by orbit classes
  (`Finset.sum_fiberwise`). In each fiber replace `e i` by the class of the orbit
  representative `q.out`; the coefficient is then an orbit sum, which is `0`.
* `mk_eq_mk_iff`: `mk v = mk w` iff all orbit sums of `v` and `w` agree.
* `zsmul_cancel`: for `m ≠ 0`, `m • z = m • z'` implies `z = z'`. So the
  coinvariants are torsion free.
* `orbitSum_smul_of_mk_eq`: for normal `H` and `g ∈ G`, if
  `mk (ρ g v) = mk v` then `orbitSum v (g⁻¹ • j) = orbitSum v j`.
