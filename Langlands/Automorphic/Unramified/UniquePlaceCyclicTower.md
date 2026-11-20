# Prime cyclic towers above a place with one place above it

Worker 5130 wrote this module for Task 7784. In Harris's Proposition 4.8 the auxiliary place
has exactly one place of the Galois closure `L` above it. This module shows that the Galois
group is then solvable, so prime cyclic towers exist. It also applies Arthur–Clozel
III.4.2(c) to every step of such a tower.

## Solvability (namespace `Langlands.Global.AdelicFunctoriality`)

- `isSolvable_ringAut_of_finite`: the ring automorphisms of a finite field `R` of
  characteristic `p` form a solvable group. Each one is `ZMod p`-linear (`RingHom.ext_zmod`),
  so they embed into `Gal(R/𝔽_p)`, which is abelian (cyclic).
- `isSolvable_localAut`: for a finite extension of `p`-adic fields given as a
  `PadicField` with topological data `T` over a field `K` with `ℚ_p → K → L`, the group
  `Aut_K(L)` is solvable. The published inertia subgroup is solvable
  (`Ramification.Padic.isSolvable_inertia`). It is the kernel of the residue map into the
  ring automorphisms of the finite residue field, which is solvable by the previous item.
  These two lemmas copy the private lemmas `ringAut_isSolvable` and `localAut_isSolvable`
  of the published `HarrisCyclicPrimeTowerProof`, made public here.
- `isSolvable_completionAut`: for finite places `w | v` of number fields `L/K`, the group
  `Aut_{K_v}(L_w)` is solvable. Apply `isSolvable_localAut` to the published `p`-adic field
  structure `FiniteExtension.towerPadicField v w` on `L_w`.
- `isSolvable_of_hasUniquePlaceAbove`: if `L/K` is Galois and `v` has exactly one place of
  `L` above it (`Harris.HasUniquePlaceAbove L v`), then `Gal(L/K)` is solvable. Let `w`
  be a place above `v`. Every `g ∈ Gal(L/K)` moves `w` to a place above `v`, hence fixes
  it. By the published criterion `mem_range_decompositionHom_iff`, `g` lies in the image
  of the decomposition map `Aut_{K_v}(L_w) → Gal(L/K)`. A quotient of a solvable group is
  solvable.

## Towers (namespace `Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower`)

- `nonempty_of_isSolvable`: a finite Galois extension `K/F` of number fields with solvable
  Galois group has a `PrimeCyclicBaseChangeTower F K`. The published
  `Langlands.FieldTheory.solvableGaloisPrimeTower` gives the intermediate fields and the
  step conditions (Galois, cyclic, prime degree). Monotonicity comes from the step
  inclusions.
- `exists_weakBaseChange_step`: given Arthur–Clozel III.4.2(c) in the published form
  `CyclicPrimeIsobaricBaseChangeStatement`, every unitary isobaric datum at level `i` of a
  prime cyclic tower `T` (with compact adele quotients at every level) has a unitary weak
  base change at level `i + 1`. Each step is Galois of prime degree. The uniqueness part
  of III.4.2(c) is not used.
- `exists_weakBaseChange_step_of_isTotallyComplex`: the same from the totally complex form
  `CyclicPrimeIsobaricBaseChangeTCStatement` when the bottom field `F` is totally complex.
  Every level is an extension of `F`, hence totally complex
  (`isTotallyComplex_of_algebra`).

## Provenance

The solvability of the Galois group of a finite Galois extension of `p`-adic fields is
classical (Serre, *Local Fields*, Chapter IV, §2). Harris uses it in the proof of
Proposition 4.8 (Invent. Math. 134, 1998), where the place `v` has one place above it in
the Galois closure. Solvable Galois extensions have prime cyclic towers by the fundamental
theorem of Galois theory. Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula*, III.4.2(c), as stated in the Library.
