# Trivial rational prime-adic monodromy makes prime-power torsion rational

Let `L` be a field, `B` an abelian scheme over `Spec L`, `ℓ` a prime and `hu` a family
of proofs that the powers of `ℓ` are units of `Γ(Spec L, ⊤)`. Write
`closurePoint L = Spec.algebraMap L (AlgebraicClosure L)` for the geometric point of
`Spec L` given by the algebraic closure. The module proves that if every element of
the finite étale fundamental group `FundamentalGroup (closurePoint L) _` acts
trivially on the rational prime-adic Tate module, then for every `ν` every
`ℓ ^ ν`-torsion point of `B` with values in `AlgebraicClosure L` is the restriction of
an `L`-point of `B`:

`hasRationalGeometricTorsion_of_rationalMonodromy_eq_one B ℓ hu h ν :
  HasRationalGeometricTorsion B (ℓ ^ ν)`,

where `h` says that `Tate.PrimeAdic.rationalMonodromyRepresentation (closurePoint L)
(geometricFiberFinite _) torsionFiniteEtale B ℓ hu g = 1` for every `g`. The
predicate `HasRationalGeometricTorsion` is the one of
`Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement`.

This is the classical remark that the Galois group of `L` acts on `V_ℓ(B)` through
its action on the torsion points, and that a geometric point of a finite étale
`L`-scheme fixed by the Galois group is rational. The module derives it from the
Library's constructions; it has no separate literature source.

## Proof

All declarations are in the namespace `Langlands.AbelianScheme.Tate.PrimeAdic`.

1. `monodromyMap_eq_self_of_rationalMonodromy_eq_one`: every `g` fixes every
   element `x` of the integral Tate module `Integral B (Over.mk (closurePoint L)) ℓ`.
   The integral module embeds in the rational one by
   `GroupScheme.Tate.PrimeAdic.toRational_injective`, and
   `toRational_monodromy` identifies the image of `monodromyMap … g x` with
   `rationalMonodromy … g` applied to the image of `x`, which is that image by
   hypothesis.
2. `natCast_ne_zero_closure`: the hypothesis `hu 1` makes `ℓ` a unit of
   `Γ(Spec L, ⊤)`, hence of `L` through `Scheme.ΓSpecIso`, so `ℓ` is nonzero in the
   algebraic closure.
3. `levelMonodromy_eq_self_of_rationalMonodromy_eq_one`: every `g` fixes every
   point `y` of the torsion level `Level B (Over.mk (closurePoint L)) ℓ ν`. By
   `algClosedPointDivisibility` the points of `B` over the algebraically closed
   field are divisible by `ℓ` (step 2), so
   `GroupScheme.Tate.PrimeAdic.evaluation_surjective_of_pow` writes `y` as the
   `ν`-th coordinate of an element `x` of the integral Tate module. The coordinate
   formula `evaluation_monodromyMap` and step 1 give the claim.
4. `hasRationalGeometricTorsion_of_rationalMonodromy_eq_one`: let `x` be an
   `ℓ ^ ν`-torsion point over `closurePoint L`. By `mem_torsionPoints` and
   `mem_levelGroup` it is a point `y` of the torsion level. Let `k` be the
   corresponding point of the scheme-theoretic kernel of multiplication by `ℓ ^ ν`,
   given by the inverse of `GroupScheme.Tate.kernelLevelEquiv`. The finite étale
   cover `torsionCover torsionFiniteEtale B (ℓ ^ ν) _ (hu ν)` is this kernel, and
   `kernelPoint_levelMonodromy` expresses the action of `g` on `k` in the fibre of
   that cover through `levelMonodromy`; by step 3, `k` is fixed by the whole
   fundamental group. Since `Spec L` is connected and locally noetherian,
   `sectionOfFixedGeometricLift` gives a section `σ` of the kernel over `Spec L`
   whose restriction to the geometric point is `k`. The required `L`-point is
   `σ` followed by the kernel inclusion: it is a section of `B` by the structure map
   equation of the inclusion, and its restriction to the geometric point is the
   restriction of `k` followed by the inclusion, which is `x` by
   `GroupScheme.kernelPointsEquiv_val`.
