# Reductions of free representations

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.FreeRestrictScalars`
(`powSMul_repRestrictScalars_eq_zero`, `freeOverPowQuotient_repRestrictScalars`,
`freeOverPowQuotient_of_iso`) and `Langlands.Cohomology.DivisibleSystem.Reduction`
(`mono_powSMul_one_iff_isSMulRegular`, `reductionSystem`). Through their
imports it uses `powSMul`, `comp_powSMul` and `DivisibleSystem`
(`Langlands.Cohomology.DivisibleSystem`), `powSMul_hom_apply`,
`FreeOverPowQuotient`, `homSystem_map_surjective_of_freeOverPowQuotient` and
`isMittagLeffler_homSystem_of_freeOverPowQuotient`
(`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`), `homSystem`
(`Langlands.Cohomology.DivisibleSystem.HomSystem`), and `repRestrictScalars`
with the local instance `restrictScalarsModule`
(`Langlands.Cohomology.DivisibleSystem.ScalarExtension`). From Mathlib it uses
`MonoidAlgebra.map` (with `map_single` and `map_surjective`),
`MonoidAlgebra.ofCoeff`, `MonoidAlgebra.coeff_injective`,
`MonoidAlgebra.induction_linear`, `Finsupp.mapRange` (with
`mapRange.addMonoidHom` and `mapRange_surjective`), `Finsupp.induction_linear`,
`Representation.free` and `Representation.free_single_single`,
`Representation.free_asModule_free`, `Representation.finsuppLEquivFreeAsModule`,
`Rep.free`, `Rep.ofHom`, `Rep.epi_iff_surjective`, `Rep.toModuleMonoidAlgebra`,
`Functor.preimageIso`, `LinearEquiv.toModuleIso`, `Module.Free.chooseBasis`,
`RestrictScalars.addEquiv` and `RestrictScalars.addEquiv_map_smul`,
`Ideal.mem_span_singleton'`, `Ideal.Quotient.eq_zero_iff_mem`,
`Ideal.Quotient.mk_surjective`, `ShortComplex.exact_map_iff_of_faithful`,
`ShortComplex.moduleCat_exact_iff`, `ShortComplex.Exact.gIsCokernel`,
`IsColimit.coconePointUniqueUpToIso`, `cokernel.mapIso` and `IsSMulRegular`.

## Conventions

`ℓ` and `m` are natural numbers, `R` is a commutative ring and `G` a monoid.
`(ℓ ^ m)` denotes the ideal `Ideal.span {((ℓ : R) ^ m)}` of `R` and
`R ⧸ (ℓ ^ m)` the quotient ring. For a commutative ring `k`, `k[G]` is the
monoid algebra `MonoidAlgebra k G`; `α →₀ k[G]` is the free `k[G]`-module on a
type `α`, and `Rep.free k G α` is the free representation on it, with `G`
acting by left multiplication on every coefficient
(`Representation.free k G α`). "`P` is free over `k[G]`" means
`Module.Free (MonoidAlgebra k G) P.ρ.asModule`.

`powSMul ℓ m X` is the published endomorphism "multiplication by `ℓ ^ m`" of an
object `X`; for a representation its underlying map is `x ↦ ℓ ^ m • x`.
`repRestrictScalars R S G : Rep S G ⥤ Rep R G` is the published restriction of
scalars along an algebra `R → S`, with the same additive group and operators.
The published predicate `FreeOverPowQuotient ℓ m P`, for `P` in `Rep R G`,
states that `P` is killed by `ℓ ^ m` and is free over `(R ⧸ (ℓ ^ m))[G]`; it
formalizes Harris's "free `𝒪/ℓ^m𝒪[Γ]`-module" with `𝒪 = R`. The published
`reductionSystem ℓ L` is the `ℓ`-divisible system whose level `m` is
`cokernel (powSMul ℓ m L)`, written `L / ℓ ^ m L`; it is defined when
multiplication by `ℓ` is a monomorphism on `L` (instance argument
`[Mono (powSMul ℓ 1 L)]`).

Representations of the first section have carriers in the universe
`max w u v`, where `α : Type w`, `R : Type u` and `G : Type v`; this is the
universe of `α →₀ R[G]`. Every universe at least `max u v` has this form.

## Reduction of coefficients (namespace `Langlands.Cohomology.DivisibleSystem`)

`α` is a type.

- `coeffReduction ℓ m : R[G] →+ (R ⧸ (ℓ ^ m))[G]` reduces every coefficient
  modulo `ℓ ^ m` (`MonoidAlgebra.map` of the quotient map).
  `coeffReduction_coeff` states that the coefficient at `g` of the image is the
  class of the coefficient at `g`; `coeffReduction_single` that `single g r`
  goes to `single g` of the class of `r`.
- `freeReductionAddHom ℓ m α : (α →₀ R[G]) →+ (α →₀ (R ⧸ (ℓ ^ m))[G])` applies
  `coeffReduction ℓ m` to every component (`Finsupp.mapRange`). Lemmas:
  `freeReductionAddHom_coeff` (coefficients are reduced),
  `freeReductionAddHom_single` (value on `single a (single h r)`) and
  `freeReductionAddHom_free`: reduction commutes with the action of every
  `g : G` (`Representation.free`). Proof by induction on finitely supported
  functions and on elements of the monoid algebra; on
  `single a (single h r)` both sides are `single a (single (g * h) r̄)`, with
  `r̄` the class of `r` (`Representation.free_single_single`).
- `freeReductionLinearMap ℓ m α` is `freeReductionAddHom ℓ m α` as an
  `R`-linear map into `RestrictScalars R (R ⧸ (ℓ ^ m)) (α →₀ (R ⧸ (ℓ ^ m))[G])`.
  It is additive because `freeReductionAddHom` is. For `R`-linearity, compare
  coefficients: the coefficient of `r • x` is `r * c`, whose class is the
  image of `r` in `R ⧸ (ℓ ^ m)` times the class of `c`, which is the action of
  `r` on the restriction of scalars (`RestrictScalars.addEquiv_map_smul`).
- `freeReduction ℓ m α : Rep.free R G α ⟶ (repRestrictScalars R (R ⧸ (ℓ ^ m)) G).obj (Rep.free (R ⧸ (ℓ ^ m)) G α)`
  (the entry declaration) is this linear map as a morphism in `Rep R G`. It
  commutes with the operators of `G` by `freeReductionAddHom_free`.
  `freeReduction_hom_apply` states that its underlying map is
  `freeReductionLinearMap ℓ m α`.

## Exactness and the cokernel

- `powSMul_comp_freeReduction`: multiplication by `ℓ ^ m` followed by
  `freeReduction ℓ m α` is zero. By naturality (`comp_powSMul`) it equals
  `freeReduction ℓ m α` followed by multiplication by `ℓ ^ m` on the target,
  which is zero (`powSMul_repRestrictScalars_eq_zero`).
- `freeReduction_surjective`: the underlying map is surjective, since the
  quotient map `R → R ⧸ (ℓ ^ m)` is surjective
  (`Ideal.Quotient.mk_surjective`, `MonoidAlgebra.map_surjective`,
  `Finsupp.mapRange_surjective`). The instance `Epi (freeReduction ℓ m α)`
  follows (`Rep.epi_iff_surjective`).
- `powDiv ℓ m c` is an auxiliary choice: for nonzero `c` in `(ℓ ^ m)`, some
  `d` with `d * ℓ ^ m = c` (`Ideal.mem_span_singleton'`, chosen with
  `Classical.choose`), and `0` otherwise. `powDiv_zero` states
  `powDiv ℓ m 0 = 0`, and `pow_mul_powDiv` that `ℓ ^ m * powDiv ℓ m c = c`
  for `c` in `(ℓ ^ m)`. The value `0` at `0` makes `powDiv ℓ m` applicable
  coefficientwise to finitely supported functions.
- `exists_pow_smul_of_freeReduction_eq_zero`: if `x : α →₀ R[G]` has zero
  reduction, then `x = ℓ ^ m • y` for some `y`. All coefficients of `x` lie
  in `(ℓ ^ m)` (`Ideal.Quotient.eq_zero_iff_mem`), and `y` is obtained by
  applying `powDiv ℓ m` to every coefficient (`Finsupp.mapRange`,
  `MonoidAlgebra.ofCoeff`); coefficientwise, `ℓ ^ m • y = x` is
  `pow_mul_powDiv`.
- `freeReductionComplex ℓ m α` is the short complex in `Rep R G` formed by
  `powSMul ℓ m (Rep.free R G α)` and `freeReduction ℓ m α`, and
  `freeReductionComplex_exact` states that it is exact. Exactness is tested
  after the faithful forgetful functor to `ModuleCat R`
  (`ShortComplex.exact_map_iff_of_faithful`), where it means that every
  element killed by the second map is in the image of the first
  (`ShortComplex.moduleCat_exact_iff`); this is the previous lemma, since the
  first map is `x ↦ ℓ ^ m • x` (`powSMul_hom_apply`).
- `cokernelFreeIso ℓ m α`: an isomorphism from
  `cokernel (powSMul ℓ m (Rep.free R G α))` to the restriction of scalars of
  `Rep.free (R ⧸ (ℓ ^ m)) G α`. Since the short complex is exact and its
  second map is an epimorphism, the second map is a cokernel of the first
  (`ShortComplex.Exact.gIsCokernel`); the isomorphism is the comparison of
  the two cokernels (`IsColimit.coconePointUniqueUpToIso`).
  `cokernelπ_cokernelFreeIso_hom` states that the projection to the cokernel
  followed by this isomorphism is `freeReduction ℓ m α`.
- `freeOverPowQuotient_cokernel_powSMul_free ℓ m α`: the cokernel of
  multiplication by `ℓ ^ m` on `Rep.free R G α` satisfies
  `FreeOverPowQuotient ℓ m`. The representation `Rep.free (R ⧸ (ℓ ^ m)) G α`
  is free over `(R ⧸ (ℓ ^ m))[G]` (`Representation.free_asModule_free`), so
  its restriction of scalars satisfies the predicate
  (`freeOverPowQuotient_repRestrictScalars`), which transfers along
  `cokernelFreeIso` (`freeOverPowQuotient_of_iso`).
- `isSMulRegular_free α hℓ`: if `(ℓ : R)` is a non-zero-divisor on `R`
  (`hℓ : IsSMulRegular R (ℓ : R)`), it is a non-zero-divisor on
  `α →₀ R[G]`: compare coefficients. `mono_powSMul_free α hℓ`: then
  multiplication by `ℓ` is a monomorphism on `Rep.free R G α`
  (`mono_powSMul_one_iff_isSMulRegular`).

## Representations free over `R[G]`

`P` is a representation in `Rep.{max w u v} R G` that is free over `R[G]`
(instance argument).

- `isoFreeOfFree P`: an isomorphism from `P` to `Rep.free R G ι`, where `ι` is
  the index type of the basis of `P` over `R[G]` chosen by
  `Module.Free.chooseBasis`. The basis gives an `R[G]`-linear equivalence from
  `P.ρ.asModule` to `ι →₀ R[G]`, composed with
  `Representation.finsuppLEquivFreeAsModule`; the isomorphism in `Rep R G` is
  its preimage under the full and faithful functor
  `Rep.toModuleMonoidAlgebra` to `R[G]`-modules (`Functor.preimageIso`).
- `freeOverPowQuotient_cokernel_powSMul_of_free ℓ m P`: the cokernel of
  multiplication by `ℓ ^ m` on `P` satisfies `FreeOverPowQuotient ℓ m`. The
  isomorphism `isoFreeOfFree P` commutes with multiplication by `ℓ ^ m`
  (`comp_powSMul`), so it induces an isomorphism of the cokernels
  (`cokernel.mapIso`), and the predicate transfers from the previous section
  (`freeOverPowQuotient_of_iso`).
- `mono_powSMul_of_free P hℓ`: if `(ℓ : R)` is a non-zero-divisor on `R`,
  multiplication by `ℓ` on `P` is a monomorphism. It is the conjugate of
  multiplication by `ℓ` on `Rep.free R G ι` by `isoFreeOfFree P`
  (`comp_powSMul`), a composite of monomorphisms by `mono_powSMul_free`.

## The reduction system of a free representation

`P` is as in the previous section, multiplication by `ℓ` on `P` is a
monomorphism (instance argument; `mono_powSMul_of_free` provides it when
`(ℓ : R)` is a non-zero-divisor on `R`), and `W` is an `ℓ`-divisible system in
`Rep R G`.

- `freeOverPowQuotient_reductionSystem_obj P m`: level `m` of
  `reductionSystem ℓ P`, which is `P / ℓ ^ m P` by definition, satisfies
  `FreeOverPowQuotient ℓ m`.
- `homSystem_reductionSystem_map_surjective P W φ`: the transition maps of
  the published inverse system `homSystem R (reductionSystem ℓ P) W`, with
  value `Hom(P / ℓ ^ m P, W m)` at `m`, are surjective
  (`homSystem_map_surjective_of_freeOverPowQuotient`).
- `isMittagLeffler_homSystem_reductionSystem P W`: this inverse system
  satisfies the Mittag-Leffler condition
  (`isMittagLeffler_homSystem_of_freeOverPowQuotient`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- proof of Proposition 4.10, printed p.312 (one-based PDF page 14): "Since
  `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
  `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are
  surjective for all `m`."
- §4, printed p.311 (one-based PDF page 13): "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any
  `m`. Then `𝓛_m` forms an inverse system of `𝒪`-modules".

The published Hom-system results of the FreeTorsionProjective module derive
surjectivity of the maps (4.10.3) from the freeness of every level of the
source system over `(R ⧸ (ℓ ^ m))[G]`. This module supplies systems with that
property: the reductions `P / ℓ ^ m P` of a representation `P` free over
`R[G]`, assembled by the published `reductionSystem`, which formalizes
Harris's passage from `𝓛` to the inverse system `𝓛_m` for an arbitrary
object. Harris applies that passage to a lattice `𝓛`, which need not be free
over `𝒪[Γ]`; the results here concern free `P` only. That reduction
modulo `ℓ ^ m` preserves freeness, and that a non-zero-divisor of `R` is one on a free module, are standard facts. Harris
does not state them in this form; the formulation and all proofs are ours,
and `powDiv` is an auxiliary choice made for the proofs. The module is
derived.

## Scope

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` or
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are reductions of representations free over
`𝒪[S(ẽ)/H_p]`, and it does not identify `𝓛 ⊗_𝒪 𝒪_m` with `𝓛 / ℓ^m 𝓛`.
Everything concerns the categories `Rep` of representations of abstract
monoids, not categories of smooth representations.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
