# Flatness, unramifiedness and étaleness of bounded affinoid maps at points

Author: Worker 36.

This module defines when a bounded algebra map `f : R → S` is flat,
unramified or étale at a point `y` of the spectrum of `S`. These are the
pointwise conditions that Berkovich's definitions of flat and étale
quasifinite morphisms impose on finite morphisms of affinoid spaces. The
module compares unramifiedness with Mathlib's notion at a prime and proves
the identity and composition laws.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- §2.1, printed p.38 / PDF p.35: for a point `x` of `X = 𝓜(𝒜)`, `℘_x` is the
  prime ideal of `𝒜` corresponding to `x`, "the kernel of the seminorm on `𝒜`
  which corresponds to the point `x`";
- §3.2, printed p.58 / PDF p.55: a morphism of good spaces is flat at `y` if
  `𝒪_{Y,y}` is a flat `𝒪_{X,φ(y)}`-algebra. Proposition 3.2.1: "A finite
  morphism of k-affinoid spaces `φ : Y = 𝓜(ℬ) → X = 𝓜(𝒜)` is flat at a point
  `y ∈ Y` if and only if `ℬ_{℘_y}` is a flat `𝒜_{℘_x}`-algebra, where
  `x = φ(y)`. In particular, `φ` is flat if and only if `ℬ` is a flat
  `𝒜`-algebra";
- §1.3, printed p.25 / PDF p.22: for a coherent sheaf `F = 𝒪_X(M)` on an
  affinoid space, `Supp(F)` is the support of the annihilator of `M`;
- §3.3, printed p.63 / PDF p.60. Lemma 3.3.5 and its proof: for a finite
  morphism of k-affinoid spaces `𝓜(ℬ) → 𝓜(𝒜)`, the sheaf `Ω_{Y/X}` is
  defined by the module of differentials `Ω_{ℬ/𝒜}`. Proposition 3.3.7(a)⇔(b):
  a quasifinite morphism is unramified at `y` if and only if the support of
  `Ω_{Y/X}` does not contain `y`. Definition 3.3.4: étale means unramified and
  flat.

`IsFlatAtPoint` takes the characterization of Proposition 3.2.1 as its
definition. The definition through the local rings `𝒪_{Y,y}` and the proof of
the equivalence (which uses the faithful flatness of `𝒪_{X,x}` over `𝒜_{℘_x}`,
Berkovich's Theorem 2.1.4) are not formalized. `IsUnramifiedAtPoint`
transcribes "`y ∉ Supp Ω`" with the algebraic module of differentials and the
annihilator definition of the support. Lemma 3.3.5 identifies this module
with Berkovich's `Ω_{Y/X}` only for finite morphisms. Both conditions are
meant for finite Banach maps; the definitions do not assume finiteness.
`IsEtaleAtPoint`, the conjunction, is derived: it is the pointwise content of
Definition 3.3.4 for finite morphisms of affinoid spaces.

## Primes of points

The Library's `BanachSpectrum.kernel y` is the kernel `{a | y a = 0}` of the
seminorm `y`, and `BanachSpectrum.kernel_isPrime` proves that it is prime.
This module registers that proof as an instance, `BanachSpectrum.kernel.isPrime`.
For `f : BoundedAlgHom K R S`, `kernel_comap` shows that the kernel of the
pulled-back point `BanachSpectrum.comap f y` is the preimage of the kernel of
`y`. Both are `{a | y (f a) = 0}`.

## Definitions

Let `f : BoundedAlgHom K R S` and `y : BanachSpectrum S`, and write `x` for
`BanachSpectrum.comap f y`.

- `IsFlatAtPoint f y`: Mathlib's local homomorphism
  `Localization.localRingHom (kernel x) (kernel y) f` from `R_{℘_x}` to
  `S_{℘_y}` is flat (`RingHom.Flat`).
- `IsUnramifiedAtPoint f y`: with `S` an `R`-algebra through `f`, the
  annihilator of the Kähler differentials `Ω[S⁄R]` is not contained in
  `kernel y`.
- `IsEtaleAtPoint f y`: both.

## Results

- `isUnramifiedAtPoint_iff_isUnramifiedAt`: if `f` is of finite type, then
  `IsUnramifiedAtPoint f y` holds if and only if Mathlib's
  `Algebra.IsUnramifiedAt R (kernel y)` holds, that is, the localization
  `S_{℘_y}` is formally unramified over `R`. Mathlib's
  `unramifiedLocus_eq_compl_support` describes the unramified locus as the
  complement of the support of `Ω[S⁄R]`. The module `Ω[S⁄R]` is finite
  (`KaehlerDifferential.finite`), so membership in its support is containment
  of the annihilator (`Module.mem_support_iff_of_finite`).
- `isFlatAtPoint_of_flat`: flat maps are flat at every point
  (`RingHom.Flat.localRingHom`). This is the easy direction of the "in
  particular" of Proposition 3.2.1.
- `isUnramifiedAtPoint_of_formallyUnramified`: if `Ω[S⁄R]` vanishes, its
  annihilator is the unit ideal, which a prime ideal does not contain.
- `AlgebraicallyFiniteEtale.isEtaleAtPoint`: the published algebraic finite
  étale condition gives flatness and formal unramifiedness
  (`algebraicallyFiniteEtale_iff`), hence étaleness at every point.
  `isEtaleAtPoint_id`, `isFlatAtPoint_id` and `isUnramifiedAtPoint_id` treat
  the identity.
- `IsFlatAtPoint.comp`: if `g : S → T` is flat at `z` and `f : R → S` is flat
  at `BanachSpectrum.comap g z`, then `g ∘ f` is flat at `z`. Mathlib's
  `Localization.localRingHom_comp` writes the local homomorphism of the
  composite as the composite of the local homomorphisms, and flat ring maps
  compose.
- `IsUnramifiedAtPoint.comp`: the same statement for unramifiedness, for maps
  of finite type. Both hypotheses and the conclusion are converted by the
  comparison theorem. The prime of `z` lies over the prime of
  `BanachSpectrum.comap g z` by `kernel_comap`, so Mathlib's
  `Algebra.IsUnramifiedAt.comp` applies.
- `IsEtaleAtPoint.comp` combines the two.

## Scope

No completeness, nontrivial valuation or affinoid hypothesis is used. The
following remain further work: the local-ring definition of flatness and
its equivalence with `IsFlatAtPoint`; Berkovich's sheaf `Ω_{Y/X}` for
non-finite morphisms; and the passage from these pointwise conditions to flat,
unramified and étale morphisms of analytic spaces.
