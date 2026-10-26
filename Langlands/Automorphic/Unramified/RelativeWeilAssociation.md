# Weak association of relative Weil representations with unramified spectra

Worker 35 authored this definition unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`.

The module defines when a finite-dimensional complex representation `S` of
the published relative Weil group `W_{E/F} = RelativeWeilGroup c F E` is
weakly associated with an unramified spectral system, and with an actual full
cuspidal class of `GL_{r+1}` over `F`. The comparison runs through the local
maps `ι : W_{F_v} → W_{E/F}` characterized by the published predicate
`IsLocalRelativeWeilMap`. No local map, representation, spectral system or
cuspidal class is constructed. No existence, uniqueness or rigidity
assertion is made, and no comparison with the absolute Weil group `W_F` is
made.

## Objects

Fix number fields `F E : Type u` with `[Algebra F E]` and `[IsGalois F E]`,
a class family `c : FundamentalClass.ClassFamily.{u}`, and a finite place
`v : Langlands.Global.FinitePlace F`. The representation is
`S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)`, with an
independent carrier universe `uV`.

- `W_{F_v}` is the published `Weil.Local.localWeilGroup (padicField v)`, with
  its actual inertia subgroup `Weil.Local.localInertia (padicField v)` and the
  published geometric Frobenius lift
  `Fr = Weil.Local.localGeometricFrobenius (padicField v)`. That lift is one
  element of geometric degree `+1`, chosen from proved degree surjectivity.
- The places of `E` above `v` are the published type `FinitePlacesAbove E v`.
  For `w` in it, `IsLocalRelativeWeilMap v w.1 e ι` is the published
  characterization of a map `ι : W_{F_v} →ₜ* W_{E/F}` attached to `w` and to a
  geometrically normalized local reciprocity candidate
  `e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1)`.
- A spectral system `s : SpectralSystem (FinitePlace F) n` is the published
  numerical structure: a finite exceptional set `s.exceptional` and, at each
  `v ∉ s.exceptional`, a multiset of `n` nonzero complex numbers `z_i`.
  `s.eulerPolynomial v hs` is `∏ (1 - z_i X)`.
- `S.IsContinuous` is the published continuity predicate: the action map is
  continuous into `Module.End ℂ S` with its module topology, which is the
  usual finite-dimensional topology. The topology of `W_{E/F}` is the
  published `ClassExtension` topology.

## Declarations

- `localComponent S ι` is `S ∘ ι`, the published
  `FiniteRepresentation.restrict ι.toMonoidHom S`, on the original carrier of
  `S`. `localComponent_representation` states by `rfl` that it acts on `g` as
  `S (ι g)`.
- `localComponent_isContinuous` proves that `S ∘ ι` is continuous when `S`
  is. It applies the published `FiniteRepresentation.isContinuous_restrict`
  to the continuity of `ι`.
- `localPairClass S ι` is the class, in the published type
  `Correspondence.LocalPairClass (padicField v)`, of the Weil–Deligne
  representation with zero monodromy built from `S ∘ ι` and the actual local
  norm character. It is not used by the predicates below. It is provided so
  that later gamma-factor statements can apply the published Weil-side pair
  factors to the local components.
- `localEulerPolynomial S ι` is `LocalFactor.eulerPolynomial (S (ι Fr))`,
  that is `det(1 - X S(ι Fr))` on the whole carrier of `S`. When `S ∘ ι` is
  unramified, inertia acts trivially, so this is the Euler denominator of
  `S ∘ ι`. The value does not then depend on the chosen lift `Fr`, because two
  lifts of degree one differ by an inertia element.
- `IsUnramifiedMatchAt S v P` holds when, for every place `w` of `E` above
  `v`:
  1. some pair `(e, ι)` satisfies `IsLocalRelativeWeilMap v w.1 e ι`, and
  2. every pair `(e, ι)` satisfying it makes `S ∘ ι` unramified, meaning that
     every element of `localInertia` acts as the identity, and gives
     `localEulerPolynomial S ι = P`.
- `IsWeaklyAssociated S s`, for `s : SpectralSystem (FinitePlace F) n`, is the
  conjunction of `S.IsContinuous`, `S.rank = n`, and

  `∀ᶠ v in Filter.cofinite, ∃ hs : v ∉ s.exceptional,
    IsUnramifiedMatchAt S v (s.eulerPolynomial v hs)`.

  `S.rank` is `Module.finrank ℂ S`.
- `isWeaklyAssociated_iff_exists_finset` restates the cofinite condition as
  one finite set `T` with `s.exceptional ⊆ T` such that
  `IsUnramifiedMatchAt S v (s.eulerPolynomial v _)` holds for every
  `v ∉ T`. The forward proof takes `T` to be the finite failure set together
  with `s.exceptional`. The reverse proof uses `T.eventually_cofinite_notMem`.
- `isWeaklyAssociated_restrict_iff` proves that enlarging the exceptional set
  of `s` by the published `SpectralSystem.restrict` does not change the
  relation. The restricted system has the same eigenvalues off the larger
  set, and a finite set is cofinitely avoided.

### Invariance under equivalence

Let `φ : FiniteRepresentation.Equiv S S'`, where `S'` has an independent
carrier universe `uW`.

- `representation_eq_conj_of_equiv` proves
  `S' g = φ.toLinearEquiv.conj (S g)` for every `g`. Each point is the
  intertwining identity of `φ` at `φ⁻¹ b`.
- `isContinuous_of_equiv` proves that continuity transfers from `S` to `S'`.
  By the previous lemma, the action map of `S'` is the action map of `S`
  followed by conjugation, which is a linear map between finite-dimensional
  modules and hence continuous for the module topologies
  (`IsModuleTopology.continuous_of_linearMap`).
- `localEulerPolynomial_eq_of_equiv` applies the published
  `LocalFactor.eulerPolynomial_conj`.
- `localComponent_isUnramified_of_equiv` transfers triviality on inertia
  through the intertwining identity.
- `IsUnramifiedMatchAt.of_equiv`, `IsWeaklyAssociated.of_equiv` and
  `IsWeaklyAssociatedClass.of_equiv` combine these. The rank uses the
  published `FiniteRepresentation.rank_eq_of_equiv`.

### Attachment to cuspidal classes

Under the explicit assumption `[CompactSpace (AdeleQuotient F)]`, which the
published automorphic-form constructions require, take
`π : Automorphic.CuspidalOperatorRealization.IsoClass F r`, an actual full
cuspidal class of `GL_{r+1}` over `F`.

- `IsWeaklyAssociatedClass S π` means that some spectral system `s` of rank
  `r + 1` satisfies the published
  `CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{u, uP} π s` and
  `IsWeaklyAssociated S s`. The universe parameter order is
  `.{u, uV, uP}`. The universe `uP` of the presentation's local factors is
  independent of the carrier universe `uV` of `S`.
- `isWeaklyAssociatedClass_isoClass_iff` expresses the relation at any
  actual representative `T` of the class, as the existence of a
  `CuspidalSpectralPresentation.{u, uP} T` whose exported system is weakly
  associated with `S`. It applies the published `hasSpectralSystem_iff`.

`HasSpectralSystem` is the current published attachment relation. Its witness
supplies an actual presentation of the class: smooth local factors and a
genuine tensor equivalence onto a nonzero slice of its form image, with
irreducible, admissible unramified local factors away from a finite set, on
whose spherical fixed spaces the standard Hecke operators act by the scalars
`Unramified.standardHeckeScalar`. The system is the one exported by that
presentation. A numerical system alone does not determine a class, and no
uniqueness of presentations is used or asserted.

## Source correspondence

The definition follows Henniart 2000, §2.2, printed p.444 (PDF p.6),
registered as `henniart-2000-simple-proof`. For a continuous complex
representation `S` of degree `n` of `W_F` and an automorphic representation
`Π` of `GL_n(𝔸_F)`, Henniart calls `S` and `Π` associated if, for almost
every finite place `v` at which the local components `S_v` and `Π_v` are
unramified, `L(S_v, s) = L(Π_v, s)`. This is the unramified Langlands
correspondence at almost every place. The same notion appears in §1.7,
printed p.442 (PDF p.4), for the cuspidal representations constructed in §3.

The formalization differs from the source in the following derived choices.

1. **Relative Weil group.** Henniart uses the absolute Weil group `W_F`.
   Here `S` is a representation of the finite-level group `W_{E/F}` at a
   supplied class family `c`. A representation of `W_F` factoring through
   `W_{E/F}` would give such an `S`, but the library has no absolute global
   Weil group. The absolute group and the comparison between the two levels
   belong to Worker 2's construction. No claim is made that every
   representation used in Henniart's proof factors through some `W_{E/F}`.
2. **Local components.** Henniart's `S_v` is the restriction of `S` along
   `W_{F_v} → W_F`, which is defined up to conjugacy. Here the local
   components are `S ∘ ι` for the maps `ι` characterized by
   `IsLocalRelativeWeilMap`, at every place `w` above `v` and for every
   reciprocity candidate `e`. The predicate requires matching for all such
   pairs, which needs no conjugacy or uniqueness theorem. The published
   conjugacy statement (`LocalRelativeWeilMapConjugacyStatement`, unproved)
   would make the choice of `ι` for fixed `w` and `e` irrelevant, because
   Euler polynomials and unramifiedness are conjugation invariant.
3. **No vacuous matching.** The predicate also requires that some pair
   `(e, ι)` exists for every `w` above `v`. Without this, the matching
   condition would hold vacuously when no local map exists, for instance for
   a class family `c` that is not the fundamental class. The published
   statement `LocalRelativeWeilMapExistenceStatement` (unproved) supplies
   such maps under its fundamental-class hypotheses.
4. **One cofinite set.** Henniart restricts to the finite places where both
   `S_v` and `Π_v` are unramified and asks for equality at almost all of
   them. Here one cofinite set of places is required on which the spectrum
   is defined, `S ∘ ι` is unramified, and the Euler polynomials agree. The two
   forms agree when `S` is unramified at almost every place and the class is
   unramified off a finite set. The first is a theorem about continuous
   representations, and the second is part of the presentation. Neither is
   used or proved here; the predicate states the stronger, explicit form.
5. **Euler polynomials.** For unramified `S_v`, `L(S_v, s)` is
   `det(1 - q_v^{-s} S_v(Fr))^{-1}`. For `Π_v` unramified with Satake
   parameters `z_i`, `L(Π_v, s) = ∏ (1 - z_i q_v^{-s})^{-1}`. Equality of the
   two functions of `s` is equality of the polynomials in `X = q_v^{-s}`,
   because `s ↦ q_v^{-s}` takes every nonzero complex value. The predicate
   compares these polynomials directly.
6. **Normalizations.** The spectrum attached through `HasSpectralSystem` uses
   the published `HasSphericalHeckeSpectrum` normalization: the spherical
   subgroup has Haar mass one, and the characteristic function of the double
   coset of `diag(ϖ, …, ϖ, 1, …, 1)` with `i` uniformizers acts on spherical
   vectors by `q^{i(n-i)/2} e_i(z)`, using the positive square root of `q`.
   The operators are `π(f) = ∫ f(g) π(g) dg`. These are the Satake parameters
   for which `L(Π_v, s) = ∏ (1 - z_i q_v^{-s})^{-1}`. On the Weil side, `Fr`
   is a geometric Frobenius and `e` is geometrically normalized by condition 1
   of `IsLocalRelativeWeilMap`, so a uniformizer corresponds to a geometric
   Frobenius. This matches the unramified correspondence, under which an
   unramified character `χ` of `F_v^×` corresponds to the Weil character
   `χ ∘ τ` with value `χ(ϖ)` at a geometric Frobenius.
7. **Rank-one check.** Take `E = F`. Then `W_{F/F}` is the idele class group
   `C_F` through `inclusion`. The residue degree is one, so
   `completionWeilMap` sends an element `y` of degree one to a geometric
   Frobenius lift `y'`. By condition 3 of `IsLocalRelativeWeilMap`,
   `ι(y') = (inclusion (i_v(e[y])))⁻¹`, and by condition 1 `e[y]` is a
   uniformizer `ϖ_v` at `v`. Let `χ` be a Hecke character unramified at `v`.
   By the integrated action above, its spectrum at `v` is `χ_v(ϖ_v)`. Let `S`
   be a character with `S ∘ inclusion = χ⁻¹`. When `S ∘ ι` is unramified,
   `S(ι Fr) = S(ι y') = χ_v(ϖ_v)`, so `S` is associated with `χ`.
   Equivalently `S = χ ∘ τ_F`, where `τ_F(inclusion x) = x⁻¹`. Under the sign
   translation explained in the published `LocalRelativeWeilMap.md`, this
   `τ_F` is Tate's geometrically normalized reciprocity map. This agrees with
   Henniart's `det S = ω_Π ∘ τ_F` in §2.2. The check is an explanation, not a
   formal proof.
8. **Continuity and rank.** Henniart's `S` is continuous of degree `n`. The
   library's `FiniteRepresentation` carries no continuity, so
   `S.IsContinuous` is a conjunct, and the degree is the explicit equation
   `S.rank = n`.
9. **Cuspidal classes.** Henniart's `Π` is any automorphic representation.
   `IsWeaklyAssociatedClass` treats only the actual full cuspidal classes
   with a published spectral presentation. Isobaric or other noncuspidal
   automorphic representations are not covered.

## Scope

This module asserts no theorem beyond the elementary lemmas above. In
particular it does not assert:

- that a weakly associated class or representation exists for a given `S`
  or `π`;
- strong multiplicity one or the Jacquet–Shalika rigidity used by Henniart
  for uniqueness of `Π`, or the Chebotarev-type uniqueness of semisimple `S`;
- the consequences in Henniart §2.2 for duals, determinants and twists;
- any comparison of gamma, L or ε factors at ramified places (Henniart
  Theorem 2.3 and its corollaries), which are separate statement targets
  that will use `localPairClass`.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Section 2.2, printed p.444 (PDF p.6): the definition of association.
  Section 1.7, printed p.442 (PDF p.4): its use for cuspidal
  representations.
