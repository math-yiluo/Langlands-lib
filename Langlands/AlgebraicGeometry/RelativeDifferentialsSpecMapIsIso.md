# Invertibility of the canonical differential comparison on spectra: proof

The theorem `Langlands.Scheme.relativeDifferentialsSpecMapIsIso` proves
`Langlands.Scheme.RelativeDifferentialsSpecMapIsIsoStatement.{u}` for an
arbitrary universe `u`. For every `R A : CommRingCat.{u}` with `Algebra R A`,
the existing map

\[
c_{R,A} = \texttt{relativeDifferentialsSpecMap R A} :
\widetilde{\Omega_{A/R}} \longrightarrow \Omega_{X/S},
\qquad X = \operatorname{Spec} A,\ S = \operatorname{Spec} R,
\]

is shown to be an isomorphism by constructing an explicit two-sided inverse.
No quasi-coherence of the target is assumed, and there are no finiteness,
nonzero-ring or nonempty-spectrum hypotheses. Zero rings are included. All
auxiliary declarations live in the namespace
`Langlands.Scheme.SpecDifferentials`.

## Algebra: the localized universal derivation

For a submonoid \(P \subseteq A\), `localizedKaehlerEquiv R A P` is the
\(A_P\)-linear map \(\Omega_{A_P/R} \to (\Omega_{A/R})_P\). It is the inverse of
the `IsLocalizedModule.iso` of `KaehlerDifferential.map R R A (Localization P)`,
made linear over the localization by `LinearMap.extendScalarsOfIsLocalization`.
Mathlib supplies the needed `IsLocalizedModule` instance in
`Mathlib.RingTheory.Etale.Kaehler`. Composing it with the universal derivation of
\(A_P\) gives `localizedDerivation R A P`, an \(R\)-derivation
\(A_P \to (\Omega_{A/R})_P\). The lemma `localizedDerivation_algebraMap` says
that it sends \(a/1\) to \((D a)/1\). The quotient rule
`localizedDerivation_mk` gives

\[
\delta\!\left(\frac{a}{g}\right) = \frac{g\,Da - a\,Dg}{g^2}.
\]

The proof applies the Leibniz rule to \((a/g)\cdot(g/1) = a/1\) and multiplies
by \(1/g\).

## Sheaf: a derivation into the tilde of the differentials

At each point \(x\), `pointDerivation R A x` is the localized derivation at the
prime complement of \(x\). It is written on `LocalizedModule`, which is how
Mathlib's structure sheaf and `tilde` store stalk values. The lemmas
`pointDerivation_mk`, `_zero`, `_add` and `_mul` record the quotient rule,
additivity and the Leibniz rule.

`tildeDerivationApp R A U` applies `pointDerivation` pointwise to a section
\(s \in \Gamma(X, U)\). The result is a section of
`tilde (ModuleCat.of A (KaehlerDifferential R A))` over \(U\). Local
representability follows from the quotient rule: if \(s = r/t\) near \(x\),
then the image is \((t\,Dr - r\,Dt)/t^2\) there. This map is additive.

`tildeDerivation R A` packages these maps as a
`RelativeDerivation (Spec.map φ) (tilde Ω)`. The fields are checked as follows:

* Leibniz rule: pointwise, by `pointDerivation_mul`.
* Compatibility with restriction: definitional.
* Vanishing on functions pulled back from \(S\): pointwise. Such a function is
  locally \(\varphi(r)/\varphi(t)\), and the quotient rule together with
  `Derivation.map_algebraMap` gives \(0\).

The global formula `tildeDerivation_app_top` states that, for \(a \in A\),

\[
\texttt{tildeDerivation}(X)\bigl((\Gamma\mathrm{SpecIso}_A)^{-1} a\bigr)
= \operatorname{tilde.toOpen}_X(D a).
\]

## Uniqueness of relative derivations on a spectrum

`relativeDerivation_ext` proves that two relative derivations
\(d, d'\) of \(\mathcal O_X\) into any module sheaf \(M\) on \(X\) are equal
if they agree on all global functions \((\Gamma\mathrm{SpecIso}_A)^{-1} a\).
The proof has three steps.

1. By `app_restrict`, \(d\) and \(d'\) agree on restrictions of global
   functions to every open set.
2. On a basic open \(D(g)\), the section \(c = f/g\) satisfies
   \(c \cdot g|_{D(g)} = f|_{D(g)}\). The Leibniz rule gives
   \(g \cdot d(c) = g \cdot d'(c)\). Since \(g\) acts invertibly on sections over
   \(D(g)\) (`Scheme.Modules.isSMulRegular_of_le_basicOpen`), we get
   \(d(c) = d'(c)\).
3. Every section of \(\mathcal O_X\) over \(U\) is locally of the form \(f/g\)
   on basic opens covering \(U\) (`StructureSheaf.exists_const`). The sheaf
   property of \(M\) (`TopCat.Sheaf.eq_of_locally_eq'`) and step 2 conclude.

This argument works for an arbitrary module sheaf \(M\) and uses no
quasi-coherence.

## The inverse and the two identities

The inverse candidate is

\[
\psi = \texttt{specMapInv R A}
= \texttt{relativeDifferentialsDesc (Spec.map φ) (tildeDerivation R A)} :
\Omega_{X/S} \longrightarrow \widetilde{\Omega_{A/R}}.
\]

It is obtained from the published universal property of the relative
differential sheaf. By `relativeDifferentialsDesc_fac`, \(\psi\) sends
\(d_{X/S}(X)\bigl((\Gamma\mathrm{SpecIso}_A)^{-1}a\bigr)\) to
\(\operatorname{tilde.toOpen}_X(D a)\) (`specMapInv_app_D`).

* `specMap_comp_specMapInv`: \(c_{R,A} \gg \psi = \mathrm{id}\). Both sides are
  compared through the injective `tilde.adjunction.homEquiv`. By
  `Adjunction.homEquiv_naturality_right` and
  `relativeDifferentialsSpecMap_adjoint`, the left side becomes
  `relativeDifferentialsSpecLinearMap R A` followed by \(\Gamma(\psi)\). The
  right side becomes the adjunction unit \(\operatorname{tilde.toOpen}_X\)
  (`Adjunction.homEquiv_id`). These two \(A\)-linear maps out of
  \(\Omega_{A/R}\) are compared on the spanning set \(\{D a\}\)
  (`KaehlerDifferential.span_range_derivation`, `LinearMap.ext_on_range`).
  There `relativeDifferentialsSpecMap_adjoint_D` and `specMapInv_app_D` give
  the equality.
* `specMapInv_comp_specMap`: \(\psi \gg c_{R,A} = \mathrm{id}\). By
  `relativeDifferentials_hom_ext`, it suffices to compare postcompositions of
  the universal derivation. After `RelativeDerivation.postcomp_comp`,
  `relativeDifferentialsDesc_fac` and `RelativeDerivation.postcomp_id`, it
  remains to show that `(tildeDerivation R A).postcomp c_{R,A}` equals the
  universal derivation. By `relativeDerivation_ext`, this is checked on global
  functions. There `tildeDerivation_app_top` and
  `relativeDifferentialsSpecMap_app_toOpen_D` (with \(W = X\), where the
  restriction is the identity) give the equality.

Finally, `relativeDifferentialsSpecMapIsIso` packages \(\psi\) and the two
identities as `IsIso (relativeDifferentialsSpecMap R A)`.

## Provenance

The statement is the sheaf-level formulation of Stacks Project, Morphisms
§29.33, Lemmas 29.33.4–5 (tags 01UO and 01UT, section tag 01UM). Registered
source `stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`, file
`01UM.html`. The implemented route differs from the source in its details. It
does not establish bijectivity of `RelativeDerivation.specToAlgebra` for every
module sheaf. Instead it builds one concrete derivation into
\(\widetilde{\Omega_{A/R}}\), using localized Kähler differentials, and it
proves uniqueness of relative derivations on spectra from their values on global
functions. The inverse of \(c_{R,A}\) is then the morphism this concrete
derivation induces. The uniqueness step works for every module sheaf, so the
correction in the source about premature use of quasi-coherence does not apply
here.
