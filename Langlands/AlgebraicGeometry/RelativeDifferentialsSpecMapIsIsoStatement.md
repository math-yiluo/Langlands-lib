# Invertibility of the canonical differential comparison on spectra

`Langlands.Scheme.RelativeDifferentialsSpecMapIsIsoStatement.{u}` is the
proposition that, for every `R A : CommRingCat.{u}` and every `Algebra R A`,
the existing morphism `Langlands.Scheme.relativeDifferentialsSpecMap R A`
is `CategoryTheory.IsIso`.

Write \(\varphi : R \to A\) for `algebraMap R A`, \(X=\operatorname{Spec} A\),
\(S=\operatorname{Spec} R\), and \(f=\operatorname{Spec}(\varphi):X\to S\).
The map whose invertibility is asserted is

\[
c_{R,A}:\widetilde{\Omega_{A/R}}\longrightarrow\Omega_{X/S}.
\]

Its source is Mathlib's
`tilde (ModuleCat.of A (KaehlerDifferential R A))`; its target is the
existing sheafification-based
`relativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap R A)))`.
The statement uses this exact map and these exact objects.

The already proved lemma `relativeDifferentialsSpecMap_adjoint_D`
expresses the commutativity of the following diagram of underlying sets,
where \(c_{R,A}^{\sharp}\) is the adjoint under the tilde/global-sections
adjunction:

\[
\begin{array}{ccc}
A & \xrightarrow{D_{A/R}} & \Omega_{A/R}\\
\big\downarrow{\scriptstyle(\Gamma\mathrm{SpecIso}_A)^{-1}}
&& \big\downarrow{\scriptstyle c_{R,A}^{\sharp}}\\
\Gamma(X,\mathcal O_X) & \xrightarrow{d_{X/S}(X)}
& \Gamma(X,\Omega_{X/S}).
\end{array}
\]

For every open \(W\subseteq X\) and every \(a\in A\),
`relativeDifferentialsSpecMap_app_toOpen_D` already proves

\[
c_{R,A}(W)\bigl(\operatorname{tilde.toOpen}_W(D_{A/R}a)\bigr)
=d_{X/S}(W)\bigl((\Gamma\mathrm{SpecIso}_A)^{-1}(a)|_W\bigr).
\]

This formula concerns restrictions of global functions.
`relativeDifferentialsSpecMap_unique` already proves that the displayed
adjoint compatibility for all \(a\) uniquely determines \(c_{R,A}\).
These are results imported from `RelativeDifferentialsSpecMap`; this
module adds only the proposition asserting its invertibility.

The provenance is a derived sheaf-level formulation of Stacks Project,
Morphisms §29.33, Lemmas 29.33.4–5 (tags 01UO and 01UT, in section tag
01UM). Lemma 29.33.4 identifies relative sheaf derivations with algebraic
derivations on global sections for an arbitrary module sheaf on a spectrum.
Together with the sheaf and algebraic universal properties and the tilde
adjunction, it gives the natural Hom-set comparison that motivates
invertibility of this specific map. Lemma 29.33.5 states the compatible
comparison on sections of affine opens; its displayed conclusion is a
module isomorphism, while the present proposition concerns the canonical
sheaf morphism on whole spectra.

Registered original: `stacks-relative-differentials-internal-hom-2026-10-21`,
folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
file `01UM.html`, Lemmas 29.33.4–5. The original passage and the correction
concerning premature use of quasi-coherence in Lemma 29.33.5 were checked.

There is no finiteness, smoothness, reducedness, nonzero-ring, nonempty-spectrum,
or quasi-coherence hypothesis. The universe parameter is arbitrary; the
quantifiers include zero rings. This module contains no proof of the
invertibility proposition. Its proof is a separate exact-target obligation.
