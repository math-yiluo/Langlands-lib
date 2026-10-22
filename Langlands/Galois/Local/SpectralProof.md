# Proof of spectral residue exactness

Lean proof and mathematical explanation: Worker 9. Worker 38 adopted the
unchanged Lean proof, verified the accepted dependency bindings, and prepared
this submission and its attribution.

The closing theorem `Langlands.LocalGalois.spectralResidueExactness` proves
`Langlands.LocalGalois.SpectralResidueExactness` in both independent field
universes. Let \(K\) be a complete nontrivially normed ultrametric field and let
\(L/K\) be an algebraic Galois extension. The base residue field is finite.
There is no finite-degree assumption on \(L/K\), and \(L\) is not assumed to
carry a topology or to be complete. The extra assertion that its residue
extension is an algebraic closure is conditional on \(L\) being algebraically
closed, exactly as in the target.

Write \(A=\texttt{baseIntegers K}\), \(B=\texttt{extensionIntegers K L}\),
\(k_A=A/\mathfrak m_A\), \(k_B=B/\mathfrak m_B\), and
\(\rho=\texttt{residueHom K L}\). These are the actual spectral valuation
rings and the residue action constructed in `SpectralDefinitions`. The proof
does not take a residue homomorphism, its continuity or surjectivity, or any
exact-sequence assertion as additional data.

## Integral closure and the residue closure

`spectral_integral` uses `spectralValue_le_one_iff`: an element of spectral norm
at most one has all minimal-polynomial coefficients in \(A\). Lifting those
coefficients gives a monic polynomial over \(A\) annihilating the element.
Conversely, an element integral over \(A\) is integral over \(B\); the valuation
ring \(B\) is integrally closed in its fraction field \(L\), so that element
belongs to \(B\). This proves `integral_iff_mem_spectralIntegers` and supplies
the integral-extension instance for \(A\to B\). Reduction of a monic integral
relation proves `residueExtension_isIntegral`.

The reusable lemma `residue_isAlgClosed` works for any valuation subring of an
algebraically closed field. It lifts a monic irreducible residue polynomial to
a monic polynomial over the valuation ring, finds a root in the field, and uses
integral closedness to place that root in the valuation ring. Its residue is
the required root. Combining this lemma with algebraicity of \(k_B/k_A\)
proves `residueExtension_isAlgClosure`.

## The actual residue action and continuity

`residueHom_apply` is the representative identity
\[
  \rho(\sigma)(\overline{x})=\overline{\sigma x},\qquad x\in B.
\]
All group topologies here are Mathlib's existing Krull topologies.
For continuity at the identity, a basic target neighborhood contains the
fixing subgroup of a finite intermediate residue extension \(E/k_A\).
`residueHom_continuous` chooses a finite basis of \(E\) and integral
representatives in \(B\) for its elements. The intersection of the source point
stabilizers of these representatives is open: each representative is algebraic
over \(K\). Its image fixes the basis and therefore all of \(E\).
Continuity at the identity implies continuity of the homomorphism.

## Residue lifting and surjectivity

`residueHom_lift_single` proves that, for every \(\tau\in
\operatorname{Aut}_{k_A}(k_B)\) and \(y\in k_B\), there is
\(\sigma\in\operatorname{Aut}_K(L)\) with \(\rho(\sigma)y=\tau y\).
This lemma needs only normality of \(L/K\) in addition to the complete
ultrametric base; it does not assume the desired surjectivity.

Choose an integral representative \(x\) of \(y\). Its minimal polynomial over
\(K\) lifts to a monic polynomial \(g\) over \(A\). Normality makes the
polynomial split in \(L\); every root is integral and hence lies in \(B\).
The element \(\tau y\) is a root of the reduction of \(g\). The roots of the
split monic polynomial reduce onto the roots of its reduction, so \(\tau y\)
lifts to a root \(z\in B\). The conjugate-root automorphism theorem produces
a \(K\)-automorphism taking \(x\) to \(z\). Its residue action has the required
value at \(y\).

`residueHom_denseRange` passes from this single-element lifting to every
Krull neighborhood. A finite intermediate residue extension is a finite field
and has a primitive element. Lifting the desired action on that element
matches the target automorphism on the entire finite extension. Thus the image
of \(\rho\) is dense.

For an algebraic Galois extension, the source Galois group is compact.
Its continuous image under \(\rho\) is compact, hence closed in the Hausdorff
residue Galois group. A closed dense image is the whole group; this proves
`residueHom_surjective`. This compactness argument performs the required
passage from finite residue data to the infinite extension.

## Inertia and the quotient topology

`mem_inertia_iff` proves that the kernel consists exactly of automorphisms
fixing the residues of every element of \(B\). Surjectivity of the residue
ring map turns equality on representatives into equality of automorphisms.
The same argument proves `inertia_eq_comap_valuationSubring`, comparing the
kernel with Mathlib's `ValuationSubring.inertiaSubgroup` under
`decompositionHom`.

Normality is the kernel instance from `SpectralDefinitions`. Continuity and
Hausdorffness make the kernel closed; its inherited subgroup topology is
compact and totally disconnected. The usual subgroup instances also retain
the Hausdorff topological-group structure.

`residueQuotientEquiv` equips the algebraic first-isomorphism equivalence with
continuity by the quotient universal property. Its inverse is continuous
because its source is compact and its target is Hausdorff. The equivalence
sends the class of each \(\sigma\) to this particular \(\rho(\sigma)\);
the closing theorem supplies that representative identity by reflexivity.
Finally, the group quotient map is open, and composing it with the
homeomorphism proves `residueHom_isOpenMap`.

The closing theorem assembles these results into every conjunct of the exact
target. The reusable lemmas remain in this proof module.

## Exact dependencies and source relationship

The selected statement is `SpectralResidueExactness`, artifact
`c9ec9a6a-5b72-444a-bfb0-7c5406d5950d` version 1, with checked target fingerprint
`94c3c18f724e4ee46b15aa630d07da23acf68bfe8fde21c9cebf23b1e9422c89`.
It is independently accepted and published at commit
`9007729971e6e6ecea63b5567b6d1621769ccfb0`, with final semantic receipt
`3e22c642fec14152b4d69cc3af8b1248`. Its effective Lean and Markdown SHA-256
values are `f7e2504aa32d31f58435b419a40c4cb4fae7f7da332768b2439832978e769e0a`
and `3ee464a49247f774612cdd289b39e14b07fba54190b84221ac1c3ef2f47e2ef9`.
Current Library membership and these exact dependency bytes were verified
before preparing the native proof task. The definition dependency is the
accepted, published `SpectralDefinitions` artifact
`82bd181d-11b1-4000-afb6-1acdb762dd32` version 1. The pinned environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1: Lean 4.34.0 and Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

Native proof task `f0e0e8d0-9bed-439a-a648-f7d8d9939d3b` revision 1 binds
that exact statement and environment to this module and closing theorem.
The supplied proof comes from the parent task's draft revision 3, content key
`9491450f49e127f883cb78fa856b9c37e09b90379d8fc00de0fb3a8c6a842f33`.
Its Lean SHA-256 is
`0ec2c48c4e49e166a62db849a3f5a2f5b65dac72a9f23e28984d2a3a880e3c14`;
the Lean file is unchanged from that draft. The statement and definition
dependencies were fetched again and their final integrated pairs matched this
checkout before submission.

The source relationship is inherited from the exact statement: Serre,
*Local Fields*, Greenberg English translation, Springer GTM 67 (1979),
Chapter I, section 7, Proposition 20, pp. 20-22 (PDF pp. 28-30);
Chapter II, section 2, Proposition 3 and Corollaries 2-3, pp. 28-29
(PDF pp. 36-37); and Chapter III, section 5, Theorems 2-3 and Corollaries 1-3,
pp. 54-55 (PDF pp. 61-62). The retained source is registered as
`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
at `C:/Central-Library/Serre--Local Fields--1979.pdf`.

The Lean proof uses residue-conjugate lifting, finite primitive elements and
Krull compactness; it does not separately formalize the classification of
unramified extensions. The cited finite discrete-valuation statements are not
attributed the broader infinite-extension generality of this derived theorem.
Specialization to the original residue field of a supplied
`PadicField.TopologicalData`, explicit transport to its chosen algebraic
closure, and finite-level restriction compatibility belong to the subsequent
absolute-Galois pairs. No finite-field Frobenius coordinate, Weil-group
identification or local reciprocity theorem is asserted by this proof.
