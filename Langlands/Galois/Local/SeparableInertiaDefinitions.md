# The separable inertia fixed field of a nonarchimedean local field

Lean construction: Worker 785. Markdown and source audit: Worker 972.

For every nonarchimedean local field \(F\), this file defines the fixed field
\(U\) of the inertia subgroup of \(\operatorname{Gal}(\Omega/F)\), where
\(\Omega=\) `SeparableClosure F` is Mathlib's actual separable closure. It also
builds the tower \(F\to U\to\Omega\) of fields, valuations, integer rings, residue
fields and topologies. The namespace is `Langlands.LocalGalois.Separable`. The
constructions are noncomputable because Mathlib's spectral norm is noncomputable.

## Base field, universe and the choice of norm

The base is `F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`,
for one arbitrary universe `u`. There is no `CharZero F` or `PerfectField F`
hypothesis, so imperfect fields of positive characteristic are included.
`SeparableClosure F`, its intermediate fields and all residue fields below live
in `Type u`.

The supplied valuation relation and topology of \(F\) are not changed. The
Library's spectral constructions need a real-valued norm, so the file installs
four *file-local* instances from the published module
`Langlands.Galois.Local.AbsoluteDefinitions`:

- `localNormedField F` is a nontrivially normed field structure on \(F\). It is
  Mathlib's `Valued.toNontriviallyNormedField` for the rank-one structure
  `localRankOne F`. That structure embeds the value group into
  \(\mathbb R_{\ge 0}\) by the arbitrary choice `IsRankLeOne.nonempty.some`. So
  \(\lVert x\rVert\) is the image of the supplied valuation of \(x\) under one
  chosen order embedding, and no numerical normalization is asserted. Its
  topology is the supplied topology of \(F\) (`localNormedField_topology` is
  proved by `rfl`). Its order is the supplied valuation order
  (`localNormedField_le`). Its closed unit ball is the supplied integer ring
  `𝒪[F]` (`localNormedField_integer`).
- `localNormedField_ultrametric F`, `localNormedField_complete F` and
  `localResidue_finite F` give the ultrametric inequality, completeness, and
  finiteness of the residue field of the norm's unit ball. All three are proved
  in that module.

These instances are local, so importers see only the original instances on
\(F\). However, declarations whose types mention `baseIntegers F` or
`extensionIntegers F _` are elaborated with these four instances. A consumer
must install the same instances, as this file does, to restate them.

Write \(A=\) `baseIntegers F` for the unit ball of this norm and \(k_A\) for
its residue field. `𝒪[F]` and `𝓀[F]` are the supplied integer ring and residue
field. \(A\) and `𝒪[F]` have the same elements but are different Lean terms.
They are compared below through `localNormedField_integer` and
`localResidueEquiv`.

## The separable closure and its spectral valuation

`SeparableClosure F` is Mathlib's separable closure of \(F\) in
`AlgebraicClosure F`. Mathlib proves that it is Galois over \(F\).
`Gal(SeparableClosure F/F)` carries Mathlib's Krull topology; no other topology
on the Galois group is introduced.

- `sepClosureValuation F` is `spectralValuation F Ω`, the
  \(\mathbb R_{\ge0}\)-valued valuation whose value at \(x\) is Mathlib's spectral
  norm of \(x\) over \(F\) (`sepClosureValuation_apply`).
- `sepClosureIntegers F` is its valuation subring. By definition it is
  `extensionIntegers F Ω` (`sepClosureIntegers_eq`). Write \(B\) for it and
  \(k_B\) for its residue field.
- The instance `sepClosureValuation_extends` proves Mathlib's
  `Valuation.HasExtension` from the *original* valuation `ValuativeRel.valuation F`
  to `sepClosureValuation F`. For \(x,y\in F\), \(v(x)\le v(y)\) holds if and only if
  the spectral norms of their images satisfy the same inequality. The proof
  combines Mathlib's `spectralNorm_extends` with `localNormedField_le`. The
  extension therefore respects the order of the supplied valuation. Only the
  order is compared: the two valuations take values in different types (the
  supplied value group of \(F\) and \(\mathbb R_{\ge0}\)).

## The inertia subgroup and its fixed field

- `separableResidueHom F` is the Library's `residueHom F Ω`. This is the
  homomorphism \(\operatorname{Gal}(\Omega/F)\to\operatorname{Aut}_{k_A}(k_B)\)
  sending \(\sigma\) to the map \(\bar b\mapsto\overline{\sigma b}\) for
  \(b\in B\).
- `separableInertia F` is the Library's `inertia F Ω`, the kernel of that
  homomorphism (`separableInertia_eq_ker` holds by definition). Write \(I\) for
  it.
  - It is normal (instance `separableInertia_normal`).
  - \(\sigma\in I\) if and only if \(\overline{\sigma b}=\bar b\) for every
    \(b\in B\) (`mem_separableInertia_iff`, from the published
    `mem_inertia_iff`).
  - It is closed in the Krull topology (`separableInertia_isClosed`, from the
    published `inertia_isClosed`).
- `inertiaFixedField F` is `IntermediateField.fixedField (separableInertia F)`.
  This is the intermediate field \(U\) of \(\Omega/F\) consisting of the elements
  fixed by every element of \(I\) (`mem_inertiaFixedField_iff`).
- `inertiaFixedField_isGalois`: \(U/F\) is Galois because \(I\) is normal. This
  is Mathlib's `IsGalois.of_fixedField_normal_subgroup`.
- `fixingSubgroup_inertiaFixedField`: the subgroup of
  \(\operatorname{Gal}(\Omega/F)\) fixing \(U\) pointwise is exactly \(I\). This is
  Mathlib's infinite Galois correspondence
  `InfiniteGalois.fixingSubgroup_fixedField`, applied to the closed subgroup
  \(I\).

So \(U\) is the inertia fixed field *by construction*. It is defined as the fixed
field of the kernel of the constructed residue action. No arithmetic property of
\(U\) is used or asserted.

## The field maps

- `baseToFixedField F : F →ₐ[F] U` is the structure map `Algebra.ofId`.
- `fixedFieldToSepClosure F : U →ₐ[F] Ω` is the subtype inclusion `U.val`
  (`fixedFieldToSepClosure_apply`).
- `fixedFieldToSepClosure_comp_baseToFixedField` states that their composite is
  the structure map \(F\to\Omega\).

## The valuation on \(U\) and the integer rings

- `fixedFieldValuation F` is the restriction
  `(sepClosureValuation F).comap (algebraMap U Ω)` (`fixedFieldValuation_apply`).
  Write \(v_U\) for it. `fixedFieldValuation_eq_spectralValuation` proves that
  it equals the Library's `spectralValuation F U`, using Mathlib's
  `spectralNorm.eq_of_tower`.
- `fixedFieldIntegers F` is the valuation subring of \(v_U\).
  `fixedFieldIntegers_eq` identifies it with `extensionIntegers F U`.
  `fixedFieldIntegersEquiv F` is the resulting ring isomorphism, which is the
  identity on elements (`coe_fixedFieldIntegersEquiv`).
- The instance `fixedFieldValuation_extends` is `HasExtension` from the original
  valuation of \(F\) to \(v_U\).
- The instance `sepClosureValuation_extends_fixedField` is `HasExtension` from
  \(v_U\) to `sepClosureValuation F`. It holds by the definition of the
  restriction.

## Integer maps

Consider the maps
\[
 \texttt{𝒪[F]}\xrightarrow{\ \texttt{integerToFixedField}\ }
 \texttt{fixedFieldIntegers F}
 \xrightarrow{\ \texttt{fixedFieldIntegerInclusion}\ }
 \texttt{sepClosureIntegers F}
\]
and \(\texttt{integerToSepClosure}:\texttt{𝒪[F]}\to\texttt{sepClosureIntegers F}\).
They are Mathlib's algebra maps between valuation integer rings attached to the
`HasExtension` instances above.

- On elements they are the field maps (`coe_integerToFixedField`,
  `coe_fixedFieldIntegerInclusion`, `coe_integerToSepClosure`).
- The triangle commutes (`fixedFieldIntegerInclusion_comp_integerToFixedField`).
- All three are local homomorphisms (instances `integerToFixedField_isLocalHom`,
  `fixedFieldIntegerInclusion_isLocalHom`, `integerToSepClosure_isLocalHom`).

They are compared with the published generic maps as follows.

- `integerInclusion_fixedFieldIntegersEquiv`: the Library's
  `integerInclusion F Ω U`, precomposed with `fixedFieldIntegersEquiv F`, is
  `fixedFieldIntegerInclusion F`.
- `integerToFixedField_localNormedField` and
  `integerToSepClosure_localNormedField` concern an element of \(A\) carried to
  `𝒪[F]` by `RingEquiv.subringCongr (localNormedField_integer F)`. The two maps
  out of `𝒪[F]` send it to its images under the algebra maps
  \(A\to\) `extensionIntegers F U` (read through `fixedFieldIntegersEquiv F`) and
  \(A\to B\).

## Residue maps

`residueToFixedField F`, `fixedFieldResidueInclusion F` and
`residueToSepClosure F` are `IsLocalRing.ResidueField.map` of the three integer
maps. They go from `𝓀[F]` to the residue field of `fixedFieldIntegers F`, from
there to \(k_B\), and from `𝓀[F]` to \(k_B\).

- `residueToFixedField_residue`, `fixedFieldResidueInclusion_residue` and
  `residueToSepClosure_residue` evaluate them on residues of representatives.
- `fixedFieldResidueInclusion_comp_residueToFixedField` proves the composition
  law.
- `residueInclusion_fixedFieldIntegersEquiv`: the Library's
  `residueInclusion F Ω U`, precomposed with the residue-field isomorphism
  induced by `fixedFieldIntegersEquiv F`, is `fixedFieldResidueInclusion F`.
- `residueToFixedField_localResidueEquiv` and
  `residueToSepClosure_localResidueEquiv`: precomposed with the published
  `localResidueEquiv F : k_A ≃+* 𝓀[F]`, the two maps out of `𝓀[F]` are the
  residue algebra maps out of \(k_A\). The first is
  \(k_A\to\) the residue field of `extensionIntegers F U`, read through the
  induced isomorphism. The second is \(k_A\to k_B\).

## Topologies

The four structures `sepClosureNormedField`, `sepClosureTopology`,
`fixedFieldValued` and `fixedFieldTopology` are not global instances. Each is a
definition marked `@[instance_reducible]`, to be installed locally.

- `sepClosureNormedField F` is Mathlib's
  `spectralNorm.nontriviallyNormedField F Ω`. Its norm is the spectral norm
  (`sepClosureNormedField_norm`). `sepClosureTopology F` is its metric topology.
- `fixedFieldValued F` is `Valued.mk' (fixedFieldValuation F)`, and
  `fixedFieldTopology F` is its topology. This is the additive group topology
  with the following basis of neighbourhoods of \(0\): the sets
  \(\{x\in U: v_U(x)<\gamma\}\), where \(\gamma\) runs through the elements of
  Mathlib's value group of \(v_U\), the subgroup of \(\mathbb R_{>0}\) generated
  by the nonzero values of \(v_U\) (Mathlib's `Valued.hasBasis_nhds_zero`).
- `fixedFieldTopology_eq_induced` proves that `fixedFieldTopology F` equals the
  topology induced from `sepClosureTopology F` by the inclusion
  \(U\subseteq\Omega\). Both are additive group topologies, so the proof
  compares neighbourhood bases of zero. A valuation ball of radius \(\gamma\) is
  the trace on \(U\) of the metric ball of radius \(\gamma\). Conversely, given
  \(\varepsilon>0\), choose \(a\in F\) with \(0<\lVert a\rVert<\varepsilon\). The
  valuation ball of radius \(v_U(a)\) then lies in the trace of the
  \(\varepsilon\)-ball.

The topology of \(F\) itself is not changed. Completeness or local compactness of
\(U\) or \(\Omega\) is neither assumed nor claimed.

## What this unit does not assert

This is a construction unit, and it proves only the short facts listed above.
The following are later arithmetic obligations. None appears here as a
hypothesis, as input data or as a conclusion:

- \(U\) is the maximal unramified extension of \(F\) in \(\Omega\);
- finite-unramified exhaustion: every finite subextension of \(U/F\) is
  unramified, and every finite unramified subextension of \(\Omega/F\) lies in
  \(U\);
- the residue field of `fixedFieldIntegers F` is an algebraic closure of
  `𝓀[F]`;
- \(v_U\) is discrete, and `fixedFieldIntegers F` is Henselian.

Completeness and local compactness of \(U\) are not part of this construction.
No comparison of `Gal(SeparableClosure F/F)` with the `AlgebraicClosure`-based
`Field.absoluteGaloisGroup F` is made. The Library's `absoluteResidueHom` and
`absoluteInertia` are neither used nor changed.

## Sources and correspondence

**Serre.** Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979. Registered source
`serre-1979-local-fields`; file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Chapter I, §7, printed pp. 20–22 (PDF pages 28–30). For a finite Galois
  extension \(L/K\), page 21 defines the decomposition group \(D\) and the
  homomorphism \(\varepsilon:D\to G(\bar l/\bar k)\) induced on residue fields.
  Its kernel is the inertia group \(T\), and the corresponding field \(K_T\)
  satisfies \(G(L/K_T)=T\). Proposition 20 is on page 21 and Proposition 21 on
  page 22. Proposition 21 states that \(w_T\) prolongs \(v\) with index 1 and
  that the residue field of \(K_T\) is the separable closure of \(\bar k\) in
  \(\bar l\).
- Chapter III, §5, Theorems 2–3 and Corollaries 1–3, printed pp. 54–55 (PDF
  pages 61–62). Over a complete discrete valuation ring, finite unramified
  extensions correspond to finite separable residue extensions. Corollary 1
  defines the maximal unramified extension \(K_{nr}\) as the inductive limit of
  these extensions. It is Galois over \(K\) with residue field \(k_s\), and
  \(G(K_{nr}/K)=G(k_s/k)\).
- Chapter IV, §1, Proposition 1, printed p. 62 (PDF page 69): \(G_0\) is the
  inertia subgroup of \(G\) in the sense of Chapter I, §7, and \(G/G_0\) is the
  Galois group of the residue extension. Also the Corollary after Proposition 2,
  printed p. 63 (PDF page 70): the subgroup corresponding to the largest
  unramified subextension is the inertia group \(G_0\).

**Serre corrections.** Jean-Pierre Serre, *Corrections to J-P. Serre's books*
(2019). Registered source `serre-book-corrections-2019`; file
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA-256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`. The
*Local Fields* entries are on PDF pages 2–3. None concerns printed pp. 20–22,
54–55 or 62. The two entries for p. 63 concern Proposition 3 only.

**Kaletha–Prasad.** Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New
Approach*, Cambridge University Press, 2023. Registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

- §2.5(c), printed p. 88 (PDF page 119): for a discretely valued Henselian
  field \(k\) with perfect residue field, \(K\) denotes the maximal unramified
  extension in a fixed separable closure \(k_s\).
- Lemma 2.5.12 (printed p. 89, PDF page 120) and Definition 2.5.13, Lemma 2.5.14
  and Remark 2.5.15 (printed p. 90, PDF page 121) use this \(K\) to define the
  Iwahori subgroup of a torus.

These were read with the authors' corrections, version of 1 November 2024
(registered source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`), PDF pages
24–25. Their Section 2.5 entries change the formula for \(\omega_T\) in
2.5(b), replace "§7" by "§6" in Remark 2.5.11, and replace Remark 2.5.15. None
changes the setup of 2.5(c), Lemma 2.5.12 or Definition 2.5.13.

All cited pages were read in the retained files listed above.

**Correspondence and provenance.**

- Serre defines \(\varepsilon\) on the decomposition group of a finite Galois
  extension. In the Library construction, every \(F\)-automorphism of \(\Omega\)
  preserves \(B\) (the published `integerAut`). So the residue action
  `residueHom` is defined on the whole of \(\operatorname{Gal}(\Omega/F)\), and
  `inertia` is its kernel. `separableResidueHom` and `separableInertia`
  specialize these to the infinite extension \(\Omega/F\).
- `inertiaFixedField` is the analogue for \(\Omega/F\) of Serre's \(K_T\). Its
  identification with Serre's \(K_{nr}\) and with Kaletha–Prasad's \(K\) is a
  later obligation and is not proved here. This unit uses no Henselian,
  discreteness or perfect-residue-field hypothesis beyond what the Library's
  spectral constructions already need.
- The Lean names and the following objects are derived implementation content:
  the restriction of the spectral valuation to \(U\), the `HasExtension`
  instances, the integer and residue maps and their comparisons, and both
  topologies. The cited sources do not define these Lean objects literally.

## Dependencies

The file imports `Langlands.Galois.Local.AbsoluteDefinitions`,
`Mathlib.FieldTheory.IsSepClosed` and `Mathlib.FieldTheory.Galois.Infinite`.
The project modules used are the published versions at Library commit
`0d8048b01d03683dff30528ca443052ab82a07be`:

- `Langlands.Galois.Local.SpectralDefinitions` (Lean SHA-256
  `7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a`), for
  `spectralValuation`, `baseIntegers`, `extensionIntegers`, `integerAut`,
  `residueHom`, `inertia` and `inertia_normal`;
- `Langlands.Galois.Local.SpectralProof` (Lean SHA-256
  `0ec2c48c4e49e166a62db849a3f5a2f5b65dac72a9f23e28984d2a3a880e3c14`), for
  `mem_inertia_iff` and `inertia_isClosed`;
- `Langlands.Galois.Local.AbsoluteDefinitions` (Lean SHA-256
  `6abe3d956b83ed48d70cd27e76272a19e41f71a9baf1fab3a7673bace9a5a663`), for
  `localNormedField` and its construction lemmas, `localResidueEquiv`,
  `localResidue_finite`, `integerInclusion` and `residueInclusion`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 with
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The file introduces no
axioms and does not change any existing module.
