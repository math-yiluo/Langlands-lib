# Strong multiplicity one for cuspidal realizations of `GL_(r+1)`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module states one proposition and proves nothing:

- `Langlands.Global.CuspidalStrongMultiplicityOneStatement`.

The module is `Langlands.Global.Factors.CuspidalStrongMultiplicityOneStatement`.
The proposition is the strong multiplicity one theorem, Getz–Hahn (2024),
Theorem 11.7.2 (Jacquet–Shalika 1981, *Euler products I*, Theorem 4.8 and
Corollary 4.10). Let `π` and `π'` be cuspidal automorphic representations of
`GL_n(𝔸_F)`. If `π_v ≅ π'_v` at all places `v` outside a finite set, then
`π ≅ π'`.

It reuses Library vocabulary and defines nothing new:

- `CuspidalOperatorRealization`, `CuspidalSpectralPresentation`;
- `CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents`;
- `CuspidalPairFunctionalEquation.localClass`, from
  `Langlands.Global.Factors.CuspidalPairFactorData`.

These are the local components already used by the published pair L-function
statements `CuspidalPairPoleStatement` and
`CuspidalPairGlobalFunctionalEquationStatement`.

**Why it is here.** The program ledger
`notes/automorphic/global-program-coverage.md` lists the
representation-theoretic form of Getz–Hahn 11.7.2 as an L4 target of this
program with no public statement. The list is in the closing paragraph of the section
"13 November 2026 Getz–Hahn 11.7.1 poles, Lemma 11.8.1 and the H3 reduction".
The Library's `CuspidalSpectralRigidityStatement` has only the numerical form,
which compares unramified spectra (§5 below).

**Proof target.** A later proof task should prove the Library statement
`Langlands.Global.CuspidalStrongMultiplicityOneStatement`. Its universe
parameters are `u` (the number field) and `uQ` (the factor universe of the
spectral presentations).

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.

| Source ID | Short name | Locators used |
|---|---|---|
| `getz-hahn-2024-automorphic-representations` | GH | Thm 11.5.2, p.305 (PDF 316); Thm 11.7.1, Thm 11.7.2 and Cor 11.7.3, p.309 (PDF 320); Exercises 11.6 and 11.8, p.314 (PDF 325) |
| `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4` | JS I | Thm (4.8), p.552 (PDF 54); proof of (4.8) and Cor (4.10), pp.552–553 (PDF 54–55) |

JS I is Jacquet–Shalika, *On Euler products and the classification of
automorphic representations I*, Amer. J. Math. 103 (1981), 499–558. In its
registered file the printed page is the PDF page plus 498.

**What the sources state.** GH p.309:

> **Theorem 11.7.2 (Strong multiplicity one)** Let `π` and `π'` be cuspidal
> automorphic representations of `GL_n(𝔸_F)` and let `S` be a finite set of
> places of `F`. If `π^S ≅ π'^S` then `π ≅ π'`.

Here `π^S` is the restricted tensor product of the local components `π_v` at
the places `v ∉ S`. GH continues: "We leave the proof as Exercise 11.6. It is a
consequence of Theorem 11.5.2 and Theorem 11.7.1." Exercise 11.6 (p.314)
restates the theorem as an exercise. Theorem 11.5.2 (p.305) says: if `π` and
`π'` are unitary, then the local `L(s, π × π')` is holomorphic and nonzero for
`Re(s) ≥ 1`. Corollary 11.7.3 (p.309) and Exercise 11.8 (p.314) state the
same for isobaric representations.

JS I (4.8), p.552, is stated for irreducible unitary cuspidal `π` and `π'`, with
a finite set `S` of places that contains the infinite places and every finite
place where `π_v` or `π'_v` is ramified. The printed hypothesis is

> `L(s, π'_v × π̄_v) = L(s, π'_v × π̄'_v)` for `v ∉ S`,

where `π̄_v` is the complex conjugate representation (notation of JS I (2.1.2)).
The printed conclusion is `π ≃ π'`, equivalence of representations. The proof,
pp.552–553, compares the poles at `s = 1` of two global Rankin–Selberg
integrals and ends with "By (4.6)(ii), `π ≃ π'`". JS I (4.10), p.553, reads:
"Suppose `π` and `π'` are irreducible unitary representations of `G_r(𝔸)`.
Suppose `S` is a finite set of places such that `π_v ≃ π'_v` for `v ∉ S`. Then
`π ≃ π'`." It is a corollary of (4.8), so `π` and `π'` are cuspidal as there.
Its conclusion is also equivalence. So JS I and GH have the same conclusion.

## 2. The declaration

`CuspidalStrongMultiplicityOneStatement` says the following. Let:

- `F` be a number field with `[CompactSpace (AdeleQuotient F)]`, the instance
  needed by `CuspidalOperatorRealization`;
- `r : ℕ`, and `T`, `T'` be actual cuspidal realizations of `GL_(r+1)` over
  `F` (`CuspidalOperatorRealization F r`);
- `P`, `P'` be spectral presentations of `T` and `T'` with factors in universe
  `uQ`;
- `h`, `h'` say that every finite local component of `P` (resp. `P'`) is
  irreducible and admissible (`HasIrreducibleAdmissibleComponents`);
- `S : Finset (FinitePlace F)` be a finite set of finite places.

Suppose `localClass P h v = localClass P' h' v` for every finite place
`v ∉ S`. Then `T.isoClass = T'.isoClass`.

`localClass P h v` is the canonical p-adic class
`(P.localComponent v).padicClass (h v).1 (h v).2`, in
`Correspondence.AutomorphicClass (padicField v) r.succPNat`. Both sides lie in
the same type because `T` and `T'` have the same rank `r + 1`.

## 3. Hypotheses and their match with the source

- **Cuspidal representations.** `CuspidalOperatorRealization F r` is an actual
  irreducible cuspidal subspace of automorphic forms on `GL_(r+1)`, with all
  finite, compact and differential operators. It is GH's cuspidal automorphic
  representation of `GL_n(𝔸_F)` with `n = r + 1`. GH's Theorem 11.7.2 has no
  hypothesis on the split component `A_GL` of the centre, and neither does
  this statement. JS I assumes unitarity; GH does not. Every cuspidal `π` is a
  twist `π₀ ⊗ |det|^t` of a unitary one with `t` real, so the two forms agree.
- **The local components `π_v`.** A spectral presentation `P` of `T` is a
  nonzero finite-adelic-invariant subspace of `T` (`P.finiteSlice`), with an
  equivalence to a restricted tensor product of supplied local factors.
  `P.localComponent v` is the actual embedded copy of the factor at `v`.
  Under `h`, its class is `localClass P h v`. By
  `LocalRealization.padicClass_eq_iff_isoClass_eq`
  (`Langlands/Automorphic/PadicLocalCategory.lean`), equality of these classes
  is exactly isomorphism of the local smooth representations. So the
  hypothesis says `π_v ≅ π'_v` at all finite `v ∉ S`.
- **Why the components of a presentation.** The Library also has
  `OperatorRealization.IsoClass.localClass`
  (`Langlands/Automorphic/OperatorLocalRestriction.lean`). That is the class
  of the whole carrier restricted to `GL_(r+1)(F_v)`, a large direct sum of
  copies of `π_v`, and not `π_v`. It is not used. The components of a
  presentation are the representations `π_v` of the tensor product theorem.
  They are the local components of the published pair statements built on
  `CuspidalPairFactorData`, so a proof can use those statements directly.
- **Independence of the presentation.** The statement quantifies over all
  presentations `P` and `P'` with irreducible admissible components. Their
  local classes do not depend on the choice: the finite slice is then an
  irreducible submodule of `π_∞ ⊗ π_f`, hence isomorphic to `π_f`, and the
  tensor product theorem determines the factors. This is background only. The
  statement neither uses nor asserts it.
- **The statement is not vacuous.** For `uQ = u`, every `T` has such a
  presentation. This follows from the proved
  `cuspidalIrreducibleAdmissibleFiniteSliceExistence`
  (`Langlands/Automorphic/CuspidalAdmissible/Existence.lean`) and
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  (`Langlands/Automorphic/CuspidalSlicePresentation.lean`).
- **The infinite places.** GH's `S` is any finite set of places. Here `S` holds
  finite places only, and nothing is assumed at the infinite places. This is
  GH's theorem for sets `S` that contain every infinite place, and it is
  equivalent to GH's theorem. Given GH's `S`, take its finite places as the Lean
  `S`: GH's hypothesis then gives the Lean hypothesis. Conversely, the Lean
  hypothesis with a finite set `S` is GH's hypothesis for `S` together with all
  infinite places. JS I (4.8) also requires `S` to contain the infinite places.
- **Ramified places.** JS I (4.8) also puts all ramified places into `S`. The
  Lean `S` is arbitrary. The comparison is still at every finite `v ∉ S`,
  ramified or not, as in GH and JS I (4.10).

## 4. The conclusion

`T.isoClass = T'.isoClass` is equality in `CuspidalOperatorRealization.IsoClass F r`.
By `CuspidalOperatorRealization.isoClass_eq_iff` it says
`Nonempty (T.Equivalence T')`: there is a linear equivalence of the carriers
that intertwines all finite, compact and differential operators. This is GH's
`π ≅ π'`, and JS I's `π ≃ π'` in (4.8) and (4.10).

Equality of `T` and `T'` as subspaces of the cusp forms is a different and
stronger claim. Neither GH 11.7.2 nor JS I (4.8) or (4.10) states it. It would
follow from `π ≅ π'` together with multiplicity one (GH Theorem 11.4.3,
published as the unproved
`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement`,
stated for subspaces of `L²`). It is not part of this statement.

## 5. Relation to `CuspidalSpectralRigidityStatement`

`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement`
(`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean`)
has a numerical form, `CuspidalEulerConstituentRecoveryStatement`. For one
constituent on each side (`p = q = 1`), it says that two cuspidal classes whose
attached spectral systems have the same Euler polynomials outside a finite set
are equal. That is strong multiplicity one stated with unramified spectra
instead of local components.

This statement is not a specialization of that one. To deduce it from the
numerical form, a proof needs a bridge: at an unramified `v`, isomorphic local
components of `P` and `P'` have the same spherical Hecke spectrum. The
transport of a spectrum along an equivalence is
`Langlands.Unramified.hasSphericalHeckeSpectrum_iff_of_equiv`
(`Langlands/Representation/Unramified/HeckeOperators.lean`). Uniqueness of the
spectrum on a nonzero spherical space is a further step. Neither statement is
proved in the Library at this time.

## 6. Proof routes (for the proof task; not part of the statement)

**GH's route (Exercise 11.6).** Hecke characters that agree at almost all
places are equal, so `π` and `π'` have the same central character. Twist both
by the same `|det|^t` to make them trivial on `A_GL`. Twisting preserves the
hypothesis. Let `S'` be `S` together with the infinite places. Outside `S'`,
the local factors of `π × π'^∨` and of `π' × π'^∨` agree. By GH Theorem 11.7.1
(the published `CuspidalPairPoleStatement`), the completed `L(s, π' × π'^∨)`
has a pole at `s = 1`. At `s = 1` the local factors at the places of `S'` are
holomorphic and nonzero (GH Theorem 11.5.2, after twisting to unitary).
Therefore `L(s, π × π'^∨)` also has a pole at `s = 1`. By Theorem 11.7.1 again,
`π ≅ (π'^∨)^∨ ≅ π'`.

The Lean form of Theorem 11.5.2 is not yet in the Library. The program ledger
lists it as an L4 target. A proof also needs the contragredient presentation
(the proved `cuspidalContragredientPresentationExistence`,
`Langlands/Automorphic/CuspidalContragredientPresentationExistenceProof.lean`)
and the twist.

**JS's route (JS I (4.8)).** This route compares the poles of global
Rankin–Selberg integrals directly. It uses JS I (4.6) and the local integral
estimates (1.5) and (3.17). It needs unitary `π` and `π'`, so first twist as in
GH's route. If `π_v ≅ π'_v`, then `π̄_v ≅ π̄'_v`, so the local factors in the
(4.8) hypothesis agree; this is how (4.10) follows from (4.8). For unitary `π`,
the conjugate `π̄_v` is equivalent to the contragredient `π_v^∨`, which links
the printed form to the contragredient form used in GH's route.

## 7. Not asserted

- equality of `T` and `T'` as subspaces, or multiplicity one (GH Theorem 11.4.3);
- isobaric representations (GH Corollary 11.7.3);
- different ranks: `T` and `T'` have the same `r`, as in GH and JS I;
- the existence of presentations in a universe `uQ ≠ u`;
- independence of the local classes from the presentation (§3);
- anything at the infinite places.

## 8. Provenance

This is a source statement: GH Theorem 11.7.2, with the hypothesis read
through Library vocabulary. Two choices belong to this formalization: the set
`S` contains finite places only (§3, equivalent to GH), and the local
components are read through spectral presentations. Both are explained above.
The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
declaration is a `def` returning `Prop`.
