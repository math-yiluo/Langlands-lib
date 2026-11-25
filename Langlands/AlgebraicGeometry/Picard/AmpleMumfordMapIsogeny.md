# The Mumford homomorphism of an ample line bundle is an isogeny

Lean module: `Langlands.AlgebraicGeometry.Picard.AmpleMumfordMapIsogeny`, namespace
`Langlands.AbelianScheme.AmpleMumfordIsogeny`.

Let `k` be a field, `A` an abelian scheme over `Spec k`, and `W : Rosati.DualData A` the
witnesses for the Library's constructed dual `W.dual P`. Here
`P : Rosati.Prerequisites` collects the tensor and Picard inputs. Classically, if `L` is an
ample line bundle on an abelian variety over an algebraically closed field, then
`φ_L : A → A^∨, a ↦ t_a^*L ⊗ L⁻¹` is an isogeny. This module proves that statement for the
Library's actual Mumford map `mumfordSchemeMapOfLineBundle`.

## Provenance

Milne, *Abelian Varieties* (1986 article, author revision January 2, 2022; registered source
`milne-abelian-varieties-1986-author-2022`), Section 10, p.17, after Proposition 10.1. For
ample `L`, each class in `Pic⁰` is represented by `L_a` for only finitely many `a`, so the
classifying map `φ_L` is an isogeny. Isogenies are finite, flat and surjective by
Proposition 8.1, p.12. The finiteness of the kernel `K(L)` is Lemma (2.19), printed p.23
(PDF p.27), of Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`). There, `K(L)` is the maximal closed
subscheme over which the Mumford bundle `Λ(L)` is trivial (Definition (2.16)), and the proof
shows that `L ⊗ (-1)^*L` restricted to it is both trivial and ample. The steps below
implement that argument for the scheme-theoretic kernel of the Mumford map.

The structure `AmpleMumfordPresentation` is an internal auxiliary definition. It packages the
explicit ample Mumford presentation from the hypotheses of the published
`Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`; no source defines it.

## Declarations

### `AmpleMumfordPresentation P k A W ψ` (definition)

A structure for `ψ : A ⟶ W.dual P`. Its fields are a line bundle `L` on `A`, a line bundle
`B` on `Spec k` with `evaluationB : e^*L ⊗ B ≅ O`, a line bundle `M` on `A` with
`evaluation : N ⊗ M ≅ O_A`, a proof `isAmple` that `L` is ample, and a proof `hom_eq` that
the underlying scheme morphism `(groupHom ψ).hom.hom` equals
`mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation P.square W.hasDual`.
Here `N = LineBundle.normalize … L B evaluationB` is the normalized rigidified bundle. In
words: an explicit presentation of `ψ` as the Mumford homomorphism `φ_L` of an ample line
bundle. The hypotheses `L.IsAmple → (groupHom lam).hom.hom = mumfordSchemeMapOfLineBundle …`
of `MumfordMixedEulerTraceStatement` are exactly the data of an
`AmpleMumfordPresentation P k A W lam`.

### `isFinite_kernel`

**Statement.** If `L` is ample and `(groupHom ψ).hom.hom` is the Mumford map of
`(L, B, evaluationB, M, evaluation)`, then the scheme-theoretic kernel
`GroupScheme.kernel (groupHom ψ)` is finite over `Spec k`. The field is arbitrary.

**Proof.** Let `j : Z ⟶ A` be the underlying morphism of the kernel inclusion. It is a closed
immersion because the dual is separated.

1. The tautological point `tautological A j : testObject A j ⟶ A.X` factors through the
   kernel, so its composite with `ψ` is the unit point `1` (`GroupScheme.kernel_isPullback`).
2. `mumfordSchemeMapOfLineBundle_points` says that the Poincaré classifying map sends this
   composite to the class of the pulled-back Mumford family. The published multiplicative
   equivalence `dualAbelianSchemePointMulEquiv` sends the unit point to the trivial class
   (`map_one`). Hence the pulled-back Mumford family is isomorphic to the trivial family
   (`Quotient.exact`, `RigidifiedLineBundle.pullbackTrivialIso`).
3. The published `TranslationStabilizer.antidiagonalTrivialization` turns this into an
   isomorphism `j^*M ⊗ (j ≫ ι)^*M ≅ O_Z`, where `ι` is the inversion of `A`.
4. In the Picard group, `[N] + [M] = 0` from `evaluation` (`LineBundle.classOf_tensor`,
   `LineBundle.classOf_eq_iff`), and pullback is a group homomorphism
   (`Group.pullback_lineBundle_classOf`). Hence `j^*N ⊗ (j ≫ ι)^*N` has class `0`, i.e. it is
   trivial.
5. `N` is ample: its carrier is isomorphic to `L` (`nonempty_normalize_carrier_iso`,
   `ampleIso`). Pullbacks along the closed immersions `j` and `j ≫ ι` are ample
   (`closedImmersionPullbackAmple`), and so is their tensor product (`ampleTensor`). So the
   trivial bundle on `Z` is ample, and the published `properAmpleTrivialFinite` shows that
   the proper morphism `j ≫ A.X.hom`, the structure map of the kernel, is finite.

Step 5 follows the Library module `FieldMumfordFiniteLocus`. Here the ample bundle is the
rigidified factor `N` of the Mumford family, not its inverse, which is why step 4 is needed.

### `isIsogeny`

**Statement.** If `k` is algebraically closed, `L` is ample and `(groupHom ψ).hom.hom` is the
Mumford map of `(L, B, evaluationB, M, evaluation)`, then `IsIsogeny ψ`: the underlying
morphism `hom ψ` is finite, flat and surjective.

**Proof.** The kernel is finite by `isFinite_kernel`. `A` is proper and the dual is separated,
so `HomIsogeny.isFinite_of_finite_kernel` (module
`Langlands.GroupScheme.AlgClosedFiniteKernelHomIsogeny`) makes `hom ψ` finite. The published
`fieldFiniteMumfordMapSurjective` then makes the Mumford map surjective. Finally
`HomIsogeny.isIsogeny_of_finite_kernel_of_surjective` applies: the dual is smooth,
geometrically connected and separated, being an abelian scheme.

### `AmpleMumfordPresentation.isIsogeny`

Over an algebraically closed field, a homomorphism `ψ` with an
`AmpleMumfordPresentation P k A W ψ` is an isogeny. Proof: apply `isIsogeny` to the fields
of the presentation.
