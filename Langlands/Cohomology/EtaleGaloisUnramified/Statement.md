# Almost-everywhere unramified Galois actions on étale cohomology

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `GaloisCohomologyUnramifiedStatement`.
Let `K` be a number field and `f : X ⟶ Spec K` a morphism of finite type.
Worker 13's published `Langlands.Geometry.EtaleGaloisAction` lets the
absolute Galois group `Gal(K̄/K)` act on the étale cohomology of
`X_K̄ = X ×_{Spec K} Spec K̄` with constant coefficients. The proposition
says that for a finite coefficient module `M` and a degree `n`, this action
is unramified at all finite places of `K` outside a finite set: at each
such place `v`, the inertia subgroup of the absolute Galois group of the
completion `K_v` acts trivially. Unramifiedness is the predicate
`IsUnramifiedAt` of the published `Langlands.Shimura.DecompositionGroupAction`.
Nothing is proved here.

Harris (1999) works with Galois representations "unramified at all but
finitely many places" (see [Provenance](#provenance)). This module states
that property for the étale cohomology of finite-type schemes with finite
constant coefficients. It is an input to the almost-everywhere unramified
association, which the task keeps separate from ramified local
compatibility.

## Objects

All types live in one universe `u`.

- `K` is a field with `[NumberField K]`.
- `f : X ⟶ Spec (CommRingCat.of K)` is a morphism of Mathlib schemes with
  `[LocallyOfFiniteType f]` and `[QuasiCompact f]`, that is, of finite type.
  No separatedness, properness or smoothness is assumed.
- `R` is a commutative ring. `M : ModuleCat R` is quantified inside the
  proposition with the instance `[Finite M]`: the underlying set of `M` is
  finite. `n : ℕ` is the degree.
- `galoisCohomologyRep (L := AlgebraicClosure K) f R M n` is Worker 13's
  representation of `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` on the
  degree-`n` étale cohomology of `X_K̄ := baseChange K (AlgebraicClosure K) f`
  with coefficients in the constant sheaf of `M`, computed in sheaves of
  `R`-modules on Mathlib's small étale site (Worker 13's
  `Langlands.Geometry.EtaleDerivedSections`). The published
  [EtaleGaloisSmooth](../EtaleGaloisSmooth/Statement.md) explains the
  action: `σ` acts by the pullback along `baseChangeMap f σ`, the identity
  on `X` times `Spec σ` on `Spec K̄`.
- In Mathlib commit `5ed29652` the category `Rep R G` is a structure, not
  `Action (ModuleCat R) G`. Mathlib's functor `Rep.RepToAction` turns the
  representation into an object of `Action (ModuleCat R) G`, with the same
  module and with `σ` acting by the endomorphism of `ModuleCat` given by the
  linear map of `σ`. Here `G = Field.absoluteGaloisGroup K`, which Mathlib
  defines as `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` with the same
  group structure.
- `Global.FinitePlace K` is the Library's type of finite places, the
  height-one primes of the ring of integers of `K`.
- `DecompositionGroupAction.IsUnramifiedAt V v A`, for an object `A` of
  `Action V (Field.absoluteGaloisGroup K)`, says: every element of
  `localInertia v` acts trivially on `A` after restriction along Mathlib's
  chosen closure embedding `chosenClosureEmbedding`, a `K`-algebra map from
  `K̄` to the algebraic closure of the completion `K_v`. Here
  `localInertia v` (published module `Langlands.Galois.CompatibleFamily`,
  Worker 41) is the kernel of the action of the absolute Galois group of
  `K_v` on the residue field of its algebraic closure, and the restriction
  `localRestriction v ι g` is the unique element `σ` of `Gal(K̄/K)` with
  `ι ∘ σ = g ∘ ι` (`localRestriction_commutes`). The published theorem
  `isUnramifiedAlong_iff` shows that the condition does not depend on the
  closure embedding.

## The proposition

```lean
def GaloisCohomologyUnramifiedStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [QuasiCompact f] (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ),
    ∃ S : Set (Global.FinitePlace K), S.Finite ∧ ∀ v ∉ S,
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))
```

In words: for every finite `R`-module `M` and every degree `n` there is a
finite set `S` of finite places of `K` such that, for every finite place
`v ∉ S`, the inertia subgroup at `v` acts trivially on
`H^n(X_K̄, M)`. The set `S` may depend on `M` and `n`.

The test lemma `isUnramifiedAt_repToAction_iff` of check `526e7ba1` (below)
spells out the condition for an arbitrary `A : Rep R (Field.absoluteGaloisGroup K)`:
`IsUnramifiedAt` holds for `(Rep.RepToAction R _).obj A` if and only if
`A.ρ (localRestriction v (chosenClosureEmbedding _) i) = LinearMap.id` for
every `i ∈ localInertia v`.

## Why the statement is expected to hold

This argument is derived from the cited sources; none of them states the
proposition in this form. Fix `M` and `n`, and let `e` be the cardinality of
`M`, so `e • M = 0`.

1. *Spreading out.* Write `K` as the filtered colimit of the rings
   `O_K[1/N]`, so that `Spec K` is the limit of the affine schemes
   `Spec O_K[1/N]` along affine transition maps. Since `K` is noetherian,
   `f` is of finite presentation. By Stacks Lemma 32.10.1 (tag 01ZM), part
   (1), there are `N ≥ 1` and a morphism of finite presentation
   `f_N : 𝒳 → Spec O_K[1/N]` whose base change to `Spec K` is `X`. After
   replacing `N` by `N e`, the integer `e` is invertible on
   `T = Spec O_K[1/N]`.
2. *Coefficients.* The constant sheaf of `M` on `𝒳` is a constructible
   sheaf of `ℤ/e`-modules (SGA 4 IX 2.3: constant with finite value), and
   `ℤ/e` is a noetherian ring annihilated by an integer invertible on `T`,
   as SGA 4½ [Th. finitude] requires. The cohomology of a sheaf of
   `R`-modules is that of its underlying abelian sheaf: injective sheaves of
   `R`-modules are flasque (SGA 4 V 4.6), flasqueness depends only on the
   underlying abelian sheaf (V 4.4), and flasque sheaves have no higher
   cohomology (V 4.1).
3. *Generic base change.* By SGA 4½ [Th. finitude] Théorème 1.9 for
   `f_N : 𝒳 → T` (with `Y = S = T`), there is a dense open `U ⊂ T` over
   which `R^n f_{N*} M` is constructible and whose formation is compatible
   with every base change `T' → U`.
4. *A locally constant piece.* `U` is noetherian and irreducible. By SGA 4
   IX 2.4 (i), `U` is a union of locally closed constructible parts on each
   of which `G = R^n f_{N*} M` is locally constant with finite fibres. The part
   containing the generic point is open in its closure `U`, so `G` is
   locally constant with finite fibres on a nonempty open `V ⊂ U`, and is
   represented there by a finite étale covering (IX 2.2).
5. *The geometric generic stalk.* Take the geometric point
   `η̄ : Spec K̄ → V` given by `K ⊂ K̄`. Compatibility with the base change
   `Spec K̄ → U` identifies the stalk `G_η̄` with
   `H^n(𝒳 ×_T Spec K̄, M) = H^n(X_K̄, M)`. For `σ ∈ Gal(K̄/K)`, `Spec σ` is
   an automorphism of `η̄` over `V`, and the base change isomorphism is
   natural in `T'`. Hence the action of `σ` on `G_η̄` is the pullback along
   `baseChangeMap f σ`, which is the Library's action, possibly up to
   replacing `σ` by `σ⁻¹`. Such an inversion does not change which subgroup
   acts trivially.
6. *Inertia acts trivially.* By SGA 1 V §7 and IX 2.2, the locally constant
   sheaf `G|_V` corresponds to the finite set `G_η̄` with its continuous
   action of `π_1(V, η̄)`, and `Gal(K̄/K)` acts on `G_η̄` through
   `π_1(Spec K, η̄) → π_1(V, η̄)`. `V` is connected, noetherian and normal.
   By SGA 1 V Proposition 8.2 the kernel of this map corresponds to the
   composite of the finite extensions of `K` inside `K̄` that are unramified
   over `V`. Let `v` be a closed point of `V`, let `ι` be a closure embedding
   at `v`, and let `g ∈ localInertia v`. The Galois closure of a finite
   extension unramified over `V` is again unramified over `V`, so the
   composite is generated by finite Galois subextensions `L ⊂ K̄` unramified
   over `V`. For such `L`, the extension `ι(L) K_v` of `K_v` is finite,
   Galois and unramified, so its Galois group maps isomorphically onto that
   of its residue extension. Since `g` acts trivially on residues, `g` fixes
   `ι(L) K_v` pointwise. As `ι (σ x) = g (ι x)` for
   `σ = localRestriction v ι g` (`localRestriction_commutes`) and `ι` is
   injective, `σ` fixes `L`. So `σ` lies in the kernel and acts
   trivially on `G_η̄ = H^n(X_K̄, M)`.
7. *The finite set.* The complement of `V` in `Spec O_K` is a closed set not
   containing the generic point, hence a finite set of closed points. Let
   `S` be the corresponding finite places, including those dividing `N e`.
   By step 6, every `v ∉ S` satisfies `IsUnramifiedAt`.

The argument uses neither properness nor smoothness of `X`. The set `S`
depends on `M` (through `e` and through the open set of Théorème 1.9).

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §5, printed p.313: "we will be considering λ-adic representations
σ of Gal(F̄/F) which are unramified at all but finitely many places and pure
of weight m". Theorem 5.7 (ii) (p.313) and Theorem 5.9 (i) (p.315) state
the equality of local Euler factors "for almost all places", for
representations realized on the cohomology of unitary Shimura varieties.
Harris attributes these parts to Kottwitz and Clozel (pp.314-315).

The proposition is the unramifiedness part of this, for a different object:

- the cohomology is that of an arbitrary finite-type scheme over a number
  field, with constant coefficients, not the cohomology of Harris's Shimura
  varieties `S_K(N)` with the coefficient systems `W`;
- the coefficients are finite modules, not λ-adic. The set `S` depends on
  `M`. A λ-adic statement needs one finite set for all torsion levels at
  once, which this proposition does not give;
- nothing is said about purity, Frobenius eigenvalues or Euler factors.

| Lean | Source |
| --- | --- |
| `IsUnramifiedAt ... v ...` for `v ∉ S`, `S.Finite` | Harris 1999 §5, p.313, "unramified at all but finitely many places" |
| `galoisCohomologyRep (L := AlgebraicClosure K) f R M n` with `[Finite M]` | the cohomology of a finite-type scheme over a number field with finite constant coefficients; truth from SGA 4½ [Th. finitude] 1.9 |
| `[LocallyOfFiniteType f] [QuasiCompact f]` | "S-schémas de type fini" in [Th. finitude] 1.9, after spreading out (Stacks 01ZM) |

## Scope and relation to other modules

The statement does not cover:

- λ-adic or rational coefficients, or a finite set of places that works for
  all torsion levels;
- non-constant coefficient sheaves, compactly supported cohomology, or the
  cohomology modules of the Library's CM towers (`cmSmallLevelGaloisCohomologyFunctor`,
  `cmPrimeToGaloisCohomologyFunctor` and their decomposition-group
  restrictions), which are colimits over levels with coefficients pulled
  back from `Spec F` and are built separately;
- any description of the exceptional set `S`, such as places of bad
  reduction;
- Frobenius eigenvalues, purity, or local-global compatibility.

Related Library declarations:

- The published [EtaleGaloisSmooth](../EtaleGaloisSmooth/Statement.md)
  states that the same Galois action is smooth for the Krull topology.
- `Langlands.Shimura.DecompositionGroupAction` (no Author line) defines
  `IsUnramifiedAt` for objects of `Action V (Field.absoluteGaloisGroup K)`
  and proves that it is independent of the closure embedding, invariant
  under isomorphism, and that unramified actions give a well-defined
  geometric Frobenius. It proves unramifiedness of no specific object.
- `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology` (no Author
  line) takes unramifiedness of the CM cohomology as a hypothesis of its
  Frobenius results.
- `Langlands.GaloisRepresentation.IsUnramifiedAt` (Worker 41, module
  `Langlands.Galois.CompatibleFamily`) is the analogous predicate for
  finite-dimensional representations in compatible families. It is not used
  here.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; §5,
  printed p.313 (PDF p.15), Theorem 5.7 (pp.313-314) and Theorem 5.9 (i)
  (p.315, PDF p.17), read in the text layer. Provenance only.
- `deligne-1977-sga4-half-cohomologie-etale`: SGA 4½, Lecture Notes in
  Mathematics 569, PDF SHA-256
  `fb2939521f4c0ea0cdd55a90bec2e618e32fb433c78b194e705c6d989f4e42a6`
  (printed page = PDF page - 39 in [Th. finitude]); [Th. finitude] §1, the
  standing hypotheses on printed p.233 (PDF p.272) and Théorème 1.9 on
  printed p.236 (PDF p.275), read in the text layer. Truth argument.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305, original scan, PDF SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`
  (PDF page = printed page + 3 in Exposé IX); Exposé IX (Artin) 2.0
  (printed p.6), 2.2 (p.8), Définition 2.3 (pp.8-9) and Proposition 2.4 (i)
  (p.9), read on rendered page images. Truth argument.
- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`;
  Exposé V (Verdier) 4.1, 4.4 and 4.6, printed pp.28-31. Truth argument.
- `sga1-arxiv-math-0206203v2`: SGA 1, recomposed edition (arXiv
  math/0206203v2), PDF SHA-256
  `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`
  (printed page = PDF page - 16 in Exposé V); Exposé V §7 and Propositions
  8.1 and 8.2, printed p.117 (PDF p.133), read in the text layer. Truth
  argument.
- `stacks-limits-of-schemes-a04446e5`: Stacks Project, Chapter 32 Limits of
  Schemes, `limits.tex` at commit
  `a04446e57ec1fbc252a871afcec7752fb2807b14` (file SHA-256
  `dccddc3622ebad21dd6219ea50b157fcf20c574e82b9e920b7f4d1ed127e0aa4`);
  Lemma 32.10.1 (tag 01ZM, label `lemma-descend-finite-presentation`,
  line 2370), part (1). Truth argument.

## Formal dependencies and checks

Direct project imports, in Library commit
`568f1cff4df2c51ba08b932716bf99235d0032c7` and the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Geometry.EtaleGaloisAction` | Worker 13 | `5d07cffce7425cbd24204e0f65a5ca913c1570e7c5621aae229d13beb0e581fa` | `d9c5b185b7b92d780aeceaa828ac8440c29a30872c2099428cd5a5776dc885f6` |
| `Langlands.Shimura.DecompositionGroupAction` | no Author line | `9a5ae46b57a07e743845d7980e90a00a4db618f2e14fee54dc16f303e91cda43` | `317291d8aad940a67f73157ad08598516b9d3cb5731f195dd524085ac58b4cfc` |

Through these imports the module uses Worker 13's
`Langlands.Geometry.EtaleConstantCohomology` (`constantCohomologyRep`) and
Worker 41's `Langlands.Galois.ClosureRestriction` (`chosenClosureEmbedding`)
and `Langlands.Galois.CompatibleFamily` (`localInertia`). The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `568f1cff`, on the final Lean file (SHA-256
`f061ad9b56726fbdcde8f3760d3760708ea3948a07763a85b1a0502f6f35caaa`). None reported errors or warnings.

- `526e7ba1-7942-4049-9df2-f6944e4c54ac` compiled the file from a draft
  directory together with a test file
  (`Langlands/Inspect/EtaleGaloisUnramifiedPrint.lean`, SHA-256
  `de494a79265232e065e3d111c87f7260102cf562b6f4a537b64a8581423ed6ee`), not part of the candidate. It printed
  `GaloisCohomologyUnramifiedStatement` with universes: a `Prop`-valued
  definition with the single universe parameter `u`. It proved
  `isUnramifiedAt_repToAction_iff`, which depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `5e039e66-b4df-44b5-a0d1-eda4c361255e` built the file with Lake from the workspace and
  inspected `GaloisCohomologyUnramifiedStatement`: a `Prop`-valued
  definition with the universe parameter `u`, depending only on `propext`, `Classical.choice` and
  `Quot.sound` (type hash `51b46f1d424817b9b246643699c08a78d18823c7aadc4e7708ba608a8f63b968`).

This establishes a well-formed statement. It does not prove it.
