# Unramified Galois actions on étale cohomology outside a uniform set of places

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `GaloisCohomologyGoodReductionStatement`.
Let `K` be a number field and `f : X ⟶ Spec K` a smooth proper morphism.
Worker 13's published `Langlands.Geometry.EtaleGaloisAction` lets the
absolute Galois group `Gal(K̄/K)` act on the étale cohomology of
`X_K̄ = X ×_{Spec K} Spec K̄` with constant coefficients. The proposition
says that there is one finite set `S` of finite places of `K`, chosen before
the coefficients, such that for every finite coefficient module `M` and
every degree `n` the action on `H^n(X_K̄, M)` is unramified at every finite
place `v ∉ S` at which the order of `M` is a unit. Unramifiedness is the
predicate `IsUnramifiedAt` of the published
`Langlands.Shimura.DecompositionGroupAction`. Nothing is proved here.

The companion statement `GaloisCohomologyUnramifiedStatement` (module
`Langlands.Cohomology.EtaleGaloisUnramified.Statement`, candidate
`c1c7da7d-650b-424c-a2c5-a19a36cab4c0` by the same author, approved and not
yet in Library `568f1cff`) holds for every finite-type `X`, but its set of
places may depend on `M`. The present statement asks for more on smooth
proper `X`: one set `S` for all `M`, apart from the places dividing the
order of `M`. This uniformity is what an `ℓ`-adic representation needs:
for a fixed prime `ℓ` and the coefficients `ℤ/ℓ^k` for all `k`, the
exceptional set is `S` together with the places above `ℓ`.

## Objects

All types live in one universe `u`.

- `K` is a field with `[NumberField K]`.
- `f : X ⟶ Spec (CommRingCat.of K)` is a morphism of Mathlib schemes with
  `[Smooth f]` and `[IsProper f]`. Mathlib's `Smooth` asks that `f` be
  smooth on affine opens (the ring maps are smooth), and `IsProper` that
  `f` be separated, universally closed and locally of finite type.
- `R` is a commutative ring. `M : ModuleCat R` is quantified inside the
  proposition with the instance `[Finite M]`: the underlying set of `M` is
  finite. `Nat.card M` is its cardinality. `n : ℕ` is the degree.
- `galoisCohomologyRep (L := AlgebraicClosure K) f R M n` is Worker 13's
  representation of `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` on the
  degree-`n` étale cohomology of `X_K̄ := baseChange K (AlgebraicClosure K) f`
  with coefficients in the constant sheaf of `M`, computed in sheaves of
  `R`-modules on Mathlib's small étale site (Worker 13's
  `Langlands.Geometry.EtaleDerivedSections`). The published
  [EtaleGaloisSmooth](../EtaleGaloisSmooth/Statement.md) explains the
  action: `σ` acts by the pullback along `baseChangeMap f σ`, the identity
  on `X` times `Spec σ` on `Spec K̄`.
- In Mathlib commit `5ed29652` the category `Rep R G` is a structure.
  Mathlib's functor `Rep.RepToAction` turns the representation into an
  object of `Action (ModuleCat R) G` with the same module and the same
  linear action. Here `G = Field.absoluteGaloisGroup K`, which Mathlib
  defines as `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` with the same
  group structure.
- `Global.FinitePlace K` is the Library's type of finite places, the
  height-one primes of the ring of integers `𝓞 K`, and `v.asIdeal` is the
  prime ideal of `v`. The condition
  `(Nat.card M : 𝓞 K) ∉ v.asIdeal` says that the order of `M` is a unit in
  the residue field of `v`, that is, the residue characteristic of `v` does
  not divide the order of `M`.
- `DecompositionGroupAction.IsUnramifiedAt V v A` says that every element of
  `localInertia v`, the kernel of the action of the absolute Galois group of
  the completion `K_v` on the residue field of its algebraic closure (Worker
  41's `Langlands.Galois.CompatibleFamily`), acts trivially on `A` after
  restriction to `Gal(K̄/K)` along Mathlib's chosen closure embedding. The
  published theorem `isUnramifiedAlong_iff` shows that the condition does
  not depend on the closure embedding.

## The proposition

```lean
def GaloisCohomologyGoodReductionStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IsProper f]
    (R : Type u) [CommRing R] : Prop :=
  ∃ S : Set (Global.FinitePlace K), S.Finite ∧
    ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ) (v : Global.FinitePlace K), v ∉ S →
      ((Nat.card M : NumberField.RingOfIntegers K) ∉ v.asIdeal) →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))
```

In words: there is a finite set `S` of finite places of `K` such that for
every finite `R`-module `M`, every degree `n` and every finite place
`v ∉ S` whose residue characteristic does not divide the order of `M`, the
inertia subgroup at `v` acts trivially on `H^n(X_K̄, M)`. The set `S` comes
before `M` and `n` in the quantifiers, so it does not depend on them.

## Relation to the almost-everywhere statement

The test lemma `unramified_of_goodReduction` of check `5d1a92cd` (below)
proves, for smooth proper `f`, that this proposition implies
`GaloisCohomologyUnramifiedStatement K f R`. For given `M`, it adds to `S`
the places `v` with `(Nat.card M : 𝓞 K) ∈ v.asIdeal`. These are finitely
many, because `Nat.card M` is a nonzero element of `𝓞 K` and only finitely
many height-one primes divide a nonzero ideal (Mathlib's
`Ideal.finite_factors`). The converse does not follow formally.

## Why the statement is expected to hold

This argument is derived from the cited sources; none of them states the
proposition in this form.

1. *Spreading out.* `Spec K` is the limit of the affine schemes
   `Spec O_K[1/N]`, `N ≥ 1`. Since `K` is noetherian, `f` is of finite
   presentation. By Stacks Lemma 32.10.1 (tag 01ZM), part (1), there are
   `N` and a morphism of finite presentation `f_N : 𝒳 → Spec O_K[1/N]`
   whose base change to `Spec K` is `X`. After enlarging `N`, `f_N` is
   smooth (Stacks tag 0C0C, `lemma-descend-smooth`) and proper (Stacks tag
   081F, `lemma-eventually-proper`). Let `S` be the finite set of places
   dividing `N`. It depends only on `f`.
2. *A fixed coefficient module.* Let `M` be finite, `e` its cardinality, and
   `v ∉ S` a place whose residue characteristic does not divide `e`. Let
   `Y = Spec O_K[1/(N e)]`, an open subscheme of `Spec O_K` containing `v`,
   and `f_Y : 𝒳_Y → Y` the base change of `f_N`, again smooth and proper.
   The constant sheaf of `M` on `𝒳_Y` is a constructible abelian sheaf
   (SGA 4 IX 2.3) of `e`-torsion, and every prime dividing `e` is
   invertible on `Y`. The cohomology of a sheaf of `R`-modules is that of its
   underlying abelian sheaf: injective sheaves of `R`-modules are flasque
   (SGA 4 V 4.6), flasqueness depends only on the underlying abelian sheaf
   (V 4.4), and flasque sheaves have no higher cohomology (V 4.1).
3. *Specialization.* By SGA 4 XVI Corollaire 2.2, applied to `f_Y` and the
   constant sheaf `M`, the sheaf `G = R^n f_{Y*} M` is constructible and
   locally constant on `Y`, and for every geometric point `ȳ` of `Y`,
   `G_ȳ ≅ H^n(𝒳_ȳ, M)`. Its fibres are finite, so it is represented by a
   finite étale covering of `Y` (SGA 4 IX 2.2).
4. *The geometric generic stalk.* For the geometric point
   `η̄ : Spec K̄ → Y` given by `K ⊂ K̄`, step 3 gives
   `G_η̄ ≅ H^n(𝒳 ×_{Spec O_K[1/N]} Spec K̄, M) = H^n(X_K̄, M)`. For
   `σ ∈ Gal(K̄/K)`, `Spec σ` is an automorphism of `η̄` over `Y`, and the
   identification is natural in the geometric point. Hence the action of
   `σ` on `G_η̄` is the pullback along `baseChangeMap f σ`, the Library's
   action, possibly up to replacing `σ` by `σ⁻¹`. Such an inversion does not
   change which subgroup acts trivially.
5. *Inertia acts trivially.* By SGA 1 V §7 and IX 2.2, `Gal(K̄/K)` acts on
   `G_η̄` through `π_1(Spec K, η̄) → π_1(Y, η̄)`. `Y` is connected,
   noetherian and normal, so by SGA 1 V Proposition 8.2 the kernel of this
   map corresponds to the composite of the finite extensions of `K` inside
   `K̄` that are unramified over `Y`. This composite is generated by finite
   Galois subextensions `L` unramified over `Y`. Let `ι` be a closure
   embedding at `v` and `g ∈ localInertia v`. The extension `ι(L) K_v` of
   `K_v` is finite, Galois and unramified, so its Galois group maps
   isomorphically onto that of its residue extension, and `g` fixes it
   pointwise. As `ι (σ x) = g (ι x)` for `σ = localRestriction v ι g`
   (`localRestriction_commutes`) and `ι` is injective, `σ` fixes `L`. So `σ`
   acts trivially on `G_η̄ = H^n(X_K̄, M)`.

Steps 2 to 5 hold for every `M` and every admissible `v` with the same `S`,
which proves the proposition.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §5, printed p.313: "we will be considering λ-adic representations
σ of Gal(F̄/F) which are unramified at all but finitely many places and pure
of weight m". Theorem 5.7 (ii) (p.313) and Theorem 5.9 (i) (p.315) concern
"almost all places", for representations realized on the cohomology of
unitary Shimura varieties; Harris attributes these parts to Kottwitz and
Clozel (pp.314-315).

The proposition is the unramifiedness input to such `λ`-adic statements,
for a different object:

- the cohomology is that of an arbitrary smooth proper scheme over a
  number field, with constant coefficients, not that of Harris's Shimura
  varieties `S_K(N)` with the coefficient systems `W`;
- the coefficients are finite modules. The `λ`-adic representation itself,
  an inverse limit over torsion levels, is not constructed here. The
  proposition gives the uniform exceptional set such a limit needs;
- nothing is said about purity, Frobenius eigenvalues or Euler factors, or
  about which places lie in `S`.

| Lean | Source |
| --- | --- |
| `∃ S, S.Finite ∧ ∀ M n v, v ∉ S → ... → IsUnramifiedAt ...` | Harris 1999 §5, p.313, "unramified at all but finitely many places", for all torsion levels at once |
| `[Smooth f] [IsProper f]` | "un morphisme propre et lisse" in SGA 4 XVI Cor. 2.2, after spreading out (Stacks 01ZM, 0C0C, 081F) |
| `(Nat.card M : 𝓞 K) ∉ v.asIdeal` | the torsion of the coefficients is prime to the residue characteristic, as in SGA 4 XVI Cor. 2.2 |

## Scope and relation to other modules

The statement does not cover:

- the `λ`-adic or rational cohomology itself, or non-constant coefficient
  sheaves, or compactly supported cohomology;
- schemes that are not smooth and proper, for which see the companion
  `GaloisCohomologyUnramifiedStatement`;
- the cohomology modules of the Library's CM towers, which are colimits
  over levels with coefficients pulled back from `Spec F` and are built
  separately; `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`
  (no Author line) takes their unramifiedness as a hypothesis;
- any description of `S`, such as the places of bad reduction of a model;
- Frobenius eigenvalues, purity, or local-global compatibility.

Related Library declarations: the published
[EtaleGaloisSmooth](../EtaleGaloisSmooth/Statement.md) states that the same
Galois action is smooth for the Krull topology;
`Langlands.Shimura.DecompositionGroupAction` (no Author line) defines
`IsUnramifiedAt` and proves its independence of the closure embedding, but
proves unramifiedness of no specific object.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; §5,
  printed p.313 (PDF p.15), Theorem 5.7 (pp.313-314) and Theorem 5.9 (i)
  (p.315, PDF p.17), read in the text layer. Provenance only.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305, original scan, PDF SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`
  (PDF page = printed page + 3); Exposé XVI (Artin), Corollaire 2.2, printed
  p.214 (PDF p.217), and Exposé IX (Artin) 2.2 (printed p.8) and
  Définition 2.3 (pp.8-9), read on rendered page images. Truth argument.
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
  line 2370) part (1), tag 0C0C (label `lemma-descend-smooth`, line 1931)
  and tag 081F (label `lemma-eventually-proper`, line 3265). Truth
  argument.

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
and `Langlands.Galois.CompatibleFamily` (`localInertia`). The module does
not import `Langlands.Cohomology.EtaleGaloisUnramified.Statement`. The
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `568f1cff`, on the final Lean file (SHA-256
`0acfa9a65ceccf612c6481eefc75545b5c6ec2b185024be5cdf2b42215addfca`). None reported errors or warnings.

- `5d1a92cd-a9be-42e0-a4ee-cbc389c9dccc` compiled the file from a draft directory together with the
  workspace module `Langlands.Cohomology.EtaleGaloisUnramified.Statement`
  and a test file (`Langlands/Inspect/EtaleGaloisGoodReductionPrint.lean`,
  SHA-256 `d492f622d8560b0eefa4eec510f62fb57b33d548d4c109ba1dafd657cdd2094e`), neither part of the candidate. It printed
  `GaloisCohomologyGoodReductionStatement` with universes: a `Prop`-valued
  definition with the single universe parameter `u`. It proved
  `unramified_of_goodReduction`, which depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `2a25bb4a-4ef5-456d-92a8-1d0ab021c202` built the file with Lake from the workspace and
  inspected `GaloisCohomologyGoodReductionStatement`: a `Prop`-valued
  definition with the universe parameter `u`, depending only on `propext`,
  `Classical.choice` and `Quot.sound` (type hash `3b913245f583e2c2750a2174407c91e063aec80754e9b65340aae5dbaa648f8d`).

This establishes a well-formed statement. It does not prove it.
