# Formally versal Picard families over complete local bases: statement

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleStatement`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This module contains one proposition,
`FiniteTypeFormalVersalBundleStatement.{u}`, which is not proved here. It is
an intermediate statement for the proof of the published
`FiniteTypePicardStackAtlasStatement`. It states the first step of the proof
of Stacks Lemma 98.13.8 for the actual Picard groupoid over a base of finite
type over `ℤ`: every line bundle on a finite type field fibre is the residue
of an effective versal formal object. Together with the companion statement
`VersalAlgebraizationStatement` (algebraization of such an object, Stacks
Lemma 98.12.7), it gives the published `FiniteTypeVersalChartStatement`.

## The statement

`FiniteTypeFormalVersalBundleStatement.{u}` quantifies over

- every commutative ring `R : Type u` of finite type over `ℤ`;
- every scheme `X : Over (Spec R)` with `X.hom` proper and flat;
- every field `K : Type u` with an `R`-algebra structure such that `K` is
  of finite type over `R` (`Algebra.FiniteType R K`);
- every actual line bundle `L₀` on
  `(relativeSpace X.hom).obj (ArtinianTest.residueBase R K)`, that is, on
  `Spec K ×_{Spec R} X`. Here `ArtinianTest.residueBase R K` is `Spec K`
  over `Spec R` through `algebraMap R K`.

Its conclusion is the existence of

- a commutative ring `A : Type u` that is Noetherian, local, and complete
  and Hausdorff for its maximal-ideal-adic topology
  (`IsAdicComplete (IsLocalRing.maximalIdeal A) A`), with an `R`-algebra
  structure;
- an `R`-algebra map `ε : A →ₐ[R] K`;
- an actual line bundle `L` on `Spec A ×_{Spec R} X`, where `Spec A` lies
  over `Spec R` through `algebraMap R A`;
- a morphism `p : ArtinianTest.residueBase R K ⟶ Spec A` over `Spec R`

such that

1. `ε` is surjective. Its kernel is then a maximal ideal, hence the maximal
   ideal of `A`, so `ε` identifies the residue field of `A` with `K` over
   `R`;
2. `p.left = Spec.map ε`: `p` is the closed point of `Spec A`, viewed as a
   `K`-point through `ε`;
3. `PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p`
   holds (described below);
4. there is an isomorphism `ArtinianChartVersality.residueBundle X.hom L p ≅ L₀`.
   The published `residueBundle X.hom L p` is the pullback of `L` along
   `(relativeSpace X.hom).map p : Spec K ×_{Spec R} X ⟶ Spec A ×_{Spec R} X`.

### The versality predicate

`IsFormallyVersalAt X.hom L p` is the published Library predicate, here for
the chart `U = Spec A`. Its tests are the published `ArtinianTest R K`:
local Artinian `R`-algebras `B` with a surjective `R`-algebra map `B → K`
(the augmentation, whose kernel is the maximal ideal), and
augmentation-preserving `R`-algebra maps between them. The predicate says:
for every test arrow `q : B ⟶ B'` whose algebra map `B → B'` is surjective,
for every scheme `T` over `Spec R`, every actual line bundle `M` on
`T ×_{Spec R} X`, every `a : Spec B ⟶ T` over `Spec R` with
`b = Spec q ≫ a`, and every actual point `y` of the point fibre of `L` and
`M` over `Spec B'` (via `b`) whose chart map `Spec B' ⟶ Spec A` restricts to
`p` on the residue point `Spec K ⟶ Spec B'`, there is an actual point `x`
over `Spec B` (via `a`) whose restriction along `Spec q` is `y`. A point of
the point fibre over `Spec B` is a morphism `Spec B ⟶ Spec A` over `Spec R`
together with an isomorphism of the pullbacks of `L` and `M` to
`Spec B ×_{Spec R} X`; the lift `x` keeps both the chart map and the
isomorphism.

For `U = Spec A` this is versality of the formal object of `L`. A morphism
`Spec B' ⟶ Spec A` over `Spec R` restricting to `p` is an `R`-algebra map
`φ : A → B'` with `B' → K` composed with `φ` equal to `ε`. Such a `φ` maps
the maximal ideal `𝔪` of `A` into the nilpotent maximal ideal of `B'`, so it
factors through `A/𝔪ⁿ` for some `n`. A point `y` is therefore a morphism from
the truncation `ξₙ = L|_{Spec(A/𝔪ⁿ) ×_{Spec R} X}` of the formal object of `L`
to the object over `Spec B'` given by `M` and `b`, and the lift `x` is a
morphism from some `ξₘ` with `m ≥ n` extending it. This is the lifting
condition spelled out after Stacks Definition 98.12.1.

## Source and derivation

The sources are The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06` (chapter PDFs of version
ed88ff78; Chapter 98 "Artin's Axioms" is `artin.pdf`, numbered internally
without the chapter prefix) and
`stacks-formal-deformation-theory-2026-11-06` (`formal-defos.pdf`,
Chapter 90 "Formal Deformation Theory", numbered the same way).

- **`artin.pdf`, proof of Lemma 98.13.8 (Tag 07XY), printed p. 24.** For a
  category fibred in groupoids `𝒳` over a locally Noetherian `S` and an
  object `x₀` of `𝒳` over a finite type field `Spec k → S`: by axiom [2]
  (Rim–Schlessinger), `F_{𝒳,k,x₀}` satisfies (S1) and (S2); since its
  tangent space is finite dimensional (axiom [3]), Formal Deformation Theory
  Lemma 13.4 gives a versal formal object `ξ` of `F_{𝒳,k,x₀}`; assumption
  (3) of that lemma says that `ξ` is effective. This statement records the
  resulting effective versal formal object for the Picard stack.
- **`formal-defos.pdf`, Lemma 90.13.4 (Tag 06IW), printed as Lemma 13.4,
  p. 39.** A predeformation category `F` over `𝒞_Λ` satisfying (S1), (S2)
  and `dim_k T_F < ∞` has a versal formal object. Its base is an object of
  `\hat{𝒞}_Λ`: a complete Noetherian local `Λ`-algebra with residue field
  `k`.
- **`artin.pdf`, Definition 98.12.1 (Tag 0CXJ), printed p. 18**: a formal
  object `ξ = (R', ξₙ, fₙ)` of `𝒳` is versal if it is versal as a formal
  object of `F_{𝒳,k,ξ₁}`; the text after the definition spells this out as
  the lifting condition recalled above.
- **`artin.pdf`, Lemma 98.12.3 (Tag 0CXK), printed pp. 18–19.** For `U`
  locally of finite type over `S`, a finite type point `u₀` and `x` over
  `U`, `x` is versal at `u₀` if and only if the formal object of
  `x|_{Spec \hat{𝒪}_{U,u₀}}` is versal. Its proof identifies the morphisms
  `\hat{𝒪}_{U,u₀} → B` of `\hat{𝒞}_Λ` with the morphisms `Spec B → U`
  restricting to `u₀`. The same identification for `U = Spec A`, `A`
  complete local, is the unwinding given above. `Spec A` is not of finite
  type over `S`, so this use is derived from the proof, not an instance of
  the lemma.

The Picard stack is that of the published target statement; its source is
`stacks-picard-stack-algebraicity-2026-11-01` (`0372.html`, Section 95.16).

### Specialization

Take `S = Spec R` and `𝒳` the Picard stack of `X → S`. A finite type field
over `S` is a field `K` of finite type over `R`, and `x₀` is the line bundle
`L₀`. For this `𝒳`, the Rim–Schlessinger condition holds, the tangent space
`H¹(X_K, 𝒪)` is finite dimensional because `X_K` is proper over `K`, and
formal objects are effective by Grothendieck's existence theorem (published
in the Library as `ProperFormalLineBundleEffectivityStatement`; Stacks
Proposition 30.25.4, Tag 088C, registered as
`stacks-formal-line-bundle-effectivity-2026-11-03`, `088C.html`). The statement asserts the conclusion for
every `L₀`; these facts are proof obligations, not hypotheses.

The effective versal formal object `ξ` over a complete Noetherian local
`R`-algebra with residue field `K` becomes, in Lean, the ring `A` with `ε`
(conditions 1 and 2), the actual line bundle `L` on `X_A` whose formal object
is `ξ` (effectivity), versality (condition 3, through the unwinding above)
and `ξ₁ ≅ x₀` (condition 4).

The statement is therefore a derived statement combining Lemma 90.13.4 with
effectivity as in the proof of Lemma 98.13.8; it is not a verbatim single
source assertion. Effectivity is built in by asking directly for a line
bundle over `Spec A ×_{Spec R} X` rather than for a formal object together
with an algebraization. Flatness of `X → Spec R` is assumed for uniformity
with the target statement; the source argument does not use it.

## Scope

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and zero rings (for the zero ring it is
vacuous, since there is no field `K` over it), and every proper flat scheme
over `Spec R`. It assumes no projectivity, smoothness, connectedness,
section or cohomological flatness. It does not ask that `A` be of finite
type over `R`, and asserts nothing about points of `Spec A` other than the
closed point.
