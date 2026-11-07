# Algebraization of formally versal Picard families: statement

Module: `Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This module contains one proposition, `VersalAlgebraizationStatement.{u}`,
which is not proved here. It is an intermediate statement for the proof of
the published `FiniteTypePicardStackAtlasStatement`. It specializes Stacks
Lemma 98.12.7 (algebraization of a versal effective formal object at a
finite type point) to the actual Picard groupoid and to bases of finite type
over `ℤ`, starting from an actual line bundle over a complete local base.
Together with the companion statement
`FiniteTypeFormalVersalBundleStatement`, which supplies such a line bundle
over every line bundle on a finite type field fibre, it gives the published
`FiniteTypeVersalChartStatement`.

## The statement

`VersalAlgebraizationStatement.{u}` quantifies over

- every commutative ring `R : Type u` of finite type over `ℤ`;
- every scheme `X : Over (Spec R)` with `X.hom` proper and flat;
- every field `K : Type u` with an `R`-algebra structure such that `K` is
  of finite type over `R` (`Algebra.FiniteType R K`);
- every commutative ring `A : Type u` that is Noetherian, local, and complete
  and Hausdorff for its maximal-ideal-adic topology
  (`IsAdicComplete (IsLocalRing.maximalIdeal A) A`), with an `R`-algebra
  structure;
- every surjective `R`-algebra map `ε : A →ₐ[R] K`; its kernel is the
  maximal ideal of `A`, so `ε` identifies the residue field of `A` with `K`
  over `R`;
- every actual line bundle `L` on `Spec A ×_{Spec R} X`, where `Spec A` lies
  over `Spec R` through `algebraMap R A`;
- every morphism `p : ArtinianTest.residueBase R K ⟶ Spec A` over `Spec R`
  with `p.left = Spec.map ε`, that is, the closed point of `Spec A` viewed as
  a `K`-point through `ε`. Here `ArtinianTest.residueBase R K` is `Spec K`
  over `Spec R` through `algebraMap R K`;

and assumes that
`PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p` holds.

Its conclusion is the existence of

- a scheme `U` over `Spec R`;
- an actual line bundle `L'` on `U ×_{Spec R} X`;
- a point `u₀` of `U` and an isomorphism of rings
  `e : κ(u₀) ≅ K` (`U.left.residueField u₀ ≅ CommRingCat.of K`);
- a morphism `p' : ArtinianTest.residueBase R K ⟶ U` over `Spec R`

such that

1. `p'.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀`: the point
   `p'` is the canonical morphism `Spec κ(u₀) ⟶ U` of `u₀`, transported to
   `Spec K` along `e`. Since `p'` lies over `Spec R`, this forces `e` to be
   an isomorphism of `R`-algebras, for the `R`-algebra structure of `κ(u₀)`
   coming from `U → Spec R`. So `u₀` is a point of `U` with residue field
   `K` over `R`;
2. `U.hom` is locally of finite type;
3. `IsFormallyVersalAt X.hom L' p'` holds;
4. there is an isomorphism
   `ArtinianChartVersality.residueBundle X.hom L' p' ≅
   ArtinianChartVersality.residueBundle X.hom L p`. The published
   `residueBundle X.hom L p` is the pullback of `L` along
   `(relativeSpace X.hom).map p : Spec K ×_{Spec R} X ⟶ Spec A ×_{Spec R} X`,
   and likewise for `L'` and `p'`.

### The versality predicate

`IsFormallyVersalAt X.hom L p` is the published Library predicate, used for
the chart `Spec A` in the hypothesis and for the chart `U` in the
conclusion. Its tests are the published `ArtinianTest R K`: local Artinian
`R`-algebras `B` with a surjective `R`-algebra map `B → K` (the
augmentation, whose kernel is the maximal ideal), and augmentation-preserving
`R`-algebra maps between them. For a chart `V` over `Spec R`, a line bundle
`N` on `V ×_{Spec R} X` and a `K`-point `v : Spec K ⟶ V` over `Spec R`, the
predicate `IsFormallyVersalAt X.hom N v` says: for every test arrow
`q : B ⟶ B'` whose algebra map `B → B'` is surjective, for every scheme `T`
over `Spec R`, every actual line bundle `M` on `T ×_{Spec R} X`, every
`a : Spec B ⟶ T` over `Spec R` with `b = Spec q ≫ a`, and every actual point
`y` of the point fibre of `N` and `M` over `Spec B'` (via `b`) whose chart
map `Spec B' ⟶ V` restricts to `v` on the residue point `Spec K ⟶ Spec B'`,
there is an actual point `x` over `Spec B` (via `a`) whose restriction along
`Spec q` is `y`. A point of the point fibre over `Spec B` is a morphism
`Spec B ⟶ V` over `Spec R` together with an isomorphism of the pullbacks of
`N` and `M` to `Spec B ×_{Spec R} X`; the lift `x` keeps both the chart map
and the isomorphism.

For the chart `Spec A`, a morphism `Spec B' ⟶ Spec A` restricting to `p` is
an `R`-algebra map `A → B'` lifting `ε`; it factors through `A/𝔪ⁿ` for some
`n`, since the maximal ideal `𝔪` of `A` maps into the nilpotent maximal ideal
of `B'`. So the hypothesis is versality of the formal object
`ξ = (A, ξₙ = L|_{Spec(A/𝔪ⁿ) ×_{Spec R} X})` in the sense of the lifting
condition spelled out after Stacks Definition 98.12.1, and `ξ` is effective,
since it is the formal object of the actual line bundle `L`.

## Source and derivation

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06` (chapter PDFs of version
ed88ff78). Within `artin.pdf`, Chapter 98 "Artin's Axioms" is numbered
internally without the chapter prefix.

- **`artin.pdf`, Lemma 98.12.7 (Tag 07XH), printed as Lemma 12.7, p. 20.**
  For a locally Noetherian base `S` and a category fibred in groupoids `𝒳`,
  let `ξ = (R', ξₙ, fₙ)` be a formal object of `𝒳` with `ξ₁` over
  `Spec k → S`, with image `s ∈ S`. Assume `ξ` is versal, `ξ` is effective,
  `𝒪_{S,s}` is a G-ring, and `𝒳` is limit preserving on objects. Then there
  are a morphism of finite type `U → S`, a finite type point `u₀ ∈ U` with
  residue field `k`, and an object `x` of `𝒳` over `U` such that `x` is
  versal at `u₀` and `x|_{Spec(𝒪_{U,u₀}/𝔪ⁿ)} ≅ ξₙ`. Its proof (pp. 20–21)
  applies Lemma 98.10.1 (Artin approximation) with `N = 2` to an object
  `x_{R'}` over `Spec R'` whose formal object is `ξ`, and concludes with
  Lemma 98.12.3.
- **`artin.pdf`, Definition 98.12.1 (Tag 0CXJ), printed p. 18**: versality
  of a formal object, spelled out after the definition as the lifting
  condition recalled above.
- **`artin.pdf`, Definition 98.12.2 (Tag 07XF), printed p. 18**: `x` is
  versal at a finite type point `u₀` if the induced morphism of
  predeformation categories `x̂ : F_{(Sch/U),k,u₀} → F_{𝒳,k,x₀}` is smooth
  (Formal Deformation Theory, Definition 8.1). Unwinding smoothness of
  categories cofibred in groupoids over Artinian local algebras with residue
  field `k`, this is the lifting property of the published
  `IsFormallyVersalAt` at the point `p'` of `u₀`: an object of
  `F_{(Sch/U),k,u₀}` over `B` is a morphism `Spec B → U` restricting to the
  given `Spec k → U`, and every object of the Picard stack over `Spec B` is
  the pullback of some `(T, M)` along some `a`.
- **`artin.pdf`, Example 98.12.8 (Tag 07XI), printed p. 21**, shows that
  the G-ring hypothesis of Lemma 98.12.7 cannot be dropped in general.

The Picard stack is that of the published target statement; its source is
`stacks-picard-stack-algebraicity-2026-11-01` (`0372.html`, Section 95.16).

### Specialization

Take `S = Spec R` and `𝒳` the Picard stack of `X → S`. The base is
Noetherian, and the local rings of a scheme of finite type over `ℤ` are
G-rings, so the hypotheses on `S` hold. The Picard stack of a proper, hence
finitely presented, morphism over a Noetherian base is limit preserving on
objects. A finite type field over `S` is a field `K` of finite type over
`R`. The formal object `ξ` is that of `L`, over `R' = A` with residue field
identified with `K` by `ε`; it is versal by hypothesis and effective by
construction. The G-ring property and limit preservation are proof
obligations, not hypotheses.

The conclusion of Lemma 98.12.7 gives `U`, `u₀` with an identification of
its residue field with `k` over `S`, which is the pair `u₀`, `e` with
condition 1, the object `x` (the line bundle `L'`), versality at `u₀`
(condition 3), and `x|_{u₀} ≅ ξ₁` (the case `n = 1`, condition 4, where
`ξ₁` is `residueBundle X.hom L p`).

The Lean statement weakens the source conclusion only in that `U → S` of
finite type is weakened to locally of finite type, and it omits the
identifications with `ξₙ` for `n ≥ 2`, which are not needed downstream.
Flatness of `X → Spec R` is assumed for uniformity with the target
statement; the source argument does not use it. The statement is therefore
a derived specialization of Lemma 98.12.7, not a verbatim single source
assertion. Its proof requires Artin approximation over the henselizations of
the local rings of finite-type `ℤ`-algebras (Lemma 98.10.1 in the same
chapter) or an equivalent algebraization argument.

## Scope

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and zero rings, and every proper flat
scheme over `Spec R`. It assumes no projectivity, smoothness, connectedness,
section or cohomological flatness, and no finiteness of `A` over `R`. It
asserts nothing about versality at points of `U` other than `u₀`, and
nothing about smoothness of `L'`.
