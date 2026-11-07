# Versal Picard charts at finite-type field points: statement

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartStatement`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This module contains one proposition, `FiniteTypeVersalChartStatement.{u}`,
which is not proved here. It is an intermediate statement for the proof of
the published `FiniteTypePicardStackAtlasStatement`. It specializes Stacks
Lemma 98.12.7 (algebraization of a versal effective formal object at a
finite type point) to the actual Picard groupoid and to bases of finite type
over `ℤ`. Together with the companion statement
`VersalSmoothNeighbourhoodStatement`, it gives the published
`FiniteTypePointSmoothChartStatement`; see the module
`FiniteTypePointSmoothChartReduction`.

## The statement

`FiniteTypeVersalChartStatement.{u}` quantifies over

- every commutative ring `R : Type u` of finite type over `ℤ`;
- every scheme `X : Over (Spec R)` with `X.hom` proper and flat;
- every field `K : Type u` with an `R`-algebra structure such that `K` is
  of finite type over `R` (`Algebra.FiniteType R K`);
- every actual line bundle `L₀` on
  `(relativeSpace X.hom).obj (ArtinianTest.residueBase R K)`, that is, on
  `Spec K ×_{Spec R} X`. Here `ArtinianTest.residueBase R K` is `Spec K`
  over `Spec R` through `algebraMap R K`.

Its conclusion is the existence of

- a scheme `U` over `Spec R` with `U.hom` locally of finite type;
- an actual line bundle `L` on `U ×_{Spec R} X`;
- a point `u₀` of `U` and an isomorphism of rings
  `e : κ(u₀) ≅ K` (`U.left.residueField u₀ ≅ CommRingCat.of K`);
- a morphism `p : ArtinianTest.residueBase R K ⟶ U` over `Spec R`

such that

1. `p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀`: the point
   `p` is the canonical morphism `Spec κ(u₀) ⟶ U` of `u₀`, transported to
   `Spec K` along `e`. Since `p` lies over `Spec R`, this forces `e` to be
   an isomorphism of `R`-algebras, for the `R`-algebra structure of `κ(u₀)`
   coming from `U → Spec R`. So `u₀` is a point of `U` with residue field
   `K` over `R`;
2. `U.hom` is locally of finite type;
3. `PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p`
   holds (described below);
4. there is an isomorphism `ArtinianChartVersality.residueBundle X.hom L p ≅ L₀`.
   The published `residueBundle X.hom L p` is the pullback of `L` along
   `(relativeSpace X.hom).map p : Spec K ×_{Spec R} X ⟶ U ×_{Spec R} X`.

### The versality predicate

`IsFormallyVersalAt X.hom L p` is the published Library predicate. Its tests
are the published `ArtinianTest R K`: local Artinian `R`-algebras `A` with a
surjective `R`-algebra map `A → K` (the augmentation, whose kernel is the
maximal ideal), and augmentation-preserving `R`-algebra maps between them.
The predicate says: for every test arrow `q : A ⟶ B` whose algebra map
`A → B` is surjective, for every scheme `T` over `Spec R`, every actual line
bundle `M` on `T ×_{Spec R} X`, every `a : Spec A ⟶ T` over `Spec R` with
`b = Spec q ≫ a`, and every actual point `y` of the point fibre of `L` and
`M` over `Spec B` (via `b`) whose chart map `Spec B ⟶ U` restricts to `p` on
the residue point `Spec K ⟶ Spec B`, there is an actual point `x` over
`Spec A` (via `a`) whose restriction along `Spec q` is `y`. A point of the
point fibre over `Spec A` is a morphism `Spec A ⟶ U` over `Spec R` together
with an isomorphism of the pullbacks of `L` and `M` to `Spec A ×_{Spec R} X`;
the lift `x` keeps both the chart map and the isomorphism.

## Source and derivation

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06` (chapter PDFs of version
ed88ff78). Within `artin.pdf`, Chapter 98 "Artin's Axioms" is numbered
internally without the chapter prefix.

- **`artin.pdf`, Lemma 98.12.7 (Tag 07XH), printed as Lemma 12.7, p. 20.**
  For a locally Noetherian base `S` and a category fibred in groupoids `𝒳`,
  let `ξ` be a formal object of `𝒳` over a complete local ring `R'` with
  `ξ₁` over `Spec k → S`, with image `s ∈ S`. Assume `ξ` is versal, `ξ` is
  effective, `𝒪_{S,s}` is a G-ring, and `𝒳` is limit preserving on
  objects. Then there are a morphism of finite type `U → S`, a finite type
  point `u₀ ∈ U` with residue field `k`, and an object `x` of `𝒳` over `U`
  such that `x` is versal at `u₀` and `x|_{Spec(𝒪_{U,u₀}/𝔪ⁿ)} ≅ ξₙ`.
- **`artin.pdf`, Definition 98.12.2 (Tag 07XF), printed p. 18**: `x` is
  versal at a finite type point `u₀` if the induced morphism of
  predeformation categories `x̂ : F_{(Sch/U),k,u₀} → F_{𝒳,k,x₀}` is smooth
  (Formal Deformation Theory, Definition 8.1). Unwinding smoothness of
  categories cofibred in groupoids over Artinian local algebras with residue
  field `k`, this is the lifting property of the published
  `IsFormallyVersalAt` at the point `p` of `u₀` described above: an object
  of `F_{(Sch/U),k,u₀}` over `A` is a morphism `Spec A → U` restricting to
  the given `Spec k → U`, and every object of the Picard stack over `Spec A`
  is the pullback of some `(T, M)` along some `a`.
- **`artin.pdf`, Lemma 98.13.8 (Tag 07XY), printed as Lemma 13.8**, uses
  Lemma 98.12.7 together with openness of versality to produce smooth
  charts; the published `FiniteTypePointSmoothChartStatement` specializes
  it, and this statement isolates its first step.

The Picard stack is that of the published target statement; its source is
`stacks-picard-stack-algebraicity-2026-11-01` (`0372.html`, Section 95.16).

### Specialization

Take `S = Spec R` and `𝒳` the Picard stack of `X → S`. The base is
Noetherian, and the local rings of a scheme of finite type over `ℤ` are
G-rings, so the hypotheses on `S` hold. A finite type field over `S` is a
field `K` with `Spec K → Spec R` of finite type, that is, a field of finite
type over `R`. An object `x₀` over `Spec K` is the line bundle `L₀`.

Lemma 98.12.7 needs a versal effective formal object `ξ` with `ξ₁ ≅ x₀`.
For the Picard stack it exists. The proof of Lemma 98.13.8 (printed
p. 24) obtains a versal formal object from the Rim–Schlessinger condition
(axiom [2]) and a finite-dimensional tangent space (axiom [3]), citing
Formal Deformation Theory, Lemma 13.4. Formal objects of the Picard stack of
the proper morphism `X → S` are effective by Grothendieck's existence
theorem. The statement asserts the conclusion for every `L₀`; these
facts are proof obligations, not hypotheses.

The conclusion of Lemma 98.12.7 gives `U`, `u₀` with an identification of
its residue field with `k` over `S`, which is the pair `u₀`, `e` with
condition 1, the object `x` (the line bundle `L`), versality at `u₀`
(condition 3), and `x|_{u₀} ≅ ξ₁ ≅ x₀` (the case `n = 1`, condition 4).

The Lean statement weakens the source conclusion only in that `U → S` of
finite type is weakened to locally of finite type, and it omits the
identifications with `ξₙ` for `n ≥ 2`, which are not needed downstream. The
statement is therefore a derived specialization of Lemma 98.12.7, not a
verbatim single source assertion. Its proof requires Artin approximation
over the henselizations of finite-type `ℤ`-algebras (Lemma 98.10.1 in the
same chapter) or an equivalent algebraization argument; Example 98.12.8
there shows that some such input is necessary in general.

## Scope

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and zero rings, and every proper flat
scheme over `Spec R`. It assumes no projectivity, smoothness, connectedness,
section or cohomological flatness. It asserts nothing about versality at
points other than `u₀`, and nothing about smoothness of `L`.
