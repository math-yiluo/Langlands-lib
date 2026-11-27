# Elementary étale points of separated algebraic spaces

The module `Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePointStatement`
defines the proposition `SeparatedElementaryEtalePointStatement.{u}`, a ring-point form of
Stacks Project, Decent Algebraic Spaces, Lemma 68.11.4 (Tag 0BBP) for separated algebraic
spaces over a field. The module states the proposition and does not prove it. It imports only
`Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints`.

## Statement

Let `K : Type u` be a field and `X : AlgebraicSpace (Spec (CommRingCat.of K))` an algebraic
space over `Spec K` with `IsSeparated X`. Let `A : Type u` be a `K`-algebra with
`Algebra.FiniteType K A`, let `x : RingPoints K X A` be a point such that
`IsEtale (uliftYonedaEquiv.{u + 1}.symm x)`, and let `p : PrimeSpectrum A`.

Then there exist a `K`-algebra `B : Type u` with `Algebra.FiniteType K B`, a point
`y : RingPoints K X B` with `IsEtale (uliftYonedaEquiv.{u + 1}.symm y)`, and a prime
`q : PrimeSpectrum B` such that the following two conditions hold.

1. For every `K`-algebra `D : Type u` and `K`-algebra maps `f : B →ₐ[K] D`,
   `g : A →ₐ[K] D` such that the square of presheaves

   ```
   Spec D --(ringTestMap K f)--> Spec B
     |                              |
   (ringTestMap K g)                y
     v                              v
   Spec A ----------x-----------> X
   ```

   (Yoneda images of the two maps of spectra, and the two points) is a pullback, there is a
   prime `P` of `D` with `PrimeSpectrum.comap f P = q` and `PrimeSpectrum.comap g P = p`.
2. For every `K`-algebra `C : Type u` and `K`-algebra maps `f g : B →ₐ[K] C` such that the
   square formed by `ringTestMap K f`, `ringTestMap K g`, `y` and `y` is a pullback, every
   `K`-algebra map `μ : C →ₐ[K] B` with `μ.comp f = AlgHom.id K B` and
   `μ.comp g = AlgHom.id K B`, and every prime `P` of `C` with `PrimeSpectrum.comap f P = q`
   and `PrimeSpectrum.comap g P = q`, one has `P = PrimeSpectrum.comap μ q`.

In the Lean text the algebra maps are coerced to ring homomorphisms before
`PrimeSpectrum.comap` is applied, as in `PrimeSpectrum.comap (f : B →+* D) P`.

## The Library notions used

- `RingPoints K X A` (`Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`) is the
  set of sections of `X` over the scheme `ringTest K A`, the spectrum of `A` over `Spec K`.
  For such a section `x`, `uliftYonedaEquiv.{u + 1}.symm x` is the corresponding morphism of
  presheaves `Spec A → X`. The module `Langlands.Geometry.Analytic.SpaceAnalytification`
  abbreviates the same morphism as `pointHom K x` (there `K` is a complete ultrametric
  nontrivially normed field).
- `IsEtale` (`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`) says that a morphism
  of presheaves is representable and that every represented base change is an étale morphism
  of schemes. So `x` and `y` are étale morphisms from affine schemes to `X`.
- `IsSeparated X` (`RingPoints.lean`) says that the diagonal of the presheaf of `X` is a
  representable closed immersion, the Stacks Project notion of a separated algebraic space.
- `ringTestMap K f : ringTest K D ⟶ ringTest K B`
  (`Langlands.AlgebraicGeometry.PointTopology.ringTestMap`) is the morphism of spectra over
  `Spec K` induced by `f : B →ₐ[K] D`, and `schemeYoneda` is the functor of points. In
  Mathlib's `IsPullback fst snd s t`, `fst` and `snd` are the two projections from the corner
  and `s`, `t` the two maps to the common target; so in condition 1, `Spec D` is a fibre
  product `Spec B ×_X Spec A` with first projection `Spec f` and second projection `Spec g`.

## Condition 1: `q` and `p` give the same point of `|X|`

Because `X` is separated, the fibre product `Spec B ×_X Spec A` is the base change of the
diagonal of `X` along `Spec (B ⊗_K A) → X ×_K X`, hence a closed subscheme of the affine
scheme `Spec (B ⊗_K A)`: an affine model `Spec D` as in condition 1 exists, and any two models
are isomorphic compatibly with their projections. So condition 1, which quantifies over all
models, is not vacuous and does not depend on the model. The points of a scheme are its points
as an algebraic space (Stacks Project, Properties of Algebraic Spaces, Lemma 66.4.2, Tag
03BV), and for a fibre product of algebraic spaces the map
`|Spec B ×_X Spec A| → |Spec B| ×_{|X|} |Spec A|` is surjective (Lemma 66.4.3, Tag 03H4).
Hence condition 1 says exactly that `q` and `p` have the same image in `|X|`.

## Condition 2 is the elementary-neighbourhood condition

Stacks Project, Decent Algebraic Spaces, Definition 68.11.5 (Tag 0BGU), calls an étale
morphism `(U, u) → (X, x)` from a scheme an elementary étale neighbourhood when "the morphism
`u = Spec(κ(u)) → X` is a monomorphism". Condition 2 is equivalent to the morphism
`Spec κ(q) → Spec B → X` being a monomorphism, so (by condition 1) `(Spec B, q)` is an
elementary étale neighbourhood of the image of `p` in `|X|`. The equivalence goes as follows.

- *Models and the diagonal.* As for condition 1, a model `Spec C` of `Spec B ×_X Spec B`
  exists and is unique up to an isomorphism compatible with the projections. The diagonal
  `Spec B → Spec B ×_X Spec B` is a morphism of affine schemes over `Spec K`, so it is
  `Spec μ` for a unique `K`-algebra map `μ : C → B`; the equations `μ.comp f = id` and
  `μ.comp g = id` say that `Spec μ` is a section of both projections, which characterizes the
  diagonal. So condition 2 is a condition on `y` and `q` alone.
- *The points over `q`.* Let `T = Spec κ(q) ×_X Spec κ(q)`, which is the fibre product of
  `Spec C` with `Spec (κ(q) ⊗_K κ(q))` over `Spec (B ⊗_K B)`. Since `B → κ(q)` is an
  epimorphism of rings, `T → Spec C` is a monomorphism, hence injective, and its image is the
  set of primes `P` of `C` with `PrimeSpectrum.comap f P = q = PrimeSpectrum.comap g P`.
  The diagonal of `Spec κ(q) → X` is the morphism `Spec κ(q) → T` whose point is the image of
  `q` under `Spec μ`, the prime `PrimeSpectrum.comap μ q`.
- *`T` is étale over `κ(q)`.* The scheme `E = Spec B ×_X Spec κ(q)` is étale over
  `Spec κ(q)`, being a base change of `y`, so it is a disjoint union of spectra of finite
  separable field extensions of `κ(q)`. The scheme `T = E ×_{Spec B} Spec κ(q)` is the union of
  those components whose point lies over `q` (for such a component `Spec L`, the map `B → L`
  factors through `κ(q)` and `L ⊗_B κ(q) = L`). Hence the second projection
  `T → Spec κ(q)` is étale and separated.
- *Conclusion.* The diagonal `Spec κ(q) → T` is a section of this étale separated morphism,
  hence an open and closed immersion onto one point of `T`. It is an isomorphism exactly when
  `T` has a single point, that is, when `PrimeSpectrum.comap μ q` is the only prime of `C`
  over `q` along both `f` and `g`; this is condition 2. A morphism is a monomorphism exactly
  when its diagonal is an isomorphism, so condition 2 holds exactly when `Spec κ(q) → X` is a
  monomorphism.

By Decent Algebraic Spaces, Lemma 68.11.3 (Tag 0EMX), applied to `Spec B → X`, the
monomorphism condition is also equivalent to the induced homomorphism `κ(x₀) → κ(q)` being an
isomorphism, where `x₀ ∈ |X|` is the image of `q` and `κ(x₀)` its residue field (Definition
68.11.2, Tag 0EMW, which uses that `X` is decent).

## Source and derivation

The source is the Stacks Project, Decent Algebraic Spaces (Chapter 68 of the book), registered
as `stacks-decent-spaces-chapter-ed88ff78-2026-11-05` (registered folder fingerprint
`878f5241b88f6791dc4c96ee48fc36c3e2e3e54852b029d7662bf6d432e7c4c8`): the chapter PDF of
version ed88ff78, SHA-256
`2e29935b33d7a90b4fcdfa1ce801af37406a0f0dc6d9103d54ffd2263122a3e6`. The chapter PDFs number
results within the chapter ("Lemma 11.4" there is Lemma 68.11.4 of the book); this page uses
the book numbering throughout.

- Lemma 68.11.4 (Tag 0BBP, PDF p.27): "Let S be a scheme. Let X be a decent algebraic space
  over S. For every point x ∈ |X| there exists an étale morphism (U, u) → (X, x) where U is
  an affine scheme, u is the only point of U lying over x, and the induced homomorphism
  κ(x) → κ(u) is an isomorphism."
- Lemma 68.11.3 (Tag 0EMX, PDF p.27): for a morphism of decent spaces `f : X → Y` and
  `y = f(x)`, the map `κ(y) → κ(x)` is an isomorphism if and only if `Spec(κ(x)) → Y` is a
  monomorphism. With it, the conclusion of Lemma 68.11.4 makes `(U, u)` an elementary étale
  neighbourhood in the sense of Definition 68.11.5 (Tag 0BGU, PDF p.27).
- Lemma 68.11.1 (Tag 03K4) and Definition 68.11.2 (Tag 0EMW), PDF p.26: on a decent space
  each point is represented by a monomorphism from the spectrum of its residue field.
- The diagram after Definition 68.6.1 (Tag 03I8, PDF pp.12–13): quasi-separated algebraic
  spaces are decent. A separated space is quasi-separated, since closed immersions are
  quasi-compact, so Lemma 68.11.4 applies to every `X` here.

The surjectivity of points of fibre products is Stacks Project, Properties of Algebraic
Spaces, Lemma 66.4.3 (Tag 03H4, "Lemma 4.3" on p.4 of the chapter PDF), registered as
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05` (registered folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`; `spaces-properties.pdf`,
SHA-256 `7f71f8371bd2040b4cd3ec6171420ef6a1ce14f7a0a334d32c6d04821e1741bc`). The fppf
locality is Stacks Project, Descent, Lemma 35.28.2 (Tag 036O, "Lemma 28.2" on p.65 of the
chapter PDF): "The property P(f) = “f is locally of finite type” is fppf local on the
source", registered as
`stacks-descent-ed88ff78-2026` (SHA-256
`28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`).

### What is derived here

The proposition is derived from Lemma 68.11.4; the following parts are not in the source.

- *Ring-point form.* The base is `Spec K` for a field `K`, points of `X` are given as images
  of primes `p` of étale points `x : Spec A → X` of finite type `K`-algebras, and the
  conclusion is expressed through affine models of fibre products, as explained above.
  Condition 2 is the monomorphism condition of Definition 68.11.5 rather than the residue
  field isomorphism of Lemma 68.11.4; the two agree by Lemma 68.11.3. The statement does not
  keep the conclusion of Lemma 68.11.4 that `u` is the only point of `U` over `x`.
- *Finite type.* The proposition also asks `B` to be of finite type over `K`, although `X`
  is not assumed locally of finite type. This follows from Lemma 68.11.4 as follows. Let
  `x₀ ∈ |X|` be the image of `p` and `(U, u) → (X, x₀)` the affine étale neighbourhood of
  Lemma 68.11.4; `U` is affine over `Spec K`. The scheme `W = U ×_X Spec A` is étale over
  `Spec A`, hence locally of finite type over `K`, and étale over `U`. The image `V` of
  `W → U` is open, as étale morphisms are open, and contains `u` by Properties of Algebraic
  Spaces, Lemma 66.4.3, since `u` and `p` both lie over `x₀`. As `W → V` is an étale
  surjection, hence an fppf covering, Descent, Lemma 35.28.2 shows that `V` is locally of
  finite type over `K`. A principal affine open `Spec B ⊂ V` containing `u` then has `B` of
  finite type over `K`, the composite `Spec B → U → X` is étale, and `q = u` still satisfies
  the monomorphism condition and lies over `x₀`, so conditions 1 and 2 hold.
- *Name.* The name `SeparatedElementaryEtalePointStatement` and the formulation through
  `RingPoints`, `ringTestMap` and pullback squares of presheaves are also derived here.
