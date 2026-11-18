# Adelic points, Galois twists, and rational points for the Weil restriction of GLₙ

`Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement.{u}` is a proposition
definition for a finite extension `L/K` of number fields in universe `u` and `n : ℕ`.
The field extension is given by `[Algebra K L]` and `[FiniteDimensional K L]`.

## The comparison map

Write `GLₙ` for `GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)`.
Its local `IsAffine` and `Smooth` instances come from
`GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement`. The notation `Wₙ` denotes
`weilGroup K L GLₙ`, the Weil restriction to `K` of the base change of `GLₙ` to `L`.
Then `AdelicGroupPoints K Wₙ` is `Wₙ(𝔸_K)` with its adelic topology.

The map `Φ : Wₙ(𝔸_K) → AdelicGL L n` is the same composite used in Tasks 7649 and 7660.

1. `AdelicGaloisUnit.weilAdelicEquiv K L GLₙ` takes a point of `Wₙ(𝔸_K)` to an
   `𝔸_L`-point of `AffineWeil.unitBaseChange K L GLₙ`.
2. `AdelicGroupPoints.map` of
   `(GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom`
   takes that point to an `𝔸_L`-point of the general linear group scheme over `L`.
3. `GeneralLinearGroupPoints.adelicHomeomorph L n` identifies that point with an
   invertible matrix in `AdelicGL L n = GL_n(𝔸_L)`.

## Statement

1. There is a topological group isomorphism `e : Wₙ(𝔸_K) ≃ₜ* AdelicGL L n` whose
   underlying function is `Φ`.
2. For each `σ : L ≃ₐ[K] L` and `g : AdelicGroupPoints K Wₙ`, the equality
   ```
   Φ (adelicAut K (unitGaloisAut K L GLₙ σ) g) =
     Langlands.Global.AdelicGLTransport.adelicEquiv n (σ : L ≃+* L) (Φ g)
   ```
   compares the two actions. `unitGaloisAut K L GLₙ σ` is the algebraic
   automorphism of `Wₙ` attached to `σ`. `adelicAut K` sends it to the induced
   topological group automorphism of `Wₙ(𝔸_K)`. On the right, `adelicEquiv`
   applies `AdelicFunctoriality.adeleEquiv (σ : L ≃+* L)` to each matrix
   entry.
3. For every `g : AdelicGroupPoints K Wₙ`, membership in
   `AdelicGroupPoints.rationalSubgroup K Wₙ` is equivalent to membership of
   `Φ g` in `(AdelicGL.rational L n).range`. The first subgroup is the image of
   `Wₙ(K)` under the diagonal point map, and `AdelicGL.rational L n` embeds
   `GL_n(L)` diagonally in `GL_n(𝔸_L)`.

## Mathematical justification

1. `weilAdelicEquiv` and `adelicHomeomorph` are continuous multiplicative
   equivalences. Functoriality of `AdelicGroupPoints.map` sends the two
   morphisms of the base-change isomorphism to mutually inverse continuous
   group maps. Their composite with the two equivalences gives the required
   isomorphism with underlying map `Φ`.
2. By `AdelicGaloisUnit.galoisTwist_weilAdelicEquiv`, the adelic map induced
   by `AffineWeil.unitGaloisAction K L GLₙ σ` becomes
   `AdelicGaloisUnit.galoisTwist K L GLₙ σ` under `weilAdelicEquiv`.
   After projecting from the base change to `GLₙ`, `galoisTwist_left_fst` and
   `adeleTestIso_hom_left` express the twist by precomposition with
   `Spec` of `AdeleGalois.ringEquiv K L σ`. On matrix entries this applies
   `σ ⊗ 1` under the identification `L ⊗[K] 𝔸_K ≃ 𝔸_L` given by
   `numberFieldAdeleTensorEquiv`.
   Both this ring map and `AdelicFunctoriality.adeleEquiv (σ : L ≃+* L)`
   restrict to `σ` on the diagonal copy of `L`, by `ringEquiv_algebraMap`
   and `adeleEquiv_diagonal`. Both fix the image of `𝔸_K`. For the tensor
   action this follows from `ringEquiv_adeleInclusion`. For `adeleEquiv`,
   the continuous extension `L_w → L_{σ(w)}` of `σ` intertwines the
   embeddings of `K_v` for each place `w` over `v`, since it does so on
   the dense copy of `K` in `K_v`. The images of `L` and `𝔸_K` generate
   the tensor product as a ring, so the two maps agree on `𝔸_L`. This
   gives the entrywise action in the direction of `σ`.
3. `AdelicWeilRestriction.map_rationalSubgroup` identifies the rational
   subgroups under the first map. `AdelicGroupPoints.rational_naturality`
   and the inverse of the base-change isomorphism identify them under
   the second map. `GeneralLinearGroupPoints.adelicHomeomorph_rational`
   sends the resulting rational subgroup onto `(AdelicGL.rational L n).range`
   using the equivalence with `GL_n(L)` on rational points. Injectivity
   of `Φ` gives the stated equivalence of membership.

## Provenance

This is derived content connecting two Library descriptions of the twist.
Tasks 7649 (the simple twisted trace formula) and 7660 (its per-class facts)
use `Φ` on the adelic points of the Weil restriction. Task 7573 (twisted
elliptic class finiteness) uses the entrywise action and the diagonal
rational points on `GL_n(𝔸_L)`.

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
  Trace Formula* (1989), Chapter 1, §1, Lemma 1.1 and its setup (printed p. 3),
  and §2.2, Lemma 2.5 and its setup (printed pp. 12–14), use the action of the
  cyclic generator on `GL_n(E)` and `GL_n(𝔸_E)`. This furnishes the matrix
  setting of the comparison. Registered source `arthur-clozel-1989-base-change`.
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §18.5
  (printed pp. 486–488), sets up twisted conjugation for a reductive group
  over a number field with a finite-order automorphism and states the
  simple twisted trace formula in Corollary 18.5.1. The Weil-restriction
  construction gives the group and automorphism in this setting for a
  cyclic extension. Registered source `getz-hahn-2024-automorphic-representations`.
