# Split-centralizing fixers fix all split translations

The theorem `Langlands.Geometry.Building.unramifiedSplitTranslationFixer.{u}` proves exactly the published proposition `Langlands.Geometry.Building.UnramifiedSplitTranslationFixerStatement.{u}`. It works in arbitrary universe `u` and in both characteristics. The statement and its imported pairs are unchanged.

The source is the independence argument inserted before Kaletha–Prasad Proposition 9.3.13 by the authors' *Corrections and additions to Bruhat–Tits Theory: A New Approach*, version of 1 November 2024, PDF pp. 39–40 (registered source `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`). This corrects the proof of Proposition 9.3.13 in the 2023 book, printed p. 338, PDF p. 369 (registered source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). The formal proof implements the orbit-and-convexity argument using finite convex combinations; it needs no passage to a topological closure.

## Valuation translations

The private lemma `centralizerTranslation_cocharacter` works over any field with an integer valuation. For a cocharacter `ν` of `T` and a field unit `t`, it proves

\[
\nu_Z\bigl(s(\nu(t))\bigr)=-\operatorname{ord}(t)\otimes\nu
\quad\text{in } V(T).
\]

Here `ν_Z` denotes `IntegerValuation.centralizerTranslation`, and `s : T → Z` is the factorization into the supplied centralizer. Its bijective restriction-evaluation map makes equality testable on rational characters of `Z`. `IntegerValuation.eval_centralizerTranslation` gives the negative field order of each character evaluation. Restriction of characters and `CocharacterUniformizer.rationalCharacterEval_cocharacterPoints` identify that evaluation with the integer-pairing power of `t`. The homomorphism law for `IntegerValuation.orderUnits` evaluates this power. These are published inputs from `IntegerCentralizer`, `IntegerValuation`, `CocharacterUniformizerEvaluation`, and `Langlands.BruhatTits.Cartan.CentralizerValuation`.

## Convex extension

Two private elementary lemmas give the real-span argument. `convex_contains_real_line` puts `r • w` between the adjacent multiples `floor(r) • w` and `(floor(r) + 1) • w`. `convex_contains_tensor_image` applies this to the image of `1 ⊗ ν` under a real linear map. Every integral multiple is again the image of an integral cocharacter. Tensor induction handles sums by taking the midpoint of the doubled summands, with the induction hypothesis strengthened to cover every real scalar. Thus a convex set containing all integral pure tensors contains the entire linear image of the real tensor space. This is an internal linear-algebra implementation of the source's convex-hull step.

The private lemma `split_translation_fixer_of_order_one` applies this argument over any field `k` with a unit `t` of order one. Its source `A` may be any commutative group scheme; the apartment torus `T` is maximal split in a connected reductive group. Define

\[
L:V(A)\longrightarrow V(T)/\operatorname{rootAnnihilator},
\qquad L=q\circ f_*.
\]

For each integral cocharacter `ν` of `A`, evaluate `-ν` at `t`. Functoriality of actual rational points identifies its image under `f` with the corresponding point of `T`. The supplied centralizer factorization `C.s ≫ C.j = i` identifies its image in `G`. The valuation formula above and `IntegerValuation.IsOmegaCompatible.smul_eq_vadd` show that this point acts on the apartment by translation by `L(1 ⊗ ν)`; `D.apartmentMap_smul` gives the same action in the original reduced quotient. Since `g` commutes with this point and fixes the image of `x`, it fixes the translated point.

The published theorem `KPApartmentData.convex_fixedApartmentCoordinates` in `ApartmentFacetClosureFixing` says that the fixed set of `g`, expressed in apartment coordinates based at `x`, is convex over any field. Its connected-reductive and maximal-split-torus hypotheses are exactly those available here. Applying the tensor-image lemma to this convex set proves fixation for every `L(w)`.

## Specialization to the maximal unramified field

For `K = inertiaFixedField F`, the proof uses `IsConnectedReductive.baseChange_of_algebraicExtension` from `Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent` to obtain connected reductivity of `G_K`. The supplied maximal-split hypothesis gives the monomorphism needed by the apartment API. `MaximalUnramified.baseUniformizerUnit` and `MaximalUnramified.order_baseUniformizerUnit` provide the order-one unit; they are published in `MaximalUnramifiedUniformizer`.

The original factorization `S → T → G` remains a factorization after base change by the functor composition law. This transports the given commutation hypothesis to the generic lemma. Finally, membership in `splitTranslationDirections` unfolds into a witness in `V(S_K)` followed by its image under `f_*` and the root-annihilator quotient. The generic lemma gives exactly the requested fixation.

The proof uses `splitTranslationDirections` from `UnramifiedTwistedFixedTranslationStatement` only as a definition. It takes no proof of that statement as input. It uses none of the torus-unit-fixed-apartment, Galois-fixed-building-point, or unramified-building-descent statements or their reductions. In particular, it does not require `K` to be a local field, a building metric on the quotient, or additional apartment axioms.
