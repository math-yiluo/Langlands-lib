# Composition and homeomorphism normalization of sheaf-cohomology pullback

This internal construction supplies the composition law for the actual
Ext-defined pullback on abelian sheaf cohomology and its comparison with the
existing homeomorphism cohomology equivalence.

For continuous maps f : X → Y and g : Z → X, abelian sheaves A on Y, B on X,
and C on Z, and coefficient arrows k : A → f_* B and l : B → g_* C,
`compositeCoefficientMap f g k l` is the actual arrow k followed by f_* l.
Direct images compose definitionally here, so its target is (g ≫ f)_* C.

`pushforwardMap_comp` asserts, for every natural degree n and x in H^n(Y,A),

    pushforwardMap g l n (pushforwardMap f k n x)
      = pushforwardMap (g ≫ f) (compositeCoefficientMap f g k l) n x.

The proof is by induction on n, generalizing all three sheaves. In degree zero
both maps are identified with the actual maps on global sections. In the
successor step it uses the chosen injective short exact sequences of A, B and
C and extends k and l to maps into their direct-image short complexes. Their
composite is the short-complex map for the composite coefficient arrow.
Positive-degree cohomology of the injective middle sheaf vanishes, so every
class is the connecting image of a class of the quotient sheaf. Applying
connecting-map naturality twice on the left and once on the right reduces
the equality to the induction hypothesis on the quotient sheaves. Direct image
is not required to preserve exact sequences.

For a homeomorphism e : X ≅ Y, `pushforwardMap_id_eq_equiv` asserts that
`pushforwardMap e.hom (𝟙 (e_* B)) n` equals the existing
`UnitSheafPushforward.cohomologyPushforwardEquiv e B n` on every element.
The proof again inducts on degree. Both maps have the same degree-zero
normalization. For the successor step, push forward the injective short exact
sequence of B along the equivalence e_*. This preserves exactness and
injectivity, so the connecting map surjects onto the required positive-degree
cohomology. Both maps commute with that connecting map and the induction
hypothesis proves their equality.

All spaces and sheaf coefficient groups have the fixed universe u. Neither
result has a compactness assumption. The proofs are internal consequences of
the existing Ext pullback, its global-section normalization and connecting-map
compatibility, injective embeddings, and the published homeomorphism
cohomology equivalence. This pair supplies transport laws for the host Picard
obstruction proof; it does not itself prove the obstruction naturality target.
