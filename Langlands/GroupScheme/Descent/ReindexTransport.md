# Actual point transport after reindexing

This is an internal pullback-calculus prerequisite for restricting actual
Čech descent data. It is derived from `reindexHom`, `Datum.reindex`, and
`Datum.move`; it asserts no new effectivity result and has no external source
claim. All schemes lie in an arbitrary universe `u`. No étaleness, surjectivity,
affineness, or other geometric hypothesis is used.

For `q : V → S`, `f g : T → V`, group schemes `G,H` over `S`, and a
homomorphism `e : (f ≫ q)^*G → (g ≫ q)^*H`, `reindexHom_eval` evaluates
the corresponding morphism between iterated pullbacks on an arbitrary test
scheme `Z`. Given `a : Z → q^*G` and `z : Z → T` whose projections satisfy
`a ≫ (q^*G).X.hom = z ≫ f`, evaluation followed by projection to `H` equals
evaluation of `e` at the original `G` coordinate and `z`, followed by projection
to `H`. The proof identifies the input pullback lifts by their two projections
and uses the defining projection formulas of the iterated/direct pullback
comparison isomorphisms.

For an actual datum `D` along `p : S → B`, let `t : V → C`, `q : V → S`,
and `b : C → B` satisfy `q ≫ p = t ≫ b`. For an arbitrary test point
`a : Z → q^*G` and new coordinate `v : Z → V` with equal images in `C`,
`Datum.move_reindex_fst` states that transport by the restricted datum followed
by projection to the original group `G` equals transport by `D` of the
original group coordinate to `v ≫ q`. The original-base compatibility is
derived from the supplied equality over `C` and the square equation. The proof
unfolds the restricted overlap, applies `reindexHom_eval` and `pullHom_eval`,
and identifies the two overlap maps by pullback extensionality. It therefore
compares actual scheme morphisms on every test scheme, including all
nonreduced tests.
