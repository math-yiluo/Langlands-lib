# Transport of fibre equality and centrality along composite base changes

Worker 738.

These are internal helper lemmas for the proof of
`MultiplicativeTypeCentralRigidityStatement`. They come from no specific statement in
the literature. The proof of SGA 3, Exposé IX, Théorème 5.1 (registered Gille–Polo 2009
recomposed edition `sga3-expose-ix-gille-polo-2009`, p.48, PDF page 18) moves silently
between base changes, for example from `S` to `Spec 𝒪_{S,s}` and then to its residue field
or to `Spec(𝒪_{S,s}/m^{n+1})`. In Lean, base change along a composite `c ≫ b` is only
isomorphic to the iterated base change, not equal to it. This module provides the
comparisons needed for equality of base-changed homomorphisms. For centrality it uses
the Library lemma
`MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_comp_iff` (module
`GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality`).

All declarations are in the namespace `Langlands.GroupScheme.CentralRigidityTransport`.
Here `b : S' ⟶ S` and `c : S'' ⟶ S'` are morphisms of schemes, and `H`, `G` are group
schemes over `S`.

- `compIso b c : baseChange (c ≫ b) ≅ baseChange b ⋙ baseChange c` is the natural
  isomorphism of functors on group schemes. It is obtained from Mathlib's
  `Over.pullbackComp c b` (pullback along a composite is the composite of pullbacks) by
  `Functor.mapGrpNatIso`, followed by `Functor.mapGrpCompIso`. Its components are the
  objectwise comparisons that the Library already defines, for example
  `Langlands.GroupScheme.baseChangeCompIso` in `AbelianScheme.Tate.BaseChangeCoherence`.
  The natural-isomorphism form is used here for its naturality square.
- `compIso_naturality b c w` is the naturality square of `compIso b c` at a homomorphism
  `w : H ⟶ G`.
- `baseChange_comp_map_eq_iff b c u v`: the base changes of `u, v : H ⟶ G` along `c ≫ b`
  are equal if and only if the base changes along `c` of their base changes along `b` are
  equal. The proof uses the naturality square, cancelling the isomorphism
  `(compIso b c).hom.app H` on the left in one direction and `(compIso b c).hom.app G` on
  the right in the other.
- `baseChange_eq_and_central_of_factor b c d hd u v heq hc`: let `d : S'' ⟶ S` satisfy
  `c ≫ b = d`. If the base changes of `u` and `v` along `b` are equal, and the base change
  of `u` along `b` is central, then the same holds for the base changes along `d`. The
  proof substitutes `d = c ≫ b`. Equality follows from `baseChange_comp_map_eq_iff`.
  Centrality follows from the Library lemma `IsCentral.baseChange` (module
  `GroupScheme.CentralIsogeny.BaseChange`), which says that centrality is preserved by base
  change, together with the Library's `isCentral_baseChange_comp_iff` cited above.

This module adds no axioms.
