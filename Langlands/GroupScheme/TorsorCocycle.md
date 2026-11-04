# Group-valued cocycles on covers, and sections of torsors

Worker 1515's internal prerequisite for the split-unipotent torsor theorem
(task 21d6e245-dcea-4c7a-af4a-c532ea0dd295). It is the nonabelian Čech
formalism of torsors and descent, written so that no fibre products appear.
The content is derived; it does not follow a particular cited text.

## Cocycles

Fix a scheme S, a group scheme G over S (a group object of `Over S`), and
U : Over S. A `Cocycle G U` is a family `toFun a b : Z ⟶ G.X` defined for every
Z : Over S and every pair of morphisms a, b : Z ⟶ U. It satisfies two axioms:

- naturality: `toFun (t ≫ a) (t ≫ b) = t ≫ toFun a b`;
- the cocycle identity: `toFun a c = toFun a b * toFun b c`, using the group
  structure on points of G.

This is a 1-cocycle on the Čech nerve of U → S, described through its points
over all test schemes.

- `Cocycle.IsTrivial ξ` holds when some f : U ⟶ G.X has
  `ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for all a, b.
- `Cocycle.coboundary f` is that cocycle, for a given f.
- `Cocycle.map ξ φ` is the image under a homomorphism φ : G ⟶ H, obtained by
  composing with φ.hom.hom.
- `Cocycle.twist ξ f` is (a, b) ↦ (a ≫ f)⁻¹ · ξ(a, b) · (b ≫ f).
  `IsTrivial.of_twist` shows that ξ is trivial when a twist is: if f₂
  trivializes the twist, then f · f₂ trivializes ξ.
- `Cocycle.lift ξ j hξ` takes a homomorphism j : H ⟶ G with j.hom.hom a
  monomorphism, and a proof hξ that every value of ξ factors through j. It reads
  ξ as a cocycle of H, choosing the factorizations; they are unique because j
  is a monomorphism, so naturality and the cocycle identity follow by
  cancelling j. `lift_toFun` records the factorization, and `IsTrivial.of_lift`
  shows that ξ is trivial when its lift is.

## Descent along an effective epimorphism

`exists_section_of_forall_eq` takes U : Over S with U.hom an effective
epimorphism, and φ : U ⟶ Y with a ≫ φ = b ≫ φ for every pair a, b : Z ⟶ U. It
returns s : S ⟶ Y.left with U.hom ≫ s = φ.left and s ≫ Y.hom = 𝟙 S. The
section is `EffectiveEpi.desc`, applied to test pairs viewed in `Over S`.
Cancelling the epimorphism U.hom proves that it is a section.

## Torsors

Let X : Over S carry an action of G.X (`ModObj G.X X`) with
`ModObj.leftSMul G.X X` an isomorphism. By Mathlib's `ModObj.isIso_leftSMul_iff`,
for any two points x, y : Z ⟶ X there is a unique point m of G with m • x = y.

- `torsorDiff hX x y` is that point.
- `torsorDiff_smul` and `eq_torsorDiff` give its defining property and its
  uniqueness.
- `torsorCocycle hX u`, for u : U ⟶ X, is the cocycle
  (a, b) ↦ torsorDiff (b ≫ u) (a ≫ u). Uniqueness of `torsorDiff` together
  with `ModObj.comp_smul` and `mul_smul` gives its naturality and cocycle
  identity.

`exists_section_of_isTrivial` assumes U.hom is an effective epimorphism and
the torsor cocycle of u is trivialized by f. Then X has a section,
s : S ⟶ X.left with s ≫ X.hom = 𝟙 S. The proof applies
`exists_section_of_forall_eq` to the point f⁻¹ • u: a short computation in
the group of points shows that it takes the same value on any two points of U
over a test scheme.
