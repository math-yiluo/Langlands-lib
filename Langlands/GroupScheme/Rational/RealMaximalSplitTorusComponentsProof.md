# Proof: every real component meets a maximal split torus

Lean module: `Langlands.GroupScheme.Rational.RealMaximalSplitTorusComponentsProof`,
namespace `Langlands.GroupScheme`.

```lean
theorem realMaximalSplitTorusComponents : RealMaximalSplitTorusComponentsStatement
```

The theorem's type is exactly the proposition `RealMaximalSplitTorusComponentsStatement` of
module `Langlands.GroupScheme.Rational.RealMaximalSplitTorusComponentsStatement`, with no
further hypotheses and no universe parameters. For every group scheme `G` over `Spec ℝ` with
affine underlying scheme, smooth structure morphism and connected underlying space, every
commutative `S` with a maximal split torus `i : S.toGrp ⟶ G`, and every real point
`g : RingPoint ℝ G.X ℝ`, it gives `s : RingPoint ℝ S.X ℝ` with
`ConnectedComponents.mk (s ≫ i.hom.hom) = ConnectedComponents.mk g` in the evaluation
topology. This is Borel–Tits 1965, Theorem 14.4 (Matsumoto), in the connected-component form
recorded in the statement's Markdown.

The theorem is `RealMaximalSplitTorusComponents.of_reductive` applied to
`realReductiveSplitTorusComponents`, the published proof of the connected reductive case
`RealReductiveSplitTorusComponentsStatement` (module
`Langlands.GroupScheme.Rational.RealReductiveSplitTorusComponentsProof`). This file adds the
reduction from smooth connected affine groups to connected reductive groups.

Throughout, the real points `RingPoint ℝ H.X ℝ` carry the evaluation topology and the group law
`H.ringPointGroup (CommAlgCat.of ℝ ℝ)` (the group of morphisms into a group object), installed
as a local instance. With this law they form a topological group
(`RealPointTopology.ringPointIsTopologicalGroup`). `ringPointHom f` is the homomorphism of real
points given by postcomposition with `f` (from the reductive proof module); it is continuous.

## Helper results (namespace `RealMaximalSplitTorusComponents`)

- `mul_mem_connectedComponent` and `mul_mem_connectedComponent'`: in a group with continuous
  multiplication, if `c` lies in the component of `1`, then `c * y` and `y * c` lie in the
  component of `y`. The proof maps the component of `1` by the continuous translation by `y`.
- `connectedSpace_of_isUnipotent`: if `U` is a group scheme over `ℝ` with affine underlying
  scheme, smooth structure morphism and connected underlying space, and `IsUnipotent U` holds,
  then `RingPoint ℝ U.X ℝ` is a connected space. Over the perfect field `ℝ`,
  `perfectFieldUnipotentSplit` gives a finite split series for `U`, and
  `splitUnipotentAffineSpaceStatement` gives an isomorphism of schemes over `Spec ℝ` from
  `U.X` to the affine space `𝔸(ULift (Fin n); Spec ℝ)`. The point homeomorphisms
  `affinePresentationPointHomeomorph`, `specPointHomeomorph` and
  `AlgPoint.polynomialPointHomeomorph` then identify `RingPoint ℝ U.X ℝ` with the
  connected space `ULift (Fin n) → ℝ`.
- `mem_connectedComponent_one_of_comp_eq_one`: for a homomorphism `p : G ⟶ L` of group schemes
  over `ℝ` with affine underlying schemes, where the kernel `kernel p` is affine and its real
  points form a connected space, every real point `a` of `G` with `a ≫ p.hom.hom = 1` lies in
  the identity component of `G(ℝ)`. The kernel pullback lifts `a` to a real point of
  `kernel p`. The image of the connected space of real points of the kernel under the
  continuous inclusion is preconnected and contains `1` and `a`.

## The reduction `of_reductive`

`of_reductive (hred : RealReductiveSplitTorusComponentsStatement) :
RealMaximalSplitTorusComponentsStatement`. Let `G`, `S`, `i` and `g` be given.

1. **Levi decomposition.** `characteristicZeroLeviDecomposition` over `ℝ` gives a connected
   reductive `L`, a homomorphism `p : G ⟶ L` and a section `j : L ⟶ G` with `j ≫ p = 𝟙 L`.
   The kernel `U = kernel p` is smooth, connected and unipotent. It is affine as a pullback of
   affine schemes, and `L` is affine because it is reductive over an affine base.
2. **The torus in the quotient.** The kernel inclusion `kernelι p` is a closed subgroup (a
   closed immersion, as `L` is separated). `SectionQuotient.isFppfQuotient_of_section` shows
   that `p` is the fppf quotient of `G` by the range of `kernelι p`, because `p` has the
   homomorphic section `j`. Then
   `IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel` shows that `i ≫ p` is a
   maximal split torus of `L`.
3. **The reductive case.** `connectedSpace_of_isUnipotent` makes `U(ℝ)` connected. The
   premise `hred`, applied to `L`, the torus `i ≫ p` and the real point `g ≫ p.hom.hom`,
   gives `t : RingPoint ℝ S.X ℝ` such that `p(x)` and `p(g)` lie in one component of `L(ℝ)`,
   where `x = t ≫ i.hom.hom`.
4. **Lifting back to `G`.** Put `y = j(p(g))` and `z = j(p(x))`. Continuity of `ringPointHom j`
   puts `z` in the component of `y`. Since `j ≫ p = 𝟙 L`, both `g y⁻¹` and `x⁻¹ z` map to `1`
   under `p`, so they lie in the identity component by
   `mem_connectedComponent_one_of_comp_eq_one`. Hence `g = (g y⁻¹) y` lies in the component of
   `y` and `z = x (x⁻¹ z)` lies in the component of `x`. Chaining the three component
   equalities gives that `x` and `g` have the same component, which is
   `ConnectedComponents.mk (t ≫ i.hom.hom) = ConnectedComponents.mk g`.

## Comparison with the source

Armand Borel and Jacques Tits, *Groupes réductifs*, Publications Mathématiques de l'IHÉS 27
(1965), Theorem 14.4 (Matsumoto), printed pp. 146–147, one-based PDF pp. 93–94; registered
source `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`. The theorem reads:
"Supposons G connexe, défini sur R, et soit S un tore déployé sur R maximal de G. Alors
G_R = (G_R)^0 . S_R."

The source reduces to the reductive case with a maximal reductive `R`-subgroup `H` of `G`
containing `S` and the unipotent radical `U` of `G`: "Le groupe U_R est connexe et G_R est
homéomorphe au produit H_R × U_R". The Lean proof keeps the connectedness of `U(ℝ)` but
does not choose a Levi subgroup containing `S`. It passes to the reductive quotient `L` with
the image torus `i ≫ p`, which is maximal split there, and returns to `G` with the section `j`
and the kernel. Connectedness of `U(ℝ)` comes from the scheme isomorphism of the split
unipotent group `U` with affine space. The reductive case is the separately published
`realReductiveSplitTorusComponents`; this file does not reprove it. The source works with path
components (§14.1); the Lean conclusion is the connected-component form, as explained in the
statement's Markdown.
