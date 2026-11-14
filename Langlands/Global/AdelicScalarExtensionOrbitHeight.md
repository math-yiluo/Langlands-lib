# Representation matrices and orbit heights under Galois scalar extension

This internal helper module belongs to the proof of the rank-one parabolic
rational-orbit height bound
(`Langlands.Global.RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement`).
It compares the adelic representation matrices and orbit heights of a group `G`
over a number field `F` with those of its base change `G_L` over a finite
extension `L / F`.

The setting is the one of the published module
`Langlands.Global.AdelicGaloisBoundedRootCompact`. There `G` is an affine group
scheme of locally finite type over `F`, and `G_L` is
`AffineWeil.unitBaseChange F L G`. The map

`scalarExtensionNormOneMap F L G : G(𝔸_F)¹ → G_L(𝔸_L)¹`

is the published scalar-extension map on norm-one adelic points. It is the
canonical unit `G → R_{L/F}(G_L)` on norm-one points, followed by the Weil
restriction comparison `R_{L/F}(G_L)(𝔸_F)¹ → G_L(𝔸_L)¹`. A matrix representation
`ρ` of `G` on `F^n` gives the base-changed representation
`ρ.baseChange (Spec.algebraMap F L)` of `G_L` on `L^n`.

The comparison is used in the descent step of Springer, *Reduction theory over
global fields* (1994), §3.6. That step passes from `G` over `k` to `G` over the
splitting field `l` and uses a height on `V(A, l)` whose restriction to
`V(A, k)` is the height over `k` (see the companion module
`Langlands.Global.PrimitiveAdelicHeightInclusion`). Springer does not state the
two lemmas below. Their statements and proofs are our own formalization of this
compatibility.

Throughout, `adeleInclusion : 𝔸_F → 𝔸_L` is the published inclusion of adele
rings (`Langlands.Global.AdelicFunctoriality.adeleInclusion`), and
`numberFieldAdeleTensorMap F L : L ⊗_F 𝔸_F → 𝔸_L` is the published
`L`-algebra map with `a ⊗ x ↦ a · adeleInclusion x`.

## Declarations

All declarations are theorems in the namespace
`Langlands.Global.AdelicGaloisUnit`.

`scalarExtensionNormOneMap_val_eq_tensor`. For a norm-one point `g`, the underlying adelic
point of `scalarExtensionNormOneMap F L G g` is obtained in three steps:

1. push `g` along the coefficient map `includeRight : 𝔸_F → L ⊗_F 𝔸_F`,
   `x ↦ 1 ⊗ x`;
2. view the result as an `L ⊗_F 𝔸_F`-point of `G_L`, through the published
   base-change equivalence `affinePointsBaseChangeMulEquiv`;
3. push this point along `numberFieldAdeleTensorMap F L`.

Proof. By definition, the Weil restriction comparison views an `𝔸_F`-point of
`R_{L/F}(G_L)` as an `L ⊗_F 𝔸_F`-point of `G_L` and applies step 3. The
published lemma `AffineWeil.unit_affinePoints` says that the unit acts on affine
points by steps 1 and 2.

`affineBaseChangeEquiv_affinePointsBaseChangeMulEquiv`. Take an `L`-algebra `A`
that is also an `F`-algebra with compatible scalars. The Library has two
comparisons between the `A`-points of `G` (as an `F`-algebra) and the `A`-points of
`G_L` (as an `L`-algebra): `affinePointsBaseChangeMulEquiv F L A G` and
`Lie.affineBaseChangeEquiv F L G A`, in opposite directions. The lemma says the
second undoes the first. Proof. Both maps are composites with the same
structure morphisms; we compare underlying scheme morphisms through the published
formula `affinePointsBaseChangeMulEquiv_symm_left`.

`affineMatrix_baseChange_tensor`. For an `𝔸_F`-point `x` of `G`, let `y` be the
`𝔸_L`-point of `G_L` obtained from `x` by steps 1–3 above. Then the matrix of
`ρ.baseChange (Spec.algebraMap F L)` at `y` is the matrix of `ρ` at `x` with
`adeleInclusion` applied to every entry. Proof:

- the matrix of a representation commutes with coefficient maps
  (`affineMatrix_naturality`), applied to `numberFieldAdeleTensorMap F L` and to
  `includeRight`;
- the published `MatrixRepresentation.affineMatrix_baseChange` says that the
  matrix of the base-changed representation at an `L ⊗_F 𝔸_F`-point is the
  matrix of `ρ` at the corresponding point of `G`, obtained by
  `Lie.affineBaseChangeEquiv`;
- by the previous lemma, that point is the image of `x` under `includeRight`.

So each entry of the left side is `numberFieldAdeleTensorMap F L (1 ⊗ m)`,
where `m` is the corresponding entry of the matrix of `ρ` at `x`. By
`numberFieldAdeleTensorMap_tmul` this equals `adeleInclusion m`.

`adelicMatrix_scalarExtensionNormOneMap`. For a norm-one point `g` of `G`,

`adelicMatrix L G_L ρ_L (scalarExtensionNormOneMap F L G g)
  = (adelicMatrix F G ρ g).map adeleInclusion`

as `n × n` matrices over `𝔸_L`, where `ρ_L = ρ.baseChange (Spec.algebraMap F L)`.
Proof. Rewrite with `scalarExtensionNormOneMap_val_eq_tensor`, then apply
`affineMatrix_baseChange_tensor`. The published `adelicMatrix` is, by definition,
the matrix of the representation on `𝔸`-points.

`orbitHeight_scalarExtensionNormOneMap`. **Orbit heights under scalar
extension.** Let `v ∈ F^n` be nonzero and `g` a norm-one point of `G`. Then

`orbitHeight L G_L ρ_L (algebraMap F L ∘ v) (scalarExtensionNormOneMap F L G g)
  = orbitHeight F G ρ v g ^ [L : F]`.

Here `orbitHeight` is the published orbit height
(`Langlands.Global.RepresentationGrowth.orbitHeight`): the normalized height
`Langlands.Global.PrimitiveAdelicHeight.height` of `adelicMatrix ρ g · v`, with
`v` embedded diagonally in the adeles. Proof. Let `M` be the adelic matrix of `ρ`
at `g` and `x = M · v` in `𝔸_Fⁿ`.

- By the previous lemma and `RingHom.map_mulVec`, the vector whose height is the
  left side is `adeleInclusion` applied to each coordinate of `x`. The step uses
  the published `adeleInclusion_diagonal`: on diagonally embedded elements of
  `F`, `adeleInclusion` is the diagonal embedding of `L` composed with
  `algebraMap F L`.
- `x` is primitive in the sense of `PrimitiveAdelicHeight.IsPrimitive`, since `v`
  is nonzero. So its finite local norms equal `1` at all but finitely many places
  (`IsPrimitive.hasFiniteMulSupport`).
- The height comparison `AdelicFunctoriality.height_adeleInclusion` of the
  companion module then gives the `[L : F]`-th power.

## Hypotheses

The fields `F` and `L` are number fields in the same universe `u`, with an
algebra structure `F → L`. No Galois hypothesis is needed. The lemma
`affineBaseChangeEquiv_affinePointsBaseChangeMulEquiv` is stated without the
number-field instances and without affineness or local finite type of `G`.
`affineMatrix_baseChange_tensor` is stated without affineness or local finite
type of `G`. The other three lemmas use all the hypotheses of
`scalarExtensionNormOneMap`.
