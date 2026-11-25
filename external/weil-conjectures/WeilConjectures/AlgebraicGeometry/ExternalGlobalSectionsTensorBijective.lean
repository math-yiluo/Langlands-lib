/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorAffineRight
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # External tensor product on global sections

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-external-global-sections-tensor-bijective).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The explicit external tensor map on ordinary sections is bijective.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-external-global-sections-tensor-bijective).

Proof: Choose finite affine covers of X and Y, using quasi-compactness. Their
pairwise intersections are affine by the affine diagonal criterion. On each
U_i times V_j and each overlap the affine product, pullback and tensor section
formulas identify the external section map with the tensor of the corresponding
section modules; the formulas on pure tensors make these comparisons commute
with restrictions. First hold V_j fixed and apply the sheaf equalizer for the
cover of X. Tensor over k is exact and preserves finite products, so its kernel
is Gamma(X,F) tensor G(V_j). These identifications commute with restriction in
V_j. Apply the sheaf equalizer for the cover of Y, now tensoring with Gamma(X,F).
The resulting isomorphism is the displayed explicit linear map because this
holds on pure tensors on every chart. Tensor induction gives equality on all
elements. If either scheme is empty or either coefficient is zero, its section
module and the external section module are zero, and the same equalizers apply.
No positive-degree acyclicity or cohomology comparison is used. -/
theorem externalGlobalSectionsTensor_bijective
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let C := Y.affineCover.finiteSubcover
  let U : C.I₀ → Y.Opens := fun i ↦ (C.f i).opensRange
  have hU (i : C.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (C.X i) := by
      dsimp only [C]
      rw [Scheme.OpenCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  have hUU (i j : C.I₀) : IsAffineOpen (U i ⊓ U j) :=
    (isAffineHom_diagonal_iff (f := g)).mp inferInstance ⊤ (isAffineOpen_top _)
      (U i) (by simp) (U j) (by simp) (hU i) (hU j)
  have hlocal (V : Y.Opens) (hV : IsAffineOpen V) :
      Function.Bijective (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι)) := by
    have : IsAffine V.toScheme := hV
    exact externalGlobalSectionsTensor_bijective_of_isAffine_right
      k X V.toScheme f (V.ι ≫ g) F (G.restrict V.ι)
  exact externalGlobalSectionsTensor_bijective_of_finite_cover k X Y f g F G
    U C.iSup_opensRange (fun i ↦ hlocal (U i) (hU i))
    (fun i j ↦ hlocal (U i ⊓ U j) (hUU i j))

end AlgebraicGeometry.Scheme.Modules
