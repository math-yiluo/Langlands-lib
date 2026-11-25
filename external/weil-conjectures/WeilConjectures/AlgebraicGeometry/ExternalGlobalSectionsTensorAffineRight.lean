/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCoverLeft
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # External sections with an affine second factor

Source: Stacks Project, Tag 0BED, lemma-kunneth, the displayed comparison on X times V.
(blueprint: lem-sc-external-global-sections-tensor-affine-right).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The external section comparison when the second factor is affine.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the comparison on X times V.
(blueprint: lem-sc-external-global-sections-tensor-affine-right).

Proof: Choose a finite affine open cover U_i of X. The affine-diagonal criterion makes
U_i intersect U_j affine. Put A_i = Gamma(U_i,O), B = Gamma(Y,O), M_i = F(U_i), and
N = G(Y). The affine product formula identifies U_i times Y with Spec(A_i tensor_k B).
The affine pullback formulas and the affine tensor-section formula identify sections of
pr_1^*F tensor pr_2^*G there with M_i tensor_k N. To see this algebraically, pull back
M_i and N to A_i tensor_k B, then tensor the resulting modules over that ring; the map
(m tensor b) tensor (a tensor n) goes to (a*m) tensor (b*n), and its inverse sends
m tensor n to (m tensor 1) tensor (1 tensor n). The same formulas apply to each overlap.
The adjunction-unit pure-tensor formulas identify these maps with the external section
map, and their naturality identifies the overlap maps with restrictions in M_i tensor N.
Apply the sheaf equalizer to the finite cover U_i of X and its inverse-image cover of
X times Y. Tensoring over the field with N preserves the kernel of the difference of
restriction maps and the two finite products. Thus the resulting equalizer comparison
is bijective. On each chart it sends s tensor t to the tensor of their projection
pullbacks, hence equals externalGlobalSectionsTensor by tensor induction and sheaf
uniqueness. An empty X has an empty equalizer and zero sections. An empty affine Y has
B and N zero, and both sides vanish. Zero coefficients are handled by the same formula.
No assertion that tensor preserves infinite products, and no higher cohomology, is used.
-/
theorem externalGlobalSectionsTensor_bijective_of_isAffine_right
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)] [IsAffine Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hU (i : C.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (C.X i) := by
      dsimp only [C]
      rw [Scheme.OpenCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  have hUU (i j : C.I₀) : IsAffineOpen (U i ⊓ U j) :=
    (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
      (U i) (by simp) (U j) (by simp) (hU i) (hU j)
  have hlocal (V : X.Opens) (hV : IsAffineOpen V) :
      Function.Bijective (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G) := by
    have : IsAffine V.toScheme := hV
    exact externalGlobalSectionsTensor_bijective_of_isAffine
      k V.toScheme Y (V.ι ≫ f) g (F.restrict V.ι) G
  exact externalGlobalSectionsTensor_bijective_of_finite_cover_left k X Y f g F G
    U C.iSup_opensRange (fun i ↦ hlocal (U i) (hU i))
    (fun i j ↦ hlocal (U i ⊓ U j) (hUU i j))

end AlgebraicGeometry.Scheme.Modules
