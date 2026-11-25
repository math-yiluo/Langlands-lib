/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechTensorExact
import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechProductExact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Exactness of the fixed right-coefficient Cech sequences

Source: Stacks Project, Varieties, Tag 0BED, short exact sequence paragraph.
(blueprint: lem-sc-picard-external-right-cech-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The two explicitly constructed Cech sequences are short exact.
No cover condition or cohomology comparison is needed.
Source: Stacks Project, Varieties, Tag 0BED, short exact sequence paragraph;
Modules, Tags 01CD and 01CE; Cohomology, Tag 01XD.
(blueprint: lem-sc-picard-external-right-cech-exact).

Proof: Affine diagonal makes every nonempty finite intersection of U and V affine.
On an affine the sections of the quasi-coherent sequence S are short exact,
by affine acyclicity of its first term and left exactness of sections. Restriction
of scalars to k preserves exactness. The finitely many tuple sections in each
Cech degree therefore form a short exact sequence of vector spaces. Tensor with
any term of the Cech complex of F is exact over the field k. The finitely many
summands in each total degree give short exactness of the tensor total.
The product intersection is the fibre product of the corresponding affine factor
intersections. Affine pullback and tensor sections identify its external
coefficient sections with the tensor over k of the factor sections, naturally in
S. Hence the product-cover Cech sequence is also termwise short exact, without
requiring F to be flat as an O-module. Extension by zero preserves termwise short
exactness: negative terms are all zero. Degreewise short exactness is short
exactness in the category of complexes. Empty families and zero coefficients
produce zero terms and satisfy the same argument. -/
theorem picardExternal_right_cech_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    : (S.map (picardRightTensorCechFunctor f g U V F)).ShortExact ∧
      (S.map (picardRightProductCechFunctor f g U V F)).ShortExact := by
  constructor
  · exact picardExternal_right_cech_tensor_exact f g U V hU hV F S hS
  · exact picardExternal_right_cech_product_exact f g U V hU hV F S hS

end AlgebraicGeometry.Scheme.Modules
