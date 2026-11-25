/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernelIdeal

/-! # Square-zero kernels of relative restriction on functions

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-section-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Products of functions vanishing on the smaller subscheme are zero.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-section-kernel)

Proof: On an affine open Spec A of X the two subschemes are Spec(A/I) and
Spec(A/J). The kernel of A/J to A/I is the image I/J. Products in this image
vanish because I*I is contained in J. After base change by an etale object,
the defining ideal is the extended ideal of I/J. Extension commutes with
products, so this ideal still has square zero. Cover the etale object by
such affine charts. Functions whose restriction to the smaller subscheme
is zero belong to this ideal on every chart. Their product is zero on every
chart, and hence zero globally by the structure sheaf separation axiom.
This argument also applies to nonaffine objects. If I=J the restriction is
an isomorphism; on an empty object the section ring is the zero ring. -/
theorem squareZeroRelativeSectionKernel (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (V : J.subscheme.Etaleᵒᵖ) (a b : J.subscheme.etaleStructurePresheaf.obj V)
    (ha : (etaleStructurePresheafToPullback (IdealSheafData.inclusion hJI)).app V a = 0)
    (hb : (etaleStructurePresheafToPullback (IdealSheafData.inclusion hJI)).app V b = 0) :
    a * b = 0 := by
  let f := (etaleStructurePresheafToPullback
    (IdealSheafData.inclusion hJI)).app V
  have ha' : a ∈ RingHom.ker f.hom := (RingHom.mem_ker).2 ha
  have hb' : b ∈ RingHom.ker f.hom := (RingHom.mem_ker).2 hb
  have hker := relativeSectionKernel_ker_mul_le_bot X I J hJI hII V
  have hab : a * b ∈ (⊥ : Ideal (J.subscheme.etaleStructurePresheaf.obj V)) :=
    (Ideal.mul_le.mp hker) a ha' b hb'
  simpa using hab

end AlgebraicGeometry.Scheme
