/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicTopology.SetCechNerveFreeResolution
import WeilConjectures.CategoryTheory.Sites.PresheafCechExtEdgeKernel

/-!
# Injectivity of the presheaf Čech descent edge map

Source: Stacks Project, Cohomology on Sites, Tag 079Z; Hypercoverings, Tag 01GC.
(blueprint: lem-sc-presheaf-cech-ext-edge-injective)
-/

@[expose] public section

universe u v w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

/-- The Čech edge map in degree q is injective when its other filtration pieces vanish.
Source: Stacks Project, Cohomology on Sites, Tag 079Z, and Hypercoverings, Tag 01GC.
(blueprint: lem-sc-presheaf-cech-ext-edge-injective)

Proof: replace the target of f objectwise by its image, without changing the nerve.
The free abelian augmented nerve of this surjection is exact by the fibrewise
contraction of Tag 01GC, implemented at the set level by setCechNerve_free_resolution
with ring Z. Sheafification is exact, and local surjectivity identifies the
sheafified augmentation with Z[f.right]. Thus the augmented sheafified free nerve
is a resolution of Z[f.right]. The derived Hom filtration of Tag 079Z gives a
first-quadrant spectral sequence E1^(a,b)=Ext^b(Z[E_a],F), converging to
Ext^(a+b)(Z[f.right],F), where E_a is the (a+1)-fold presheaf fibre product.
The free abelian and sheafification adjunctions identify its zero row, including
its differential, with presheafCechComplex f F.obj. The hypothesis hlower kills
all rows with 0<b<q. The other hypothesis kills E2^(q,0). Consequently every
associated graded piece in total degree q except (0,q) is zero. The finite
filtration in that degree gives an injection into E-infinity^(0,q). Since no
differentials enter column zero on any page, this term embeds in E1^(0,q).
Identify the degree-zero nerve term with f.left: the composite is pullback along
Z[f.hom], exactly the map in the conclusion. No enough-injectives hypothesis is needed:
this edge-injectivity consequence also
follows directly from the Yoneda Ext long exact sequences. Write A_i=Z[E_i],
A=Z[f.right], K_(-1)=A and K_i=ker(A_i -> K_(i-1)). Exactness gives short exact
sequences 0 -> K_i -> A_i -> K_(i-1) -> 0. A class in the kernel of
Ext^q(A,F) -> Ext^q(A_0,F) comes from Ext^(q-1)(K_0,F). Successive connecting
maps are surjective by hlower, so it comes from a map g:K_(q-1) -> F. Composing
g with the epimorphism A_q -> K_(q-1) gives a degree-q cocycle in Hom(A_*,F).
By hcech it is t composed with the differential for some t:A_(q-1) -> F.
Cancelling A_q -> K_(q-1) shows that g extends to A_(q-1). Its connecting class
is therefore zero, as is the original class. This also treats q=1 directly,
without intermediate rows. -/
theorem presheafCech_ext_edge_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) (q : ℕ) (hq : 0 < q)
    (hlower : ∀ (P : Cᵒᵖ ⥤ Type v) (b : ℕ), 0 < b → b < q →
      Subsingleton
        (Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F b))
    (hcech : IsZero ((presheafCechComplex f F.obj).homology q)) :
    Function.Injective (fun x :
      Ext ((presheafToSheaf J AddCommGrpCat).obj (f.right ⋙ AddCommGrpCat.free)) F q ↦
        (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
          (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp x (Nat.zero_add q)) := by
  intro x y hxy
  let g := fun z : Ext ((presheafToSheaf J AddCommGrpCat).obj
      (f.right ⋙ AddCommGrpCat.free)) F q ↦
    (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
      (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp z (Nat.zero_add q)
  have hxy' : g x = g y := hxy
  have hz : g (x - y) = 0 := by
    dsimp [g] at hxy' ⊢
    rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, hxy', add_neg_cancel]
  have hk := presheafCech_ext_edge_kernel F f hf q hq hlower hcech (x - y) hz
  exact sub_eq_zero.mp hk

end CategoryTheory.Sheaf
