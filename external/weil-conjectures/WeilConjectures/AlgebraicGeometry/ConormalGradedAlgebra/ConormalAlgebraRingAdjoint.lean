/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraHomogeneousRingMap
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHomAffine
/-! # A ring-sheaf adjoint from local homogeneous formulas
Source: Stacks Project, Divisors, Tag 0634.
(blueprint: lem-pur-conormal-algebra-ring-adjoint).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.ConormalGradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private def sectionMap {Y W : Scheme.{u}} (k : W ⟶ Y)
    (B : Y.CommAlgebraSheaf) (C : W.CommAlgebraSheaf)
    (q : B.toModule ⟶ (pushforward k).obj C.toModule) (V : Y.Opens) :
    B.right.obj.obj (op V) →+ C.right.obj.obj (op (k ⁻¹ᵁ V)) :=
  (q.val.app (op V)).hom.toAddMonoidHom

private theorem sectionMap_naturality {Y W : Scheme.{u}} (k : W ⟶ Y)
    (B : Y.CommAlgebraSheaf) (C : W.CommAlgebraSheaf)
    (q : B.toModule ⟶ (pushforward k).obj C.toModule)
    (U V : Y.Opens) (H : U ≤ V) (a : B.right.obj.obj (op V)) :
    sectionMap k B C q U (B.right.obj.map (homOfLE H).op a) =
      C.right.obj.map (homOfLE (k.preimage_mono H)).op
        (sectionMap k B C q V a) := by
  exact Hom.app_presheaf_map q (homOfLE H) a

private theorem sectionMap_smul {Y W : Scheme.{u}} (k : W ⟶ Y)
    (B : Y.CommAlgebraSheaf) (C : W.CommAlgebraSheaf)
    (q : B.toModule ⟶ (pushforward k).obj C.toModule)
    (V : Y.Opens) (r : Γ(Y, V)) (a : B.right.obj.obj (op V)) :
    sectionMap k B C q V (B.hom.hom.app (op V) r * a) =
      C.hom.hom.app (op (k ⁻¹ᵁ V)) (k.app V r) * sectionMap k B C q V a := by
  exact (Hom.app_smul q r a).trans
    (pushforward_smul_def k C.toModule V r (q.val.app (op V) a))

attribute [local irreducible] sectionMap

/-- A module map with the ambient homogeneous representative formula induces a
ring-sheaf morphism compatible with structure-sheaf scalars.
Source: Stacks Project, Divisors, Tag 0634.
(blueprint: lem-pur-conormal-algebra-ring-adjoint).

Proof: On compatible ambient affine charts the formula implies preservation of
one and multiplication by homogeneous_preserves_ringOperations. Cover f⁻¹V by
inverse images of compatible ambient affine pairs with i′⁻¹U′ contained in V;
these exist because i′ is a closed embedding. Naturality and the sheaf axiom
extend the ring laws from these charts to V. The additive section maps therefore
define ring homomorphisms; naturality makes them a ring-sheaf morphism. Apply
module linearity to r times one to check compatibility with structure sheaves. -/
theorem exists_ringAdjoint_of_homogeneousFormula {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (A : Presentation i) (A' : Presentation i')
    (q : A'.algebra.toModule ⟶ (pushforward f).obj A.algebra.toModule)
    (hq : ∀ (U : X.affineOpens) (U' : X'.affineOpens)
      (H : U.1 ≤ g ⁻¹ᵁ U'.1) (Hf : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
      (n : ℕ) (a : (power i' n).val.obj (op U'.1)),
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).app U.1 b =
          g.appLE U'.1 U.1 H ((powerInclusion i' n).app U'.1 a) ∧
        A.algebra.right.obj.map (homOfLE Hf).op
          (q.val.app (op (i' ⁻¹ᵁ U'.1))
            (homogeneousClass i' A'.algebra A'.inclusion n U'.1 a)) =
          homogeneousClass i A.algebra A.inclusion n U.1 b) :
    ∃ ρ : A'.algebra.right ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj A.algebra.right,
      (A'.algebra.hom ≫ ρ =
        (⟨f.c⟩ : Z'.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map A.algebra.hom) ∧
      ∀ (V : Z'.Opens) (a : A'.algebra.right.obj.obj (op V)),
        q.val.app (op V) a = ρ.hom.app (op V) a := by
  let S := sectionMap f A'.algebra A.algebra q
  have laws (V : Z'.Opens) : S V 1 = 1 ∧ ∀ a b, S V (a * b) = S V a * S V b := by
    let Charts := {p : X.affineOpens × X'.affineOpens //
      i' ⁻¹ᵁ p.2.1 ≤ V ∧ p.1.1 ≤ g ⁻¹ᵁ p.2.1}
    let W (t : Charts) := i ⁻¹ᵁ t.1.1.1
    have Hf (t : Charts) : W t ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ t.1.2.1) := by
      change W t ≤ (f ≫ i') ⁻¹ᵁ t.1.2.1
      rw [← h]
      exact i.preimage_mono t.2.2
    have HW (t : Charts) : W t ≤ f ⁻¹ᵁ V := (Hf t).trans (f.preimage_mono t.2.1)
    have cover : f ⁻¹ᵁ V ≤ ⨆ t, W t := by
      intro z hz
      obtain ⟨O, hO, hOV⟩ := i'.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
      let O' : X'.Opens := ⟨O, hO⟩
      have hzO : g (i z) ∈ O' := by
        rw [show g (i z) = i' (f z) from congrArg (fun k : Z ⟶ X' ↦ k z) h]
        change f z ∈ i'.base ⁻¹' O
        rw [hOV]
        exact hz
      obtain ⟨U', hU', hzU', hU'O⟩ := exists_isAffineOpen_mem_and_subset hzO
      obtain ⟨U, hU, hzU, hUU'⟩ := exists_isAffineOpen_mem_and_subset
        (show i z ∈ g ⁻¹ᵁ U' from hzU')
      have hU'V : i' ⁻¹ᵁ U' ≤ V := by
        intro x hx
        change x ∈ (V : Set Z')
        rw [← hOV]
        exact hU'O hx
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨(⟨U, hU⟩, ⟨U', hU'⟩), hU'V, hUU'⟩, hzU⟩
    let F (t : Charts) : A'.algebra.right.obj.obj (op (i' ⁻¹ᵁ t.1.2.1)) →+
        A.algebra.right.obj.obj (op (W t)) :=
      (A.algebra.right.obj.map (homOfLE (Hf t)).op).hom.toAddMonoidHom.comp
        (S (i' ⁻¹ᵁ t.1.2.1))
    have hF (t : Charts) : F t 1 = 1 ∧ ∀ a b, F t (a * b) = F t a * F t b := by
      apply homogeneous_preserves_ringOperations i i' A A' t.1.1 t.1.2
        (g.appLE t.1.2.1 t.1.1.1 t.2.2).hom (F t)
      intro n a
      dsimp only [F, S]
      unfold sectionMap
      exact hq t.1.1 t.1.2 t.2.2 (Hf t) n a
    have hres (t : Charts) (a : A'.algebra.right.obj.obj (op V)) :
        A.algebra.right.obj.map (homOfLE (HW t)).op (S V a) =
          F t (A'.algebra.right.obj.map (homOfLE t.2.1).op a) := by
      change A.algebra.right.obj.map _ (S V a) =
        A.algebra.right.obj.map _ (S _ (A'.algebra.right.obj.map _ a))
      rw [show S (i' ⁻¹ᵁ t.1.2.1) (A'.algebra.right.obj.map (homOfLE t.2.1).op a) =
        A.algebra.right.obj.map (homOfLE (f.preimage_mono t.2.1)).op (S V a) from
          sectionMap_naturality f A'.algebra A.algebra q _ _ t.2.1 a]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    constructor
    · apply TopCat.Sheaf.eq_of_locally_eq' A.algebra.right W (f ⁻¹ᵁ V)
        (fun t ↦ homOfLE (HW t)) cover
      intro t
      change A.algebra.right.obj.map (homOfLE (HW t)).op (S V 1) = _
      rw [hres, map_one, (hF t).1, map_one]
    · intro a b
      apply TopCat.Sheaf.eq_of_locally_eq' A.algebra.right W (f ⁻¹ᵁ V)
        (fun t ↦ homOfLE (HW t)) cover
      intro t
      change A.algebra.right.obj.map (homOfLE (HW t)).op (S V (a * b)) =
        A.algebra.right.obj.map (homOfLE (HW t)).op (S V a * S V b)
      rw [map_mul (A.algebra.right.obj.map (homOfLE (HW t)).op).hom]
      rw [hres t (a * b), hres t a, hres t b]
      rw [map_mul (A'.algebra.right.obj.map (homOfLE t.2.1).op).hom, (hF t).2]
  let ρ : A'.algebra.right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj A.algebra.right :=
    ⟨{ app := fun V ↦ CommRingCat.ofHom
        { S V.unop with
          map_one' := (laws V.unop).1
          map_mul' := (laws V.unop).2 }
       naturality := by
        intro V W j
        ext a
        exact sectionMap_naturality f A'.algebra A.algebra q
          W.unop V.unop (leOfHom j.unop) a }⟩
  refine ⟨ρ, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    ext a
    change S V.unop (A'.algebra.hom.hom.app V a) =
      A.algebra.hom.hom.app (op (f ⁻¹ᵁ V.unop)) (f.app V.unop a)
    have hs := sectionMap_smul f A'.algebra A.algebra q V.unop a 1
    change S V.unop (A'.algebra.hom.hom.app V a * 1) =
      A.algebra.hom.hom.app (op (f ⁻¹ᵁ V.unop)) (f.app V.unop a) * S V.unop 1 at hs
    rw [mul_one, (laws V.unop).1, mul_one] at hs
    exact hs
  · intro V a
    dsimp only [ρ, S]
    unfold sectionMap
    rfl
end
end AlgebraicGeometry.ConormalGradedAlgebra
