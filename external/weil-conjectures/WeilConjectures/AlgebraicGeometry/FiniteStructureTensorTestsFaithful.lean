/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase

public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

import WeilConjectures.AlgebraicGeometry.FiniteStructureTensorPowersSupported
import WeilConjectures.AlgebraicGeometry.GrothendieckExistence
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Faithful elementary tensor tests for finite structure adjoints

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-tensor-tests-faithful).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem affine_test_ext {X : Scheme.{u}} {M N : X.Modules} (v w : M ⟶ N)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ x : Γ(M, U), v.app U x = w.app U x) :
    v = w := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let V : {V : X.affineOpens // V.1 ≤ U} → X.Opens := fun V ↦ V.1.1
  refine F.eq_of_locally_eq' V U (fun V ↦ homOfLE V.2) ?_ _ _ ?_
  · intro p hp
    obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hpW⟩
  · intro W
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
    exact h W.1.1 W.1.2 _

private theorem square_test_ext {X : Scheme.{u}} {G P : X.Modules}
    [G.IsQuasicoherent] (v w : G ⊗ G ⟶ P)
    (h : ∀ (U : X.Opens) (x y : Γ(G, U)),
      v.app U (tmulSection x y) = w.app U (tmulSection x y)) : v = w := by
  apply affine_test_ext
  intro U hU t
  obtain ⟨s, rfl⟩ := (quasiCoherent_tensor_product_affine_sections G G).2 U hU |>.surjective t
  induction s using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add s t hs ht => simp only [map_add, hs, ht]

private theorem cube_test_ext {X : Scheme.{u}} {G P : X.Modules}
    [G.IsQuasicoherent] (v w : (G ⊗ G) ⊗ G ⟶ P)
    (h : ∀ (U : X.Opens) (x y z : Γ(G, U)),
      v.app U (tmulSection (tmulSection x y) z) =
        w.app U (tmulSection (tmulSection x y) z)) : v = w := by
  have : (G ⊗ G).IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections G G).1
  apply affine_test_ext
  intro U hU t
  obtain ⟨s, rfl⟩ :=
    (quasiCoherent_tensor_product_affine_sections (G ⊗ G) G).2 U hU |>.surjective t
  induction s using TensorProduct.inductionOn with
  | tmul xy z =>
    rw [tensorSectionsMap_tmul]
    obtain ⟨r, rfl⟩ := (quasiCoherent_tensor_product_affine_sections G G).2 U hU |>.surjective xy
    induction r using TensorProduct.inductionOn with
    | tmul x y => exact h U x y z
    | add r s hr hs => simp only [map_add, add_tmulSection, hr, hs]
  | add s t hs ht => simp only [map_add, hs, ht]

private theorem adjoint_test_cancel {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S)
    {F G : X.Modules}
    (ψ : (tensorPullback j).obj G ≅ (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (v w : F ⟶ G)
    (h : v ≫ finiteStructureAdjoint j p G ψ.hom =
      w ≫ finiteStructureAdjoint j p G ψ.hom) :
    (tensorPullback j).map v = (tensorPullback j).map w := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  apply (cancel_mono ψ.hom).mp
  apply (adj.homEquiv F _).injective
  apply (cancel_mono ((pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf))).mp
  have hv := adj.unit.naturality v
  have hw := adj.unit.naturality w
  dsimp only [Functor.comp_map, Functor.id_map] at hv hw
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hv, ← hw]
  simpa only [finiteStructureAdjoint, adj, Category.assoc] using h

/-- Adjoint tests on elementary tensors detect morphisms out of the square and cube.
This concerns morphisms, not injectivity of adjoints on sections over an arbitrary open.
Source: Stacks Project, Tags 088E and 088F, applied to the tensor powers in 09ZT.

Proof: Both tensor powers are coherent and have proper support. Indeed a proper
closed supporting subscheme annihilating G also annihilates the tensor powers;
on affine opens finite generation is preserved by tensor products, and the
quasi-coherent tensor comparison identifies their sections with those products.
On the Noetherian scheme X quasi-coherence and finite type imply coherence.
For a fixed n, the hypothesis on elementary tensors implies equality of the
composites v followed by the nth adjoint and w followed by that adjoint. To see
this, work first on each affine open. The affine tensor-sections map is surjective;
tensor induction gives equality on every section of the square. For the cube use
surjectivity of the outer tensor-sections map, then that of the inner square, and
tensor induction twice. Cover each arbitrary open by its contained affine opens.
Naturality of the two composites and the sheaf condition extend the equality to all opens.
By the tensor-pullback
adjunction, equality of these composites is equality of the pullbacks of v and w
followed by psi_n and the pushforward composition comparison. Both comparisons
are isomorphisms, so cancel them to get j_n^*v = j_n^*w. Faithfulness of completion
on coherent modules with proper support now gives v = w, for both tensor powers.
No compatibility of psi is needed, and no ring product on G is assumed. On opens
avoiding all reductions the adjoints need not be injective on sections; the proof
uses global morphism faithfulness instead. Zero modules and empty schemes are
covered by the same morphism argument. For the faithfulness invocation choose the
comparison required by grothendieck_existence independently of psi. Naturality makes
the reductions of w a compatible family for that comparison. The unique lift property
then equates v and w when their reductions coincide; no equality between this auxiliary
comparison and the pinned tensorPullbackCompositionIso is asserted.
(blueprint: lem-weil-pbc-finite-structure-tensor-tests-faithful). -/
theorem finite_structure_tensor_tests_faithful
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf)) :
    (∀ (v w : G ⊗ G ⟶ G),
      (∀ (n : ℕ) (U : X.Opens) (x y : Γ(G, U)),
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          (v.app U (tmulSection x y)) =
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          (w.app U (tmulSection x y))) → v = w) ∧
    (∀ (v w : (G ⊗ G) ⊗ G ⟶ G),
      (∀ (n : ℕ) (U : X.Opens) (x y z : Γ(G, U)),
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          (v.app U (tmulSection (tmulSection x y) z)) =
        (Scheme.Modules.finiteStructureAdjoint
          (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U
          (w.app U (tmulSection (tmulSection x y) z))) → v = w) := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : G.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG |>.1
  obtain ⟨hSq, hpSq, hCube, hpCube⟩ :=
    finite_structure_tensor_powers_supported A X f G hG hproper
  let j := fun n ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let c := fun n ↦ (Classical.choice (nonempty_tensorPullbackComp (i n) (j (n + 1)))).symm
    ≪≫ eqToIso (congrArg tensorPullback (hi n))
  have hfull := (grothendieck_existence_fullyFaithful A I f i hi hp c)
  have faithful (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
      (hpF : HasSupportProperOver f F) (v w : F ⟶ G)
      (h : ∀ n, (tensorPullback (j n)).map v = (tensorPullback (j n)).map w) : v = w := by
    obtain ⟨t, ht, hu⟩ := hfull G F hG hF hproper hpF
      (fun n ↦ (tensorPullback (j n)).map w)
      (fun n ↦ ((c n).hom.naturality w).symm)
    exact (hu v h).trans (hu w (fun _ ↦ rfl)).symm
  constructor
  · intro v w h
    apply faithful (G ⊗ G) hSq hpSq v w
    intro n
    apply adjoint_test_cancel (j n) (fnY n) (ψ n)
    apply square_test_ext
    intro U x y
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h n U x y
  · intro v w h
    apply faithful ((G ⊗ G) ⊗ G) hCube hpCube v w
    intro n
    apply adjoint_test_cancel (j n) (fnY n) (ψ n)
    apply cube_test_ext
    intro U x y z
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h n U x y z

end AlgebraicGeometry
