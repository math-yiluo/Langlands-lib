/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.FiniteStructureTensorPowersSupported
import WeilConjectures.AlgebraicGeometry.GrothendieckExistence
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import WeilConjectures.AlgebraicGeometry.ThickeningSystemComparisonTransport
import WeilConjectures.AlgebraicGeometry.FiniteStructureTensorComparisonComposition

/-! # Core existence statement for a lifted finite-structure product

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-product-exists).
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

private theorem tensor_hom_ext {S : Scheme.{u}} {M N P : S.Modules}
    {a b : M ⊗ N ⟶ P}
    (h : ∀ (W : S.Opens) (s : Γ(M, W)) (t : Γ(N, W)),
      a.app W (tmulSection s t) = b.app W (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 S.ringCatSheaf.obj)).homEquiv _ P
    |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h (unop W) s t

private theorem exists_structure_product {Y S : Scheme.{u}} (p : Y ⟶ S) :
    ∃ m : (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⊗
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf),
      ∀ (U : S.Opens) (x y : Γ(Y, p ⁻¹ᵁ U)), m.app U (tmulSection x y) = x * y := by
  obtain ⟨m, _, hm, _⟩ := moduleBaseChangeMap_algebra p p (𝟙 S) (𝟙 Y)
    ((Category.id_comp p).trans (Category.comp_id p).symm)
  exact ⟨m, hm⟩

private theorem structure_product_baseChange
    {Y S Y' S' : Scheme.{u}} (p : Y ⟶ S) (p' : Y' ⟶ S')
    (i : S' ⟶ S) (g : Y' ⟶ Y) (w : g ≫ p = p' ≫ i)
    (m : (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⊗
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (m' : (pushforward p').obj (SheafOfModules.unit Y'.ringCatSheaf) ⊗
        (pushforward p').obj (SheafOfModules.unit Y'.ringCatSheaf) ⟶
        (pushforward p').obj (SheafOfModules.unit Y'.ringCatSheaf))
    (hm : ∀ (U : S.Opens) (x y : Γ(Y, p ⁻¹ᵁ U)),
      m.app U (tmulSection x y) = x * y)
    (hm' : ∀ (U : S'.Opens) (x y : Γ(Y', p' ⁻¹ᵁ U)),
      m'.app U (tmulSection x y) = x * y) :
    let beta := moduleBaseChangeMap p p' i g w (SheafOfModules.unit Y.ringCatSheaf) ≫
      (pushforward p').map (tensorPullbackObjUnitToUnit g)
    (tensorPullback i).map m ≫ beta =
      (Classical.choose (module_pullback_tensor i)
        ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
        ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))).hom ≫
        (beta ⊗ₘ beta) ≫ m' := by
  obtain ⟨a, b, ha, hb, _, hab, _⟩ := moduleBaseChangeMap_algebra p p' i g w
  have he : a = m := tensor_hom_ext (fun U x y ↦ (ha U x y).trans (hm U x y).symm)
  have he' : b = m' := tensor_hom_ext (fun U x y ↦ (hb U x y).trans (hm' U x y).symm)
  subst a
  subst b
  exact hab

private theorem product_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (K : C ⥤ E) (G : C) (B : D) (B' : E)
    (c : F ⋙ H ≅ K)
    (df : F.obj (G ⊗ G) ⟶ F.obj G ⊗ F.obj G)
    (dh : H.obj (F.obj G ⊗ F.obj G) ⟶ H.obj (F.obj G) ⊗ H.obj (F.obj G))
    (dk : K.obj (G ⊗ G) ⟶ K.obj G ⊗ K.obj G)
    (db : H.obj (B ⊗ B) ⟶ H.obj B ⊗ H.obj B)
    (psi : F.obj G ≅ B) (psi' : K.obj G ≅ B')
    (m : B ⊗ B ⟶ B) (m' : B' ⊗ B' ⟶ B')
    (beta : H.obj B ⟶ B')
    (hpsi : H.map psi.hom ≫ beta = c.hom.app G ≫ psi'.hom)
    (hb : H.map m ≫ beta = db ≫ (beta ⊗ₘ beta) ≫ m')
    (ht : H.map df ≫ dh ≫ (c.hom.app G ⊗ₘ c.hom.app G) = c.hom.app (G ⊗ G) ≫ dk)
    (hn : H.map (psi.hom ⊗ₘ psi.hom) ≫ db =
      dh ≫ (H.map psi.hom ⊗ₘ H.map psi.hom)) :
    c.hom.app (G ⊗ G) ≫ dk ≫ (psi'.hom ⊗ₘ psi'.hom) ≫ m' ≫ psi'.inv =
      H.map (df ≫ (psi.hom ⊗ₘ psi.hom) ≫ m ≫ psi.inv) ≫ c.hom.app G := by
  apply (cancel_mono psi'.hom).mp
  symm
  calc
    _ = H.map df ≫ H.map (psi.hom ⊗ₘ psi.hom) ≫ H.map m ≫ beta := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← hpsi, ← Functor.map_comp_assoc H psi.inv psi.hom beta,
        psi.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    _ = H.map df ≫ H.map (psi.hom ⊗ₘ psi.hom) ≫ db ≫ (beta ⊗ₘ beta) ≫ m' := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ H.map df ≫ H.map (psi.hom ⊗ₘ psi.hom) ≫ z) hb
    _ = H.map df ≫ dh ≫
        ((c.hom.app G ≫ psi'.hom) ⊗ₘ (c.hom.app G ≫ psi'.hom)) ≫ m' := by
      have hcomp : (H.map psi.hom ⊗ₘ H.map psi.hom) ≫ (beta ⊗ₘ beta) =
          ((c.hom.app G ≫ psi'.hom) ⊗ₘ (c.hom.app G ≫ psi'.hom)) := by
        rw [tensorHom_comp_tensorHom, hpsi]
      simpa only [Category.assoc, reassoc_of% hcomp] using congrArg
        (fun z ↦ H.map df ≫ z ≫ (beta ⊗ₘ beta) ≫ m') hn
    _ = c.hom.app (G ⊗ G) ≫ dk ≫ (psi'.hom ⊗ₘ psi'.hom) ≫ m' := by
      simpa only [← tensorHom_comp_tensorHom, Category.assoc] using congrArg
        (fun z ↦ z ≫ (psi'.hom ⊗ₘ psi'.hom) ≫ m') ht
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Changing a natural comparison leaves the underlying compatible family unchanged. -/
private theorem compatible_family_change
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅ tensorPullback (j n))
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (v : ∀ n, (tensorPullback (j n)).obj G ⟶ (tensorPullback (j n)).obj F)
    (hv : ∀ n, (d n).hom.app G ≫ v n =
      (tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F) :
    ∀ n, (c n).hom.app G ≫ v n =
      (tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F := by
  obtain ⟨e, he⟩ := compatible_family_comparison_equiv (i := i) j hj c d
    (⟨F, hF⟩ : CoherentModules X) (⟨G, hG⟩ : CoherentModules X)
  have h := (e ⟨v, hv⟩).property
  change ∀ n, (c n).hom.app G ≫ (e ⟨v, hv⟩).val n =
    (tensorPullback (i n)).map ((e ⟨v, hv⟩).val (n + 1)) ≫ (c n).hom.app F at h
  rw [he ⟨v, hv⟩] at h
  exact h

private theorem reduced_product_compatible
    {X S T Y Z : Scheme.{u}} (g : T ⟶ S) (h : S ⟶ X) (k : T ⟶ X)
    (w : g ≫ h = k) (p : Y ⟶ S) (p' : Z ⟶ T) (a : Z ⟶ Y)
    (wp : a ≫ p = p' ≫ g)
    (c : tensorPullback h ⋙ tensorPullback g ≅ tensorPullback k)
    (hc : c = (tensorPullbackCompositionIso g h k w).symm)
    (G : X.Modules)
    (psi : (tensorPullback h).obj G ≅
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (psi' : (tensorPullback k).obj G ≅
      (pushforward p').obj (SheafOfModules.unit Z.ringCatSheaf))
    (hpsi : (tensorPullback g).map psi.hom ≫
      (moduleBaseChangeMap p p' g a wp (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pushforward p').map (tensorPullbackObjUnitToUnit a)) = c.hom.app G ≫ psi'.hom)
    (m : (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⊗
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (m' : (pushforward p').obj (SheafOfModules.unit Z.ringCatSheaf) ⊗
        (pushforward p').obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
        (pushforward p').obj (SheafOfModules.unit Z.ringCatSheaf))
    (hm : ∀ (U : S.Opens) (x y : Γ(Y, p ⁻¹ᵁ U)),
      m.app U (tmulSection x y) = x * y)
    (hm' : ∀ (U : T.Opens) (x y : Γ(Z, p' ⁻¹ᵁ U)),
      m'.app U (tmulSection x y) = x * y) :
    c.hom.app (G ⊗ G) ≫
        (Classical.choose (module_pullback_tensor k) G G).hom ≫
        (psi'.hom ⊗ₘ psi'.hom) ≫ m' ≫ psi'.inv =
      (tensorPullback g).map ((Classical.choose (module_pullback_tensor h) G G).hom ≫
        (psi.hom ⊗ₘ psi.hom) ≫ m ≫ psi.inv) ≫ c.hom.app G := by
  have hb := structure_product_baseChange p p' g a wp m m' hm hm'
  have ht := finiteStructure_tensorComparison_composition g h k w G G
  have ht' : (tensorPullback g).map (Classical.choose (module_pullback_tensor h) G G).hom ≫
      (Classical.choose (module_pullback_tensor g)
        ((tensorPullback h).obj G) ((tensorPullback h).obj G)).hom ≫
      (c.hom.app G ⊗ₘ c.hom.app G) =
      c.hom.app (G ⊗ G) ≫ (Classical.choose (module_pullback_tensor k) G G).hom := by
    subst c
    exact ht
  exact product_transport (tensorPullback h) (tensorPullback g) (tensorPullback k) G _ _ c
    (Classical.choose (module_pullback_tensor h) G G).hom
    (Classical.choose (module_pullback_tensor g)
      ((tensorPullback h).obj G) ((tensorPullback h).obj G)).hom
    (Classical.choose (module_pullback_tensor k) G G).hom
    (Classical.choose (module_pullback_tensor g) _ _).hom psi psi' m m' _ hpsi hb ht'
    ((Classical.choose_spec (module_pullback_tensor g)).1 _ _ _ _ psi.hom psi.hom)

private theorem product_adjoint_formula
    {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S) (G : X.Modules)
    (psi : (tensorPullback j).obj G ≅
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (m : (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⊗
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (hm : ∀ (V : S.Opens) (x y : Γ(Y, p ⁻¹ᵁ V)), m.app V (tmulSection x y) = x * y)
    (mu : G ⊗ G ⟶ G)
    (hmu : (tensorPullback j).map mu =
      (Classical.choose (module_pullback_tensor j) G G).hom ≫
      (psi.hom ⊗ₘ psi.hom) ≫ m ≫ psi.inv)
    (U : X.Opens) (x y : Γ(G, U)) :
    let a : Γ(G, U) → Γ(Y, (p ≫ j) ⁻¹ᵁ U) :=
      fun x ↦ (finiteStructureAdjoint j p G psi.hom).app U x
    a (mu.app U (tmulSection x y)) = a x * a y := by
  dsimp only
  have hu := congrArg (fun z ↦ z.app U (tmulSection x y))
    ((Classical.choose (exists_tensorPullbackAdjunction j)).unit_naturality mu).symm
  change ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app G).app U
      (mu.app U (tmulSection x y)) =
    ((tensorPullback j).map mu).app (j ⁻¹ᵁ U)
      (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (G ⊗ G)).app U (tmulSection x y)) at hu
  simp only [finiteStructureAdjoint, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app, pushforwardComp_hom_app_app]
  erw [hu, hmu]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  erw [inv_app_hom_app_apply_of_iso psi.symm]
  erw [(Classical.choose_spec (module_pullback_tensor j)).2 G G U x y]
  have hh := tensorHom_app_tmulSection (X := S) psi.hom psi.hom
    (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app G).app U x)
    (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app G).app U y)
  erw [hh]
  exact hm (j ⁻¹ᵁ U) _ _

private theorem exists_reduced_products
    (X : Scheme.{u}) (T Y : ℕ → Scheme.{u})
    (j : ∀ n, T n ⟶ X) (p : ∀ n, Y n ⟶ T n)
    (i : ∀ n, T n ⟶ T (n + 1)) (g : ∀ n, Y n ⟶ Y (n + 1))
    (wj : ∀ n, i n ≫ j (n + 1) = j n)
    (wp : ∀ n, g n ≫ p (n + 1) = p n ≫ i n)
    (c : ∀ n, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅ tensorPullback (j n))
    (hc : ∀ n, c n = (tensorPullbackCompositionIso (i n) (j (n + 1)) (j n) (wj n)).symm)
    (G : X.Modules)
    (psi : ∀ n, (tensorPullback (j n)).obj G ≅
      (pushforward (p n)).obj (SheafOfModules.unit (Y n).ringCatSheaf))
    (hpsi : ∀ n, (tensorPullback (i n)).map (psi (n + 1)).hom ≫
      (moduleBaseChangeMap (p (n + 1)) (p n) (i n) (g n) (wp n)
        (SheafOfModules.unit (Y (n + 1)).ringCatSheaf) ≫
        (pushforward (p n)).map (tensorPullbackObjUnitToUnit (g n))) =
      (c n).hom.app G ≫ (psi n).hom) :
    ∃ v : ∀ n, (tensorPullback (j n)).obj (G ⊗ G) ⟶ (tensorPullback (j n)).obj G,
      (∀ n, (c n).hom.app (G ⊗ G) ≫ v n =
        (tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app G) ∧
      (∀ (mu : G ⊗ G ⟶ G), (∀ n, (tensorPullback (j n)).map mu = v n) →
        ∀ (n : ℕ) (U : X.Opens),
        let a : Γ(G, U) → Γ(Y n, (p n ≫ j n) ⁻¹ᵁ U) :=
          fun x ↦ (finiteStructureAdjoint (j n) (p n) G (psi n).hom).app U x
        ∀ x y : Γ(G, U), a (mu.app U (tmulSection x y)) = a x * a y) := by
  classical
  choose m hm using fun n ↦ exists_structure_product (p n)
  let delta := fun n ↦ Classical.choose (module_pullback_tensor (j n)) G G
  let v : ∀ n, (tensorPullback (j n)).obj (G ⊗ G) ⟶ (tensorPullback (j n)).obj G :=
    fun n ↦ (delta n).hom ≫ ((psi n).hom ⊗ₘ (psi n).hom) ≫ m n ≫ (psi n).inv
  refine ⟨v, ?_, ?_⟩
  · intro n
    exact reduced_product_compatible (i n) (j (n + 1)) (j n) (wj n)
      (p (n + 1)) (p n) (g n) (wp n) (c n) (hc n) G
      (psi (n + 1)) (psi n) (hpsi n) (m (n + 1)) (m n) (hm (n + 1)) (hm n)
  · intro mu hmu n U
    dsimp only
    intro x y
    exact product_adjoint_formula (j n) (p n) G (psi n) (m n) (hm n) mu (hmu n) U x y

/-- A product lifting the reduced products, before proving any ring laws.
Source: Stacks Project, Tag 09ZT, multiplication paragraph; Tags 088E and 088F.

Proof: Choose a proper closed supporting subscheme annihilating G (0CYS). Its ideal
annihilates the tensor square. On affine opens the square is the tensor product of two
finite modules, so it is quasi-coherent of finite type and hence coherent on the
Noetherian scheme X. Write P_n = j_n^*, Q_n = i_n^*, and delta_n for the tensor comparison of P_n.
Let m_n be the direct-image product characterized by m_n(x tensor y) = xy on all opens.
Define v_n = delta_n followed by (psi_n tensor psi_n), m_n, and psi_n inverse.
This is a morphism P_n(G tensor G) to P_n(G). The base-change algebra formula says
Q_n(m_(n+1)) followed by beta equals delta_i followed by (beta tensor beta) and m_n.
The composition comparison kappa = c_n satisfies the tensor equation
kappa_(G tensor G) followed by delta_n = Q_n(delta_(n+1)) followed by delta_i and
(kappa_G tensor kappa_G). Prove this equation by taking adjoints, evaluating on
x tensor y, and using the adjunction mate unit identity for the pinned comparison;
the tensor comparisons take these unit images to the tensor of the individual images.
The sheaf tensor universal property then makes the equality a morphism identity.
Substitute hpsi, the displayed tensor equation, and the base-change product equation;
use naturality of delta_i with psi in both factors and cancel psi_n. The resulting
identity is c_n.app (G tensor G) followed by v_n = Q_n(v_(n+1)) followed by c_n.app G.
Fullness of completion (088E,
in the formulation 088F) lifts the compatible family to a map mu. Evaluate its
reduction equation after the tensor-adjunction unit: the tensor comparison takes
x tensor y to the tensor of the unit images. Applying psi and pushforward
composition gives precisely the adjoint multiplicativity formula below. This
construction imposes no unit, associativity or symmetry. The argument also applies
to zero modules, empty schemes, and I equal to the zero or unit ideal.
(blueprint: lem-weil-pbc-finite-structure-product-core). -/
theorem finite_structure_product_exists_core
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
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ μ : G ⊗ G ⟶ G, ∀ (n : ℕ) (U : X.Opens),
      let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
        fun x ↦ (Scheme.Modules.finiteStructureAdjoint
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
      ∀ (x y : Γ(G, U)), a (μ.app U (tmulSection x y)) = a x * a y := by
  classical
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  have wp : ∀ n, gn n ≫ fnY (n + 1) = fnY n ≫ i n := by
    intro n
    apply pullback.hom_ext
    · simpa only [Category.assoc, hi n] using hw n
    · simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ pullback.snd f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) (hcart n).flip.w
  obtain ⟨v, hv, hformula⟩ := exists_reduced_products X
    (fun n ↦ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    Yn j fnY i gn hi wp c hc G ψ hψ
  obtain ⟨hGG, hpGG, _⟩ := finite_structure_tensor_powers_supported A X f G hG hproper
  let d : ∀ n, tensorPullback (j (n + 1)) ⋙ tensorPullback (i n) ≅
      tensorPullback (j n) := fun n ↦
    (Classical.choice (nonempty_tensorPullbackComp (i n) (j (n + 1)))).symm ≪≫
      eqToIso (congrArg tensorPullback (hi n))
  have hj : ∀ n, IsClosedImmersion (j n) := by
    intro n
    dsimp only [j]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1))))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hvd := compatible_family_change (i := i) j hj d c G (G ⊗ G) hG hGG v hv
  obtain ⟨mu, hmu, _⟩ :=
    (grothendieck_existence_fullyFaithful A I f i hi hp d)
      G (G ⊗ G) hG hGG hproper hpGG v hvd
  exact ⟨mu, hformula mu hmu⟩

-- The preserved legacy endomorphism family is irrelevant to multiplication existence.
set_option linter.unusedVariables false in
/- A compatible finite-level family algebraizes to a product map whose sections multiply.
This is the algebraization and evaluation part of Tags 09ZT and 088F.
(blueprint: lem-weil-pbc-finite-structure-section-identity). -/
theorem finite_structure_product_section_identity
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
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom)
    (v : ℕ → (G ⟶ G))
    (hv : ∀ n : ℕ, v n = v (n + 1)) :
    ∃ μ : G ⊗ G ⟶ G, ∀ (n : ℕ) (U : X.Opens),
      let a : Γ(G, U) → Γ(Yn n, (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) :=
        fun x ↦ (Scheme.Modules.finiteStructureAdjoint
        (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) G (ψ n).hom).app U x
      ∀ (x y : Γ(G, U)), a (μ.app U (tmulSection x y)) = a x * a y  := by
  exact finite_structure_product_exists_core A I X f i hi hp c hc Yn fnY gn hcart hw
    G hG hproper ψ hψ




end AlgebraicGeometry
