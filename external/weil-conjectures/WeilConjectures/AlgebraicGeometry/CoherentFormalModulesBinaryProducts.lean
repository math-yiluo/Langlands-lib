/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoInvariant
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Binary products preserve coherent formal modules

Source: Stacks Project, Section 0EHN and Lemma 087X, binary-sum argument written out.
(blueprint: lem-weil-pbc-coherent-formal-finite-products-binary-products)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private def quotientFunctor {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    X.Modules ⥤ X.Modules where
  obj F := formalModuleQuotient I n F
  map f := formalModuleQuotientMap I f (Nat.le_refl n)
  map_id F := formalModuleQuotientMap_id I F n
  map_comp f g := formalModuleQuotientMap_comp I f g (Nat.le_refl n) (Nat.le_refl n)

set_option backward.isDefEq.respectTransparency false in
private theorem quotientFunctorAdditive {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (quotientFunctor I n).Additive := by
  constructor
  intro F G f g
  apply (cancel_epi (cokernel.π
      (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F))).1
  simp [quotientFunctor, formalModuleQuotientMap, formalModuleQuotientπ,
    Preadditive.comp_add, Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
private def sumSystem {X : Scheme.{u}} (F G : ℕᵒᵖ ⥤ X.Modules) : ℕᵒᵖ ⥤ X.Modules where
  obj n := F.obj n ⊞ G.obj n
  map f := biprod.map (F.map f) (G.map f)
  map_id n := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private def sumFst {X : Scheme.{u}} (F G : ℕᵒᵖ ⥤ X.Modules) : sumSystem F G ⟶ F where
  app n := biprod.fst
  naturality _ _ f := by simp [sumSystem]

set_option backward.isDefEq.respectTransparency false in
private def sumSnd {X : Scheme.{u}} (F G : ℕᵒᵖ ⥤ X.Modules) : sumSystem F G ⟶ G where
  app n := biprod.snd
  naturality _ _ f := by simp [sumSystem]

set_option backward.isDefEq.respectTransparency false in
private def sumLift {X : Scheme.{u}} {F G T : ℕᵒᵖ ⥤ X.Modules}
    (f : T ⟶ F) (g : T ⟶ G) : T ⟶ sumSystem F G where
  app n := biprod.lift (f.app n) (g.app n)
  naturality _ _ h := by
    apply biprod.hom_ext <;> simp only [sumSystem, Category.assoc,
      biprod.lift_fst, biprod.lift_snd, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      ← f.naturality h, ← g.naturality h]

set_option backward.isDefEq.respectTransparency false in
private def sumIsLimit {X : Scheme.{u}} (F G : ℕᵒᵖ ⥤ X.Modules) :
    IsLimit (BinaryFan.mk (sumFst F G) (sumSnd F G)) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ sumLift f g)
    (by intros; ext; simp [sumLift, sumFst])
    (by intros; ext; simp [sumLift, sumSnd])
    (by
      intro T f g m hm hn
      apply NatTrans.ext
      funext n
      apply biprod.hom_ext
      · simpa [sumLift, sumFst] using congrArg (fun k ↦ k.app n) hm
      · simpa [sumLift, sumSnd] using congrArg (fun k ↦ k.app n) hn)

set_option backward.isDefEq.respectTransparency false in
/-- Binary products of coherent formal modules are coherent formal.
Source: Stacks Project, Cohomology of Schemes, Section 0EHN and Lemma 087X,
binary-sum argument written out.
(blueprint: lem-weil-pbc-coherent-formal-finite-products-binary-products).

Take the inverse system H with H_n = F_n ⊞ G_n and diagonal transition maps.
The coherent kernel/cokernel theorem gives coherence of H_n. On an affine open,
the ideal-times-quasi-coherent-affine-sections theorem identifies multiplication
by I^(n+1) on H_n with the sum of the two ideal products. Both summands vanish,
so the ideal product vanishes. The same section calculation identifies
H_(n+1)/I^(n+1)H_(n+1) with the sum of the two quotients. Their given transition
isomorphisms therefore give an isomorphism to H_n, whose composite with the
quotient projection is the diagonal transition map. These affine identities
glue because the maps are induced by the canonical inclusions and projections.
Products of module sheaves and inverse systems are computed termwise, and in
this abelian category binary products are biproducts. Thus H is an ambient
binary product. Any other limiting binary cone is uniquely isomorphic to H.
Transport termwise coherence through these isomorphisms, and ideal products
and cokernels by their universal properties, to prove the assertion for every
limiting binary cone, including when one or both factors are zero.
-/
theorem coherentFormalModules_closedUnderBinaryProducts (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderBinaryProducts := by
  constructor
  rintro B ⟨p⟩
  let F := p.diag.obj ⟨WalkingPair.left⟩
  let G := p.diag.obj ⟨WalkingPair.right⟩
  have hF : IsCoherentFormalModule I F := p.prop_diag_obj ⟨WalkingPair.left⟩
  have hG : IsCoherentFormalModule I G := p.prop_diag_obj ⟨WalkingPair.right⟩
  have hsum : IsCoherentFormalModule I (sumSystem F G) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      exact ((Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule X).1
        _ _ (hF.1 n) (hG.1 n)).2
    · intro n
      have hi : Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n) ⊞ G.obj (op n)) = 0 := by
        apply biprod.hom_ext
        · obtain ⟨k, hk⟩ := formalModuleQuotient_factor I
            (biprod.fst : (F.obj (op n) ⊞ G.obj (op n)) ⟶ F.obj (op n)) (Nat.le_refl (n + 1))
          have hz : Scheme.idealModuleProductι
              (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n)) = 0 :=
            (hF.2.1 n).eq_zero_of_src _
          rw [hk, hz, comp_zero, zero_comp]
        · obtain ⟨k, hk⟩ := formalModuleQuotient_factor I
            (biprod.snd : (F.obj (op n) ⊞ G.obj (op n)) ⟶ G.obj (op n)) (Nat.le_refl (n + 1))
          have hz : Scheme.idealModuleProductι
              (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (G.obj (op n)) = 0 :=
            (hG.2.1 n).eq_zero_of_src _
          rw [hk, hz, comp_zero, zero_comp]
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      have : Mono (Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n) ⊞ G.obj (op n))) := by
        dsimp [Scheme.idealModuleProductι]
        infer_instance
      exact IsZero.of_mono_eq_zero _ hi
    · intro n
      obtain ⟨a, ha⟩ := hF.2.2 n
      obtain ⟨b, hb⟩ := hG.2.2 n
      let Q := quotientFunctor I (n + 1)
      have : Q.Additive := quotientFunctorAdditive I (n + 1)
      let := preservesBinaryBiproducts_of_preservesBinaryProducts Q
      refine ⟨Q.mapBiprod (F.obj (op (n + 1))) (G.obj (op (n + 1))) ≪≫
        biprod.mapIso a b, ?_⟩
      apply biprod.hom_ext
      · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
          Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, sumSystem]
        change formalModuleQuotientπ I (n + 1) _ ≫
          formalModuleQuotientMap I biprod.fst (Nat.le_refl (n + 1)) ≫ a.hom = _
        rw [← Category.assoc, formalModuleQuotientMap, formalModuleQuotientπ,
          cokernel.π_desc, Category.assoc, ha]
      · simp only [Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom,
          Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, sumSystem]
        change formalModuleQuotientπ I (n + 1) _ ≫
          formalModuleQuotientMap I biprod.snd (Nat.le_refl (n + 1)) ≫ b.hom = _
        rw [← Category.assoc, formalModuleQuotientMap, formalModuleQuotientπ,
          cokernel.π_desc, Category.assoc, hb]
  let q := p.toLimitPresentation.changeDiag (diagramIsoPair p.diag).symm
  exact coherentFormalModules_of_iso X I
    ((sumIsLimit F G).conePointUniqueUpToIso q.isLimit) hsum

end

end AlgebraicGeometry
