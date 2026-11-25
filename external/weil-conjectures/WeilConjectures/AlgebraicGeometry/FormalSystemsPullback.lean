/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealPowerProductImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Pullback of coherent formal systems

Source: Stacks Project, Cohomology of Schemes, Lemma 0887 and the completion identity
in the proof of Lemma 088B (blueprint: lem-weil-pbc-formal-systems-pullback).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

open CategoryTheory.Limits in
private def powerQuotientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotient (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≅
      (Scheme.Modules.tensorPullback f).obj (formalModuleQuotient J n G) := by
  let T := Scheme.Modules.tensorPullback f
  let : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 G
  let k := Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι n).2 (T.obj G)
  have : Mono k := by dsimp [k, Scheme.idealModuleProductι]; infer_instance
  have he : Subobject.mk k = Subobject.mk (image.ι (T.map i)) := by
    rw [← imageSubobject_mono k]
    exact (modulePullbackIdealPowerProductImage f J G hG n).symm
  let e := Subobject.isoOfMkEqMk k (image.ι (T.map i)) he
  exact cokernel.mapIso k (image.ι (T.map i)) e (Iso.refl _) (by simp [e]) ≪≫
    cokernelImageι (T.map i) ≪≫ (PreservesCokernel.iso T i).symm

open CategoryTheory.Limits in
private theorem powerQuotientIso_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    formalModuleQuotientπ (J.comap f) n ((Scheme.Modules.tensorPullback f).obj G) ≫
        (powerQuotientIso f J G hG n).hom =
      (Scheme.Modules.tensorPullback f).map (formalModuleQuotientπ J n G) := by
  let T := Scheme.Modules.tensorPullback f
  let : T.IsLeftAdjoint := ⟨_, Scheme.Modules.nonempty_tensorPullbackAdjunction f⟩
  dsimp only [powerQuotientIso, Iso.trans_hom, Iso.symm_hom]
  rw [PreservesCokernel.iso_inv]
  simp [formalModuleQuotientπ, cokernel.mapIso, cokernelImageι]

open CategoryTheory.Limits in
private theorem quotientMap_π {X : Scheme.{u}} (J : X.IdealSheafData)
    {G H : X.Modules} (a : G ⟶ H) {m n : ℕ} (h : n ≤ m) :
    formalModuleQuotientπ J m G ≫ formalModuleQuotientMap J a h =
      a ≫ formalModuleQuotientπ J n H := by
  exact cokernel.π_desc _ _ _

open CategoryTheory.Limits in
private theorem powerQuotientIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) {G H : Y.Modules}
    (hG : G.IsQuasicoherent) (hH : H.IsQuasicoherent)
    (a : G ⟶ H) {m n : ℕ} (h : n ≤ m) :
    (powerQuotientIso f J G hG m).hom ≫
        (Scheme.Modules.tensorPullback f).map (formalModuleQuotientMap J a h) =
      formalModuleQuotientMap (J.comap f) ((Scheme.Modules.tensorPullback f).map a) h ≫
        (powerQuotientIso f J H hH n).hom := by
  let T := Scheme.Modules.tensorPullback f
  apply (cancel_epi (cokernel.π (Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι m).2 (T.obj G)))).1
  change formalModuleQuotientπ (J.comap f) m (T.obj G) ≫ _ =
    formalModuleQuotientπ (J.comap f) m (T.obj G) ≫ _
  rw [← Category.assoc, powerQuotientIso_π, ← T.map_comp, quotientMap_π, T.map_comp]
  rw [← Category.assoc, quotientMap_π, Category.assoc, powerQuotientIso_π]

open CategoryTheory.Limits in
private theorem coherent_pullback {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (G : Y.Modules)
    (hG : RingedSpace.IsCoherent Y.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace ((Scheme.Modules.tensorPullback f).obj G) := by
  have h := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y G).mp hG
  have : G.IsQuasicoherent := h.1
  have : G.IsFiniteType := h.2
  let e := (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  have hq := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (e.app G).symm (inferInstanceAs (((Scheme.Modules.pullback f).obj G).IsQuasicoherent))
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
    ⟨hq, (Scheme.Modules.tensorPullback_isFiniteType X Y f G).1⟩

open CategoryTheory.Limits in
private theorem powerProduct_pullback_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 G)) :
    IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (J.comap f).toModulesι n).2
      ((Scheme.Modules.tensorPullback f).obj G)) := by
  let T := Scheme.Modules.tensorPullback f
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 G
  let k := Scheme.idealModuleProductι
    (Scheme.idealSheafPower (J.comap f).toModulesι n).2 (T.obj G)
  have hi : i = 0 := hz.eq_zero_of_src i
  have hq : IsIso (formalModuleQuotientπ J n G) := by
    change IsIso (cokernel.π i)
    rw [hi]
    infer_instance
  have hp : IsIso (formalModuleQuotientπ (J.comap f) n (T.obj G)) := by
    have he := powerQuotientIso_π f J G hG n
    have : IsIso (formalModuleQuotientπ (J.comap f) n (T.obj G) ≫
        (powerQuotientIso f J G hG n).hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (powerQuotientIso f J G hG n).hom
  have : Mono k := by dsimp [k, Scheme.idealModuleProductι]; infer_instance
  apply IsZero.of_mono_eq_zero k
  apply (cancel_mono (formalModuleQuotientπ (J.comap f) n (T.obj G))).1
  exact (cokernel.condition k).trans zero_comp.symm

open CategoryTheory.Limits in
private theorem coherentFormal_pullback {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData)
    (G : CoherentFormalModule Y J) :
    IsCoherentFormalModule (J.comap f) (G.obj ⋙ Scheme.Modules.tensorPullback f) := by
  have hq (n : ℕ) : (G.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mp
      (G.property.1 n)).1
  refine ⟨fun n ↦ coherent_pullback f _ (G.property.1 n), ?_, ?_⟩
  · intro n
    exact powerProduct_pullback_zero f J _ (hq n) (n + 1) (G.property.2.1 n)
  · intro n
    obtain ⟨e, he⟩ := G.property.2.2 n
    refine ⟨powerQuotientIso f J _ (hq (n + 1)) (n + 1) ≪≫
      (Scheme.Modules.tensorPullback f).mapIso e, ?_⟩
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map]
    rw [← Category.assoc, powerQuotientIso_π, ← Functor.map_comp, he]

open CategoryTheory.Limits in
private def completionPullbackIso {X Y : Scheme.{u}}
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
      Scheme.Modules.tensorPullback f) ⋙ formalCompletionFunctor (J.comap f) ≅
    (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
      formalCompletionFunctor J) ⋙
      (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj
        (Scheme.Modules.tensorPullback f) := by
  let hq (G : CoherentModules Y) : G.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).mp G.property).1
  refine NatIso.ofComponents (fun G ↦ NatIso.ofComponents
    (fun n ↦ powerQuotientIso f J G.obj (hq G) (n.unop + 1)) ?_) ?_
  · rename_i G
    intro a b t
    change formalModuleQuotientMap (J.comap f)
        (𝟙 ((Scheme.Modules.tensorPullback f).obj G.obj))
        (Nat.succ_le_succ (leOfHom t.unop)) ≫
          (powerQuotientIso f J G.obj (hq G) (b.unop + 1)).hom =
      (powerQuotientIso f J G.obj (hq G) (a.unop + 1)).hom ≫
        (Scheme.Modules.tensorPullback f).map (formalModuleQuotientMap J (𝟙 G.obj)
          (Nat.succ_le_succ (leOfHom t.unop)))
    have hn := (powerQuotientIso_naturality f J (hq G) (hq G) (𝟙 G.obj)
      (Nat.succ_le_succ (leOfHom t.unop))).symm
    rw [(Scheme.Modules.tensorPullback f).map_id] at hn
    exact hn
  · intro G H a
    apply NatTrans.ext
    funext n
    exact (powerQuotientIso_naturality f J (hq G) (hq H) a.hom
      (Nat.le_refl (n.unop + 1))).symm

/-- Termwise tensor pullback defines the functor on coherent formal systems, and it
commutes naturally with completion. On an open subscheme it is restriction, and restriction
commutes naturally with completion with respect to the restricted ideal.

Source: Stacks, Lemma 0887 and proof of Lemma 088B
(blueprint: lem-weil-pbc-formal-systems-pullback).

Proof (the seven steps of the node):
1. The extended ideal is `J.comap f`. By lem-weil-pbc-module-pullback-ideal-quotient,
   extension commutes with powers and pullback of G/J^n G is f*G/I^n f*G, naturally in G.
2. Each pulled-back term is quasi-coherent and of finite type, hence coherent on the
   locally Noetherian source (pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-module-pullback-quasi-coherent,
   lem-weil-pbc-support-pullback-finite-type).
3. J^n G_n = 0 makes the quotient projection an isomorphism. Its pullback is an
   isomorphism whose kernel is I^n f*G_n, so that product is zero.
4. Factor each transition through the quotient isomorphism in step 1 and the pullback
   of the original quotient-to-term isomorphism. This is again an isomorphism.
5. Pull back compatible families of maps termwise. Functoriality of tensorPullback
   gives compatibility and the identity and composition laws.
6. The quotient comparisons commute with transitions: precompose both composites with
   the quotient projection, use the defining equations, and cancel the epimorphism.
   Their componentwise inverses give an isomorphism of systems. Naturality of the
   quotient comparisons makes this an isomorphism of completion functors.
7. For an open immersion tensor pullback is naturally restriction
   (lem-weil-pbc-open-immersion-module-pullback-restriction). The structure-sheaf
   comparison identifies the extended ideal with the restricted ideal
   (lem-weil-pbc-module-pullback-structure-sheaf, def-nagata-extended-ideal).
   Restriction preserves cokernels and ideal products
   (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections), giving the final comparison.

The equations with the full-subcategory inclusions specify both objects and morphisms
of the two functors; thus the existential functors cannot be arbitrary functors.
The final comparison is stated in the ambient system category, whose full-subcategory
inclusion is fully faithful. -/
theorem exists_formalSystemsPullback {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (∃ (P : CoherentFormalModule Y J ⥤ CoherentFormalModule X (J.comap f))
        (C : CoherentModules Y ⥤ CoherentModules X),
      P ⋙ ObjectProperty.ι (IsCoherentFormalModule (J.comap f)) =
        ObjectProperty.ι (IsCoherentFormalModule J) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj
            (Scheme.Modules.tensorPullback f) ∧
      C ⋙ ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) =
        ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          Scheme.Modules.tensorPullback f ∧
      Nonempty (completion Y J ⋙ P ≅ C ⋙ completion X (J.comap f))) ∧
    (∀ U : Y.Opens,
      Nonempty (Scheme.Modules.tensorPullback U.ι ≅ Scheme.Modules.restrictFunctor U.ι) ∧
      Nonempty (
        (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          formalCompletionFunctor J) ⋙
            (Functor.whiskeringRight ℕᵒᵖ Y.Modules U.toScheme.Modules).obj
              (Scheme.Modules.restrictFunctor U.ι) ≅
        (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙
          Scheme.Modules.restrictFunctor U.ι) ⋙ formalCompletionFunctor (J.comap U.ι))) := by
  classical
  let T := Scheme.Modules.tensorPullback f
  let W := (Functor.whiskeringRight ℕᵒᵖ Y.Modules X.Modules).obj T
  let P : CoherentFormalModule Y J ⥤ CoherentFormalModule X (J.comap f) :=
    ObjectProperty.lift (IsCoherentFormalModule (J.comap f))
      (ObjectProperty.ι (IsCoherentFormalModule J) ⋙ W)
      (coherentFormal_pullback f J)
  let C : CoherentModules Y ⥤ CoherentModules X :=
    ObjectProperty.lift (RingedSpace.IsCoherent X.toRingedSpace)
      (ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace) ⋙ T)
      (fun G ↦ coherent_pullback f G.obj G.property)
  refine ⟨⟨P, C, rfl, rfl, ?_⟩, ?_⟩
  · exact ⟨Functor.fullyFaithfulCancelRight
      (ObjectProperty.ι (IsCoherentFormalModule (J.comap f)))
      (completionPullbackIso f J).symm⟩
  · intro U
    let t : Scheme.Modules.tensorPullback U.ι ≅ Scheme.Modules.restrictFunctor U.ι :=
      (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
        (Scheme.Modules.restrictAdjunction U.ι)
    refine ⟨⟨t⟩, ⟨?_⟩⟩
    let I := ObjectProperty.ι (RingedSpace.IsCoherent Y.toRingedSpace)
    let WU := Functor.whiskeringRight ℕᵒᵖ Y.Modules U.toScheme.Modules
    exact Functor.isoWhiskerLeft (I ⋙ formalCompletionFunctor J) (WU.mapIso t).symm ≪≫
      (completionPullbackIso U.ι J).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft I t)
        (formalCompletionFunctor (J.comap U.ι))

end
end AlgebraicGeometry
