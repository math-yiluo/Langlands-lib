/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ThickeningCompletionHomDictionary
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # Restriction of morphisms on a common proper closed support

Source: Stacks Project, Tags 088E and 088F
(blueprint: lem-weil-pbc-grothendieck-existence-supported-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Bijectivity of a functor map is invariant under isomorphisms of its endpoints. -/
private theorem map_bijective_of_isos
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {P Q P' Q' : C} (a : P ≅ P') (b : Q ≅ Q')
    (h : Function.Bijective (T.map : (P' ⟶ Q') → _)) :
    Function.Bijective (T.map : (P ⟶ Q) → _) := by
  have square (w : P ⟶ Q) :
      T.map (Iso.homCongr a b w) =
        Iso.homCongr (T.mapIso a) (T.mapIso b) (T.map w) := by
    simp only [Iso.homCongr_apply, Functor.map_comp, Functor.mapIso_inv, Functor.mapIso_hom]
  constructor
  · intro w w' hw
    apply (Iso.homCongr a b).injective
    apply h.injective
    rw [square, square, hw]
  · intro v
    obtain ⟨w, hw⟩ := h.surjective (Iso.homCongr (T.mapIso a) (T.mapIso b) v)
    refine ⟨(Iso.homCongr a b).symm w, ?_⟩
    apply (Iso.homCongr (T.mapIso a) (T.mapIso b)).injective
    rw [← square, Equiv.apply_symm_apply, hw]

/-- Transport proper completion on Z through closed pushforward and the invertible units. -/
private theorem supported_formalCompletionMap_bijective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j] [IsProper (j ≫ f)]
    (hkillF : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(F, V), a • t = 0)
    (hkillG : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(G, V), a • t = 0) :
    Function.Bijective (formalCompletionMap
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) :
      (G ⟶ F) → _) := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (j ≫ f)
  let K := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let P := Scheme.Modules.pushforward j
  obtain ⟨hP⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective P).mpr
    ((closedImmersion_pushforward_fullyFaithful j).2)
  let W := (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj P
  have hW : W.FullyFaithful := hP.whiskeringRight ℕᵒᵖ
  let C := completion Z (K.comap j)
  have hCmap (M N : CoherentModules Z) : Function.Bijective
      (C.map : (M ⟶ N) → _) := by
    dsimp only [C, K]
    rw [← Scheme.IdealSheafData.comap_comp]
    exact formalCompletion_map_bijective_of_proper I (j ≫ f) M N
  obtain ⟨hC⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective C).mpr hCmap
  let U := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)
  let V := ObjectProperty.ι (IsCoherentFormalModule (K.comap j))
  have hCV : (C ⋙ V).FullyFaithful :=
    hC.comp (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (K.comap j)))
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence j K).2
  have hH : (U ⋙ P ⋙ formalCompletionFunctor K).FullyFaithful :=
    (hCV.comp hW).ofIso θ.symm
  have hFP := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have hGP := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have : F.IsQuasicoherent := hFP.1
  have : G.IsQuasicoherent := hGP.1
  have hFlift := (Scheme.Modules.closedImmersion_pushforward_annihilated j).2 F hkillF
  have hGlift := (Scheme.Modules.closedImmersion_pushforward_annihilated j).2 G hkillG
  let FZ : CoherentModules Z := ⟨(Scheme.Modules.tensorPullback j).obj F,
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z _).mpr
      ⟨hFlift.1, hFlift.2.2 hFP.2⟩⟩
  let GZ : CoherentModules Z := ⟨(Scheme.Modules.tensorPullback j).obj G,
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z _).mpr
      ⟨hGlift.1, hGlift.2.2 hGP.2⟩⟩
  have : IsIso ((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app F) := hFlift.2.1
  have : IsIso ((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app G) := hGlift.2.1
  let a : G ≅ P.obj GZ.obj := asIso ((Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app G)
  let b : F ≅ P.obj FZ.obj := asIso ((Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app F)
  have hcomposite := hH.map_bijective GZ FZ
  have hPcoh := ((ObjectProperty.fullyFaithfulι
    (RingedSpace.IsCoherent Z.toRingedSpace)).comp hP).map_bijective GZ FZ
  have hquot : Function.Bijective
      ((formalCompletionFunctor K).map : (P.obj GZ.obj ⟶ P.obj FZ.obj) → _) := by
    constructor
    · intro v w h
      obtain ⟨v', rfl⟩ := hPcoh.surjective v
      obtain ⟨w', rfl⟩ := hPcoh.surjective w
      exact congrArg (U ⋙ P).map (hcomposite.injective h)
    · intro v
      obtain ⟨w, hw⟩ := hcomposite.surjective v
      exact ⟨(U ⋙ P).map w, hw⟩
  exact map_bijective_of_isos (formalCompletionFunctor K) a b hquot

/-- Restriction gives a bijection on morphisms for modules annihilated by one proper closed
subscheme. This is the proper-case reduction, before using the support characterization.
Source: Stacks, Theorem 088E, first paragraph; Lemmas 087T and 0883,
with the thickening formulation of Remark 088F.
(blueprint: lem-weil-pbc-grothendieck-existence-supported-hom).

Proof:
1. The given closed subscheme Z is proper over A and its ideal kills both modules.
2. Closed-immersion coherent equivalence lifts F and G to coherent modules on Z and
identifies their Hom sets. Its formal version identifies the Hom sets of their
completions, naturally in both modules and compatibly with completion of a morphism.
3. Completion on Z is fully faithful by the proper completion theorem. Transport this
bijection through the two Hom identifications to obtain the completion bijection on X.
4. The thickening-systems dictionary identifies formal morphisms with precisely the
compatible families below, and sends completed w to its restrictions. Therefore the
restriction map is bijective. Naturality of c verifies that every restricted w is a
compatible family; its canonical comparison is the one specified by hc. -/
theorem grothendieckExistence_supported_hom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
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
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j] [IsProper (j ≫ f)]
    (hkillF : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(F, V), a • t = 0)
    (hkillG : ∀ (V : X.Opens) (a : Γ(X, V)), a ∈ j.ker.idealOfOpens V →
      ∀ t : Γ(G, V), a • t = 0) :
    Function.Bijective (fun w : G ⟶ F ↦
      (⟨fun n ↦
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).map w, fun n ↦ ((c n).hom.naturality w).symm⟩ :
        {v : ∀ n : ℕ,
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ⟶
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj F |
          ∀ n : ℕ, (c n).hom.app G ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F})) := by
  classical
  obtain ⟨e, he⟩ := thickeningSystems_completion_hom_equiv
    A I f i hi hp c F G hF hG
  have hcompletion := supported_formalCompletionMap_bijective
    I f F G hF hG Z j hkillF hkillG
  have h := e.bijective.comp hcompletion
  simpa only [Function.comp_def, he] using h

end AlgebraicGeometry
