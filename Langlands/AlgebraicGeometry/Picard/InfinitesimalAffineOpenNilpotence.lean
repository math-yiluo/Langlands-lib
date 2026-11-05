import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenSquare

/-! # Nilpotent surjections on actual affine-open sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenNilpotence

/-- A commuting isomorphism square transports the actual kernel by ideal image. -/
lemma ker_eq_map_of_iso {R S R' S' : CommRingCat.{u}}
    (f : R ⟶ S) (g : R' ⟶ S') (eR : R ≅ R') (eS : S ≅ S')
    (w : f ≫ eS.hom = eR.hom ≫ g) :
    RingHom.ker g.hom = (RingHom.ker f.hom).map eR.hom.hom := by
  have hc : (RingHom.ker g.hom).comap eR.hom.hom = RingHom.ker f.hom := by
    ext x
    change g.hom (eR.hom.hom x) = 0 ↔ f.hom x = 0
    have hx := ConcreteCategory.congr_hom w x
    change eS.hom.hom (f.hom x) = g.hom (eR.hom.hom x) at hx
    rw [← hx]
    constructor
    · intro h
      exact eS.commRingCatIsoToRingEquiv.injective (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  rw [← hc]
  exact (Ideal.map_comap_of_surjective eR.hom.hom
    (show Function.Surjective eR.hom.hom from eR.commRingCatIsoToRingEquiv.surjective)
    (RingHom.ker g.hom)).symm

/-- Nilpotence of the kernel is invariant under a commuting isomorphism square. -/
lemma ker_isNilpotent_of_iso {R S R' S' : CommRingCat.{u}}
    (f : R ⟶ S) (g : R' ⟶ S') (eR : R ≅ R') (eS : S ≅ S')
    (w : f ≫ eS.hom = eR.hom ≫ g)
    (hn : IsNilpotent (RingHom.ker f.hom)) :
    IsNilpotent (RingHom.ker g.hom) := by
  rw [ker_eq_map_of_iso f g eR eS w]
  exact hn.map (Ideal.mapHom eR.hom.hom)

/-- Surjectivity is invariant under a commuting isomorphism square. -/
lemma surjective_of_iso {R S R' S' : CommRingCat.{u}}
    (f : R ⟶ S) (g : R' ⟶ S') (eR : R ≅ R') (eS : S ≅ S')
    (w : f ≫ eS.hom = eR.hom ≫ g)
    (hf : Function.Surjective f.hom) :
    Function.Surjective g.hom := by
  intro y
  obtain ⟨z, rfl⟩ := eS.commRingCatIsoToRingEquiv.surjective y
  obtain ⟨x, rfl⟩ := hf z
  exact ⟨eR.hom x, (ConcreteCategory.congr_hom w x).symm⟩

/-- A nilpotent surjection remains a nilpotent surjection in any actual ring
pushout. No flatness is needed. -/
lemma nilpotentSurjective_of_isPushout {B C S T : CommRingCat.{u}}
    (b : B ⟶ C) (s : B ⟶ S) (b' : S ⟶ T) (c : C ⟶ T)
    (h : IsPushout s b b' c)
    (hb : Function.Surjective b.hom) (hn : IsNilpotent (RingHom.ker b.hom)) :
    Function.Surjective b'.hom ∧ IsNilpotent (RingHom.ker b'.hom) := by
  let : Algebra B S := s.hom.toAlgebra
  let : Algebra B B := Algebra.id B
  let : Algebra B C := b.hom.toAlgebra
  let ba : B →ₐ[B] C := { __ := b.hom, commutes' := fun _ ↦ rfl }
  have hS : IsPushout (CommRingCat.ofHom (algebraMap B S))
      (CommRingCat.ofHom (algebraMap B B)) (𝟙 S) s := IsPushout.of_id_snd
  let eS := InfinitesimalAffineSquareSections.tensorPushoutIso (𝟙 S) s hS
  let eT := InfinitesimalAffineSquareSections.tensorPushoutIso b' c h
  let t := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id B S) ba).toRingHom
  have w : t ≫ eT.hom = eS.hom ≫ b' :=
    InfinitesimalAffineSquareSections.tensorPushoutIso_naturality ba
      (𝟙 S) s b' c hS h b' (by simp) h.w
  exact ⟨surjective_of_iso t b' eS eT w
      (InfinitesimalTensorNilpotence.tensor_surjective ba hb),
    ker_isNilpotent_of_iso t b' eS eT w
      (InfinitesimalTensorNilpotence.tensor_ker_isNilpotent ba hb hn)⟩

/-- The spectrum of the base-changed nilpotent surjection, with its actual map. -/
def pushoutSpecHomeomorph {B C S T : CommRingCat.{u}}
    (b : B ⟶ C) (s : B ⟶ S) (b' : S ⟶ T) (c : C ⟶ T)
    (h : IsPushout s b b' c)
    (hb : Function.Surjective b.hom) (hn : IsNilpotent (RingHom.ker b.hom)) :
    Spec T ≃ₜ Spec S :=
  InfinitesimalTensorNilpotence.specHomeomorph b'.hom
    (nilpotentSurjective_of_isPushout b s b' c h hb hn).1
    (nilpotentSurjective_of_isPushout b s b' c h hb hn).2

/-- Replacing the source open by an equal open preserves the sections property. -/
lemma resLE_appTop_nilpotentSurjective
    {Y Z : Scheme.{u}} (i : Y ⟶ Z) (W : Z.Opens) (V : Y.Opens)
    (e : V = i ⁻¹ᵁ W)
    (hi : Function.Surjective (i ∣_ W).appTop.hom ∧
      IsNilpotent (RingHom.ker (i ∣_ W).appTop.hom)) :
    Function.Surjective (i.resLE W V e.le).appTop.hom ∧
      IsNilpotent (RingHom.ker (i.resLE W V e.le).appTop.hom) := by
  subst V
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hi

section Relative

variable {k B C : Type u} [CommRing k] [CommRing B] [CommRing C]
  [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (b : B →ₐ[k] C) (hb : Function.Surjective b)
  (hn : IsNilpotent (RingHom.ker b.toRingHom))

include hb hn

/-- On any affine open of the target, the actual relative-space restriction
of a nilpotent surjection is again surjective on sections with nilpotent kernel. -/
lemma relativeRestriction_appTop_nilpotentSurjective
    (W : ((relativeSpace f).obj (affineBase k B)).Opens) (hW : IsAffineOpen W) :
    let i := (relativeSpace f).map (affineBaseMap b)
    Function.Surjective (i ∣_ W).appTop.hom ∧
      IsNilpotent (RingHom.ker (i ∣_ W).appTop.hom) := by
  dsimp only
  let i := (relativeSpace f).map (affineBaseMap b)
  let πB : (relativeSpace f).obj (affineBase k B) ⟶ Spec (CommRingCat.of B) :=
    (relativeProjection f).app (affineBase k B)
  let πC : (relativeSpace f).obj (affineBase k C) ⟶ Spec (CommRingCat.of C) :=
    (relativeProjection f).app (affineBase k C)
  let : IsAffine (affineBase k B).left := by
    change IsAffine (Spec (CommRingCat.of B))
    infer_instance
  let : IsAffine (affineBase k C).left := by
    change IsAffine (Spec (CommRingCat.of C))
    infer_instance
  let : IsAffine W.toScheme := hW
  let : IsAffineHom (affineBaseMap b).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom b.toRingHom))
    infer_instance
  let : IsAffineHom i := relativeSpace_map_isAffineHom f (affineBaseMap b)
  let : IsAffine (i ⁻¹ᵁ W).toScheme := hW.preimage i
  have hΓ : Function.Surjective (Spec.map (CommRingCat.ofHom b.toRingHom)).appTop.hom ∧
      IsNilpotent (RingHom.ker (Spec.map (CommRingCat.ofHom b.toRingHom)).appTop.hom) :=
    ⟨surjective_of_iso (CommRingCat.ofHom b.toRingHom) _
        (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
        (Scheme.ΓSpecIso_inv_naturality _) hb,
      ker_isNilpotent_of_iso (CommRingCat.ofHom b.toRingHom) _
        (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
        (Scheme.ΓSpecIso_inv_naturality _) hn⟩
  have hPB : IsPullback (i ∣_ W) ((i ⁻¹ᵁ W).ι ≫ πC)
      (W.ι ≫ πB) (Spec.map (CommRingCat.ofHom b.toRingHom)) :=
    (isPullback_morphismRestrict i W).paste_vert
      (relativeProjection_isPullback f (affineBaseMap b))
  exact nilpotentSurjective_of_isPushout (affineBaseMap b).left.appTop
    (W.ι ≫ πB).appTop (i ∣_ W).appTop ((i ⁻¹ᵁ W).ι ≫ πC).appTop
    (isPushout_appTop_of_isPullback hPB) hΓ.1 hΓ.2

end Relative

section RelativeSquare

variable {k R A B C : Type u} [CommRing k]
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
  (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom))

include hb hn

/-- The exact right restriction in the actual relative square is a nilpotent
surjection on sections over every affine open of the total scheme. -/
lemma rightRestriction_appTop_nilpotentSurjective
    (U : ((relativeSpace f).obj (affineBase k R)).Opens) (hU : IsAffineOpen U) :
    let i₁ := (relativeSpace f).map (affineBaseMap a)
    let i₂ := (relativeSpace f).map (affineBaseMap b)
    let j₁ := (relativeSpace f).map (affineBaseMap p)
    let j₂ := (relativeSpace f).map (affineBaseMap q)
    let w := PicardGroupoid.relativeSquare_comm f
      (affineBaseMap a) (affineBaseMap b) (affineBaseMap p) (affineBaseMap q)
      (PicardGroupoid.affineSquare_comm p q a b h)
    Function.Surjective
        (InfinitesimalAffineOpenSquare.rightRestriction i₁ i₂ j₁ j₂ w U).appTop.hom ∧
      IsNilpotent (RingHom.ker
        (InfinitesimalAffineOpenSquare.rightRestriction i₁ i₂ j₁ j₂ w U).appTop.hom) := by
  dsimp only
  let : IsAffineHom (affineBaseMap q).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom q.toRingHom))
    infer_instance
  let := relativeSpace_map_isAffineHom f (affineBaseMap q)
  have hW := hU.preimage ((relativeSpace f).map (affineBaseMap q))
  have hlocal := relativeRestriction_appTop_nilpotentSurjective f b hb hn
    (((relativeSpace f).map (affineBaseMap q)) ⁻¹ᵁ U) hW
  have e :
      (((relativeSpace f).map (affineBaseMap a) ≫
        (relativeSpace f).map (affineBaseMap p)) ⁻¹ᵁ U) =
      ((relativeSpace f).map (affineBaseMap b) ⁻¹ᵁ
        ((relativeSpace f).map (affineBaseMap q) ⁻¹ᵁ U)) := by
    rw [PicardGroupoid.relativeSquare_comm f
      (affineBaseMap a) (affineBaseMap b) (affineBaseMap p) (affineBaseMap q)
      (PicardGroupoid.affineSquare_comm p q a b h), Scheme.Hom.comp_preimage]
  exact resLE_appTop_nilpotentSurjective _ _ _ e hlocal

end RelativeSquare

end Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenNilpotence
