import Langlands.AlgebraicGeometry.Picard.InfinitesimalSimultaneousTrivialization
import Mathlib.RingTheory.RingHom.Flat

/-! # Actual affine sections in infinitesimal squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineSquareSections

section Tensor

variable {k S A B D E : Type u}
  [CommRing k] [CommRing S] [CommRing A] [CommRing B] [CommRing D] [CommRing E]
  [Algebra k S] [Algebra k A] [Algebra k B]

/-- The canonical tensor identification of a specified pushout of actual rings. -/
def tensorPushoutIso (s : CommRingCat.of S ⟶ CommRingCat.of D)
    (a : CommRingCat.of A ⟶ CommRingCat.of D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k A)) s a) :
    CommRingCat.of (S ⊗[k] A) ≅ CommRingCat.of D :=
  (CommRingCat.isPushout_tensorProduct k S A).isoIsPushout _ _ h

@[reassoc (attr := simp)]
lemma tensorPushoutIso_left (s : CommRingCat.of S ⟶ CommRingCat.of D)
    (a : CommRingCat.of A ⟶ CommRingCat.of D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k A)) s a) :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[k] A) ≫
      (tensorPushoutIso s a h).hom = s :=
  (CommRingCat.isPushout_tensorProduct k S A).inl_isoIsPushout_hom _ _ h

@[reassoc (attr := simp)]
lemma tensorPushoutIso_right (s : CommRingCat.of S ⟶ CommRingCat.of D)
    (a : CommRingCat.of A ⟶ CommRingCat.of D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k A)) s a) :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* S ⊗[k] A) ≫
      (tensorPushoutIso s a h).hom = a :=
  (CommRingCat.isPushout_tensorProduct k S A).inr_isoIsPushout_hom _ _ h

lemma tensorPushoutIso_naturality (p : A →ₐ[k] B)
    (sD : CommRingCat.of S ⟶ CommRingCat.of D) (aD : CommRingCat.of A ⟶ CommRingCat.of D)
    (sE : CommRingCat.of S ⟶ CommRingCat.of E) (bE : CommRingCat.of B ⟶ CommRingCat.of E)
    (hD : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k A)) sD aD)
    (hE : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k B)) sE bE)
    (t : CommRingCat.of D ⟶ CommRingCat.of E)
    (hs : sD ≫ t = sE) (ha : aD ≫ t = CommRingCat.ofHom p.toRingHom ≫ bE) :
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom ≫
      (tensorPushoutIso sE bE hE).hom = (tensorPushoutIso sD aD hD).hom ≫ t := by
  apply (CommRingCat.isPushout_tensorProduct k S A).hom_ext
  · change CommRingCat.ofHom _ ≫ _ = CommRingCat.ofHom _ ≫ _
    rw [← Category.assoc]
    have hm : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[k] A) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[k] B) := by
      ext z
      simp
    rw [hm, tensorPushoutIso_left, tensorPushoutIso_left_assoc, hs]
  · rw [← Category.assoc]
    have hm : CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* S ⊗[k] A) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k S) p).toRingHom =
        CommRingCat.ofHom p.toRingHom ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight.toRingHom : B →+* S ⊗[k] B) := by
      ext z
      simp
    rw [hm, Category.assoc, tensorPushoutIso_right,
      tensorPushoutIso_right_assoc, ha]

end Tensor

section Flat

variable {k S R A B C R' A' B' C' : Type u}
  [CommRing k] [CommRing S] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [CommRing R'] [CommRing A'] [CommRing B'] [CommRing C']
  [Algebra k S] [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]

/-- Flat tensor base change, expressed through any actual pushout identifications. -/
lemma isPullback_of_pushouts [Module.Flat k S]
    (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
    (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (p' : CommRingCat.of R' ⟶ CommRingCat.of A')
    (q' : CommRingCat.of R' ⟶ CommRingCat.of B')
    (a' : CommRingCat.of A' ⟶ CommRingCat.of C')
    (b' : CommRingCat.of B' ⟶ CommRingCat.of C')
    (sR : CommRingCat.of S ⟶ CommRingCat.of R') (rR : CommRingCat.of R ⟶ CommRingCat.of R')
    (sA : CommRingCat.of S ⟶ CommRingCat.of A') (rA : CommRingCat.of A ⟶ CommRingCat.of A')
    (sB : CommRingCat.of S ⟶ CommRingCat.of B') (rB : CommRingCat.of B ⟶ CommRingCat.of B')
    (sC : CommRingCat.of S ⟶ CommRingCat.of C') (rC : CommRingCat.of C ⟶ CommRingCat.of C')
    (hR : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k R)) sR rR)
    (hA : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k A)) sA rA)
    (hB : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k B)) sB rB)
    (hC : IsPushout (CommRingCat.ofHom (algebraMap k S))
      (CommRingCat.ofHom (algebraMap k C)) sC rC)
    (hsp : sR ≫ p' = sA) (hrp : rR ≫ p' = CommRingCat.ofHom p.toRingHom ≫ rA)
    (hsq : sR ≫ q' = sB) (hrq : rR ≫ q' = CommRingCat.ofHom q.toRingHom ≫ rB)
    (hsa : sA ≫ a' = sC) (hra : rA ≫ a' = CommRingCat.ofHom a.toRingHom ≫ rC)
    (hsb : sB ≫ b' = sC) (hrb : rB ≫ b' = CommRingCat.ofHom b.toRingHom ≫ rC) :
    IsPullback p' q' a' b' :=
  (InfinitesimalFlatBaseChange.isPullback_tensor (S := S) p q a b h).of_iso
    (tensorPushoutIso sR rR hR) (tensorPushoutIso sA rA hA)
    (tensorPushoutIso sB rB hB) (tensorPushoutIso sC rC hC)
    (tensorPushoutIso_naturality p sR rR sA rA hR hA p' hsp hrp)
    (tensorPushoutIso_naturality q sR rR sB rB hR hB q' hsq hrq)
    (tensorPushoutIso_naturality a sA rA sC rC hA hC a' hsa hra)
    (tensorPushoutIso_naturality b sB rB sC rC hB hC b' hsb hrb)

end Flat

end Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineSquareSections
