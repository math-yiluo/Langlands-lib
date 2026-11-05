import Langlands.GroupScheme.Descent.TensorCoordinates
import Langlands.GroupScheme.Rational.GaloisIdealDescent
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois

/-! # Tensor coordinates of a represented radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TensorCoordinates

variable (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A]
    (X : Over (Spec (CommRingCat.of k)))
    (e : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ≅ X)

/-- Global sections in the chosen ground-field affine presentation. -/
def groundSectionsEquiv : A ≃+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫
    asIso e.inv.left.appTop).commRingCatIsoToRingEquiv

/-- The projection to the original affine scheme induces the ground tensor inclusion. -/
theorem projection_comp_groundSectionsEquiv :
    (pullback.fst X.hom (algebraBaseMap k K)).appTop.hom.comp
        (groundSectionsEquiv k A X e).toRingHom =
      (sectionsEquiv k K A X e).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom := by
  have h :
      (baseChangeIso k K A X e).inv ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) =
        pullback.fst X.hom (algebraBaseMap k K) ≫ e.inv.left := by
    apply (cancel_epi (baseChangeIso k K A X e).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [baseChangeIso_hom_fst]
    simp
    exact (Category.comp_id _).symm
  have ht := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at ht
  change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.inv.left.appTop) ≫
      (pullback.fst X.hom (algebraBaseMap k K)).appTop).hom =
    ((CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A))).inv ≫
          (baseChangeIso k K A X e).inv.appTop).hom
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, ht]

/-- On global sections the canonical semilinear map is coefficient conjugation. -/
theorem sectionsEquiv_coefficientConjugate (σ : K ≃ₐ[k] K) (x : K ⊗[k] A) :
    sectionsEquiv k K A X e (TensorGaloisPoint.coefficientConjugate k K A σ x) =
      (conjugate k K X σ).appTop (sectionsEquiv k K A X e x) := by
  have h :
      (baseChangeIso k K A X e).inv ≫
          Spec.map (CommRingCat.ofHom
            (TensorGaloisPoint.coefficientConjugate k K A σ).toRingHom) =
        conjugate k K X σ ≫ (baseChangeIso k K A X e).inv := by
    apply (cancel_epi (baseChangeIso k K A X e).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← coefficientConjugate_baseChangeIso]
    simp
  have ht := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at ht
  change (((CommRingCat.ofHom
      (TensorGaloisPoint.coefficientConjugate k K A σ).toRingHom) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A))).inv) ≫
          (baseChangeIso k K A X e).inv.appTop).hom x =
    ((Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A))).inv ≫
      ((baseChangeIso k K A X e).inv.appTop ≫ (conjugate k K X σ).appTop)).hom x
  rw [Scheme.ΓSpecIso_inv_naturality, Category.assoc, ht]

end TensorCoordinates

namespace RadicalTensorIdeal

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- The canonical descent comparison followed by semilinear conjugation
is the first projection of the iterated pullback. -/
theorem descentIso_hom_conjugate (σ : K ≃ₐ[k] K) :
    (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G).hom.hom.hom.left ≫
        TensorCoordinates.conjugate k K G.X σ =
      pullback.fst (pullback.snd G.X.hom (algebraBaseMap k K))
        (galoisBaseMap k K σ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, TensorCoordinates.conjugate_fst,
      descentBaseChangeIso_hom_fst]
  · have hd := (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G).hom.hom.hom.w
    change (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G).hom.hom.hom.left ≫
          pullback.snd G.X.hom (algebraBaseMap k K) =
      pullback.snd (pullback.snd G.X.hom (algebraBaseMap k K))
        (galoisBaseMap k K σ) at hd
    rw [Category.assoc, TensorCoordinates.conjugate_snd, ← Category.assoc, hd]
    exact pullback.condition.symm

variable [IsAffineHom G.X.hom]

/-- A radical's source acquires the actual semilinear self-map from its
canonical Galois source comparison. -/
def sourceConjugate (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    U.X.left ⟶ U.X.left :=
  (hi.galoisSourceIso σ).inv.hom.hom.left ≫
    pullback.fst U.X.hom (galoisBaseMap k K σ)

/-- The radical inclusion intertwines the actual source and ambient
semilinear scheme maps. -/
theorem sourceConjugate_comp (hi : IsUnipotentRadical i) (σ : K ≃ₐ[k] K) :
    sourceConjugate hi σ ≫ i.hom.hom.left =
      i.hom.hom.left ≫ TensorCoordinates.conjugate k K G.X σ := by
  apply (cancel_epi (hi.galoisSourceIso σ).hom.hom.hom.left).mp
  have h := congrArg (fun f => f.hom.hom.left) (hi.galoisSourceIso_hom_comp σ)
  change (hi.galoisSourceIso σ).hom.hom.hom.left ≫ i.hom.hom.left =
    ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i).hom.hom.left ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G).hom.hom.hom.left at h
  have hs : (hi.galoisSourceIso σ).hom.hom.hom.left ≫ sourceConjugate hi σ =
      pullback.fst U.X.hom (galoisBaseMap k K σ) := by
    dsimp only [sourceConjugate]
    rw [← Category.assoc,
      show (hi.galoisSourceIso σ).hom.hom.hom.left ≫
        (hi.galoisSourceIso σ).inv.hom.hom.left = 𝟙 _ from
        congrArg (fun f => f.hom.hom.left) (hi.galoisSourceIso σ).hom_inv_id,
      Category.id_comp]
  rw [← Category.assoc, hs, ← Category.assoc, h, Category.assoc,
    descentIso_hom_conjugate]
  change pullback.fst U.X.hom (galoisBaseMap k K σ) ≫ i.hom.hom.left =
    ((Over.pullback (galoisBaseMap k K σ)).map i.hom.hom).left ≫ _
  simp only [Over.pullback_map_left]
  exact (pullback.lift_fst _ _ _).symm

variable (k K) (A : Type u) [CommRing A] [Algebra k A]
    (G)
    (e : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ≅ G.X)
    (i)

/-- The radical inclusion's actual global-section kernel in tensor coordinates. -/
def coordinateIdeal : Ideal (K ⊗[k] A) :=
  RingHom.ker (i.hom.hom.left.appTop.hom.comp
    (TensorCoordinates.sectionsEquiv k K A G.X e).toRingHom)

/-- The tensor-coordinate kernel is stable under every coefficient conjugation. -/
theorem coefficientConjugate_mem (hi : IsUnipotentRadical i)
    (σ : K ≃ₐ[k] K) (x : K ⊗[k] A)
    (hx : x ∈ coordinateIdeal (k := k) (K := K) (A := A) (G := G) (e := e) (i := i)) :
    TensorGaloisPoint.coefficientConjugate k K A σ x ∈
      coordinateIdeal (k := k) (K := K) (A := A) (G := G) (e := e) (i := i) := by
  change i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e
      (TensorGaloisPoint.coefficientConjugate k K A σ x)) = 0
  rw [TensorCoordinates.sectionsEquiv_coefficientConjugate]
  change (i.hom.hom.left ≫ TensorCoordinates.conjugate k K G.X σ).appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x) = 0
  rw [← sourceConjugate_comp hi σ]
  change (sourceConjugate hi σ).appTop (i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x)) = 0
  change i.hom.hom.left.appTop
    (TensorCoordinates.sectionsEquiv k K A G.X e x) = 0 at hx
  rw [hx, map_zero]

/-- Over a Galois extension the radical's coordinate ideal is extended
from its actual contraction to the original affine algebra. -/
theorem map_groundIdeal_eq [IsGalois k K] (hi : IsUnipotentRadical i) :
    (GaloisIdealDescent.groundIdeal k K A
      (coordinateIdeal (k := k) (K := K) (A := A) (G := G) (e := e) (i := i))).map
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom =
        coordinateIdeal (k := k) (K := K) (A := A) (G := G) (e := e) (i := i) :=
  GaloisIdealDescent.map_groundIdeal_eq k K A _
    (coefficientConjugate_mem (k := k) (K := K) (A := A) (G := G)
      (e := e) (i := i) hi)

end RadicalTensorIdeal

end Langlands.GroupScheme.Descent
