import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.SimplyConnected.DerivedCoverTorusProductSmoothReduction
import Langlands.GroupScheme.SmoothProducts

/-! # Simple connectedness of direct factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {C H : GroupScheme S}

/-- Taking a product with an identity preserves central isogenies. -/
theorem IsCentralIsogeny.tensor_id {f : C ⟶ H} (hf : IsCentralIsogeny f)
    (K : GroupScheme S) : IsCentralIsogeny (f ⊗ₘ 𝟙 K) := by
  have hpb := ((isPullback_tensorHom_id f.hom.hom K.X).map (Over.forget S)).flip
  refine ⟨⟨MorphismProperty.of_isPullback hpb hf.isFinite,
    MorphismProperty.of_isPullback hpb hf.flat,
    MorphismProperty.of_isPullback hpb hf.surjective⟩,
    MorphismProperty.of_isPullback hpb hf.locallyOfFinitePresentation, ?_⟩
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  change x ≫ (f.hom.hom ⊗ₘ 𝟙 K.X) = 1 at hx
  have hxC : (x ≫ fst C.X K.X) ≫ f.hom.hom = 1 := by
    have h := congrArg (fun w => w ≫ fst H.X K.X) hx
    simpa only [Category.assoc, tensorHom_fst, MonObj.one_comp] using h
  have hxK : x ≫ snd C.X K.X = 1 := by
    have h := congrArg (fun w => w ≫ snd H.X K.X) hx
    simpa only [Category.assoc, tensorHom_snd, Category.comp_id, MonObj.one_comp] using h
  intro T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (hf.mem_center_of_comp_eq_one hxC T' a (y ≫ fst C.X K.X)).eq
  · simp only [MonObj.mul_comp, Category.assoc, hxK, MonObj.comp_one, one_mul, mul_one]

/-- A product map with an identity reflects isomorphisms. -/
theorem isIso_of_tensor_id (f : C ⟶ H) (K : GroupScheme S)
    [IsIso (f ⊗ₘ 𝟙 K)] : IsIso f := by
  let iC : C ⟶ C ⊗ K := lift (𝟙 C) (Grp.homMk (toUnit C.X ≫ η[K.X]))
  let iH : H ⟶ H ⊗ K := lift (𝟙 H) (Grp.homMk (toUnit H.X ≫ η[K.X]))
  have hnatural : f ≫ iH = iC ≫ (f ⊗ₘ 𝟙 K) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [iC, iH]
    · simp only [iC, iH, Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]
      apply Grp.hom_ext
      change f.hom.hom ≫ (toUnit H.X ≫ η[K.X]) = toUnit C.X ≫ η[K.X]
      rw [← Category.assoc, toUnit_unique (f.hom.hom ≫ toUnit H.X) (toUnit C.X)]
  refine ⟨⟨iH ≫ inv (f ⊗ₘ 𝟙 K) ≫ fst C K, ?_, ?_⟩⟩
  · calc
      f ≫ (iH ≫ inv (f ⊗ₘ 𝟙 K) ≫ fst C K) =
          (f ≫ iH) ≫ inv (f ⊗ₘ 𝟙 K) ≫ fst C K := by simp only [Category.assoc]
      _ = (iC ≫ (f ⊗ₘ 𝟙 K)) ≫ inv (f ⊗ₘ 𝟙 K) ≫ fst C K := by rw [hnatural]
      _ = 𝟙 C := by
        rw [Category.assoc, IsIso.hom_inv_id_assoc]
        exact lift_fst _ _
  · have hproj : fst C K ≫ f = (f ⊗ₘ 𝟙 K) ≫ fst H K := by simp
    calc
      (iH ≫ inv (f ⊗ₘ 𝟙 K) ≫ fst C K) ≫ f =
          iH ≫ inv (f ⊗ₘ 𝟙 K) ≫ (fst C K ≫ f) := by simp only [Category.assoc]
      _ = iH ≫ inv (f ⊗ₘ 𝟙 K) ≫ ((f ⊗ₘ 𝟙 K) ≫ fst H K) := by rw [hproj]
      _ = 𝟙 H := by
        rw [IsIso.inv_hom_id_assoc]
        exact lift_fst _ _

end Base

section Field

variable {k : Type u} [Field k] {H K : GroupScheme (Spec (CommRingCat.of k))}

/-- A semisimple direct factor of a simply connected product is simply connected. -/
theorem IsSimplyConnected.of_tensor_left (h : IsSimplyConnected (H ⊗ K))
    (hH : IsSemisimple H) (hK : IsSemisimple K) : IsSimplyConnected H := by
  refine ⟨hH, ?_⟩
  intro C f hC hf
  have hprod : IsSemisimple (C ⊗ K) := by
    apply IsSemisimple.of_isCentralIsogeny (f ⊗ₘ 𝟙 K) (hf.tensor_id K) h.isSemisimple
    · exact smooth_tensor C.X K.X hC.isConnectedReductive.smooth hK.isConnectedReductive.smooth
    · have hgeom := smoothConnectedAffineGeometry.2 k C K
        hC.isConnectedReductive.smooth hC.isConnectedReductive.isAffineHom
        hC.isConnectedReductive.connectedSpace hK.isConnectedReductive.smooth
        hK.isConnectedReductive.isAffineHom hK.isConnectedReductive.connectedSpace
      have : GeometricallyIntegral (C ⊗ K).X.hom := hgeom.2.2.2
      have : Subsingleton (Spec (CommRingCat.of k)) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have : IrreducibleSpace (C ⊗ K).X.left :=
        GeometricallyIrreducible.irreducibleSpace_of_subsingleton (C ⊗ K).X.hom
      infer_instance
  have : IsIso (f ⊗ₘ 𝟙 K) := h.central_isogeny_isIso _ _ hprod (hf.tensor_id K)
  exact isIso_of_tensor_id f K

/-- The second semisimple direct factor is simply connected as well. -/
theorem IsSimplyConnected.of_tensor_right (h : IsSimplyConnected (H ⊗ K))
    (hH : IsSemisimple H) (hK : IsSemisimple K) : IsSimplyConnected K :=
  (h.of_iso (β_ K H)).of_tensor_left hK hH

/-- An incoming semisimple central cover of the first factor of a simply
connected product gives an actual isomorphism with that factor. -/
def IsSimplyConnected.directFactorCoverIso (h : IsSimplyConnected (H ⊗ K))
    (hH : IsSemisimple H) (hK : IsSemisimple K)
    {C : GroupScheme (Spec (CommRingCat.of k))} (f : C ⟶ H)
    (hC : IsSemisimple C) (hf : IsCentralIsogeny f) : C ≅ H := by
  letI : IsIso f := (h.of_tensor_left hH hK).central_isogeny_isIso C f hC hf
  exact asIso f

/-- The constructed factor-cover isomorphism has the original covering map. -/
@[simp]
theorem IsSimplyConnected.directFactorCoverIso_hom (h : IsSimplyConnected (H ⊗ K))
    (hH : IsSemisimple H) (hK : IsSemisimple K)
    {C : GroupScheme (Spec (CommRingCat.of k))} (f : C ⟶ H)
    (hC : IsSemisimple C) (hf : IsCentralIsogeny f) :
    (h.directFactorCoverIso hH hK f hC hf).hom = f := rfl

end Field

end Langlands.GroupScheme
