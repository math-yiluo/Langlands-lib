import Langlands.GroupScheme.Unipotent.AdditiveCharacter
import Langlands.GroupScheme.DominantHomFlat
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Faithfully flat additive characters of smooth connected unipotent groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding

/-- In an augmented domain over a field, a nonzero element of the augmentation
ideal is transcendental over the field. -/
theorem transcendental_of_augmentation_eq_zero
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (ε : A →ₐ[k] k) {a : A} (ha : a ≠ 0) (hε : ε a = 0) :
    Transcendental k a := by
  intro h
  have hu := h.isIntegral.isUnit ha
  have hu' := hu.map ε
  rw [hε] at hu'
  exact not_isUnit_zero hu'

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A nonzero primitive coordinate in a domain defines a dominant map to Ga. -/
theorem isDominant_quotientMap_of_isPrimitiveElem [IsDomain B] {b : B}
    (hb : letI := bialgebra e; Bialgebra.IsPrimitiveElem k b) (hb0 : b ≠ 0) :
    IsDominant (VectorGroup.quotientMap
      (isPrimitiveFamily_of_isPrimitiveElem e hb)).hom.hom.left := by
  let := bialgebra e
  have ht : Transcendental k b :=
    transcendental_of_augmentation_eq_zero (Bialgebra.counitAlgHom k B) hb0 hb.counit_eq_zero
  have hai : AlgebraicIndependent k (fun _ : Fin 1 => b) :=
    (algebraicIndependent_singleton_iff (0 : Fin 1)).2 ht
  have hi : Function.Injective
      (MvPolynomial.aeval (fun _ : Fin 1 => b) : MvPolynomial (Fin 1) k →ₐ[k] B) := hai
  rw [VectorGroup.quotientMap_left]
  change IsDominant (Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (fun _ : Fin 1 => b) : MvPolynomial (Fin 1) k →ₐ[k] B).toRingHom))
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap
    (MvPolynomial.aeval (fun _ : Fin 1 => b) : MvPolynomial (Fin 1) k →ₐ[k] B).toRingHom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot
      (MvPolynomial.aeval (fun _ : Fin 1 => b) : MvPolynomial (Fin 1) k →ₐ[k] B).toRingHom).1 hi]
  exact bot_le

/-- A smooth connected corepresented group over a field has domain coordinates. -/
theorem isDomain_of_smooth_connected
    [Smooth (Corepresented.groupScheme F e).X.hom]
    [ConnectedSpace (Corepresented.groupScheme F e).X.left] : IsDomain B := by
  let : IsAffine (Corepresented.groupScheme F e).X.left := by
    change IsAffine (Spec (CommRingCat.of B))
    infer_instance
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : GeometricallyIntegral (Corepresented.groupScheme F e).X.hom :=
    smoothConnectedAffineGeometry.1 k (Corepresented.groupScheme F e)
      inferInstance inferInstance inferInstance
  have hi := GeometricallyIntegral.isIntegral_of_subsingleton
    (Corepresented.groupScheme F e).X.hom
  change IsIntegral (Spec (CommRingCat.of B)) at hi
  exact (affine_isIntegral_iff (CommRingCat.of B)).1 hi

/-- A nonzero primitive coordinate on a finite-type group with domain coordinates
defines an fppf quotient by its actual scheme kernel. -/
theorem isFppfQuotient_quotientMap_of_isPrimitiveElem [IsDomain B]
    [LocallyOfFiniteType (Corepresented.groupScheme F e).X.hom] {b : B}
    (hb : letI := bialgebra e; Bialgebra.IsPrimitiveElem k b) (hb0 : b ≠ 0) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι (VectorGroup.quotientMap
        (isPrimitiveFamily_of_isPrimitiveElem e hb))))
      (VectorGroup.quotientMap (isPrimitiveFamily_of_isPrimitiveElem e hb)) := by
  let q := VectorGroup.quotientMap (isPrimitiveFamily_of_isPrimitiveElem e hb)
  let : IsAffine (Corepresented.groupScheme F e).X.left := by
    change IsAffine (Spec (CommRingCat.of B))
    infer_instance
  let : IsDominant q.hom.hom.left := isDominant_quotientMap_of_isPrimitiveElem e hb hb0
  let : IsAffine (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
    infer_instance
  let : IsIntegral (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left := by
    change IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
    infer_instance
  let : IsLocallyNoetherian (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left := by
    change IsLocallyNoetherian (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
    infer_instance
  let : LocallyOfFiniteType (q.hom.hom.left ≫
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : LocallyOfFiniteType q.hom.hom.left := locallyOfFiniteType_of_comp
    q.hom.hom.left (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom
  let : Flat q.hom.hom.left := DominantHomFlat.flat_of_isDominant q
  exact ⟨inferInstance, DominantHomFlat.surjective_of_flat q, inferInstance, rfl⟩

/-- Every nontrivial smooth connected corepresented unipotent group admits an
actual represented fppf quotient to the one-dimensional additive vector group. -/
theorem exists_additive_fppf_quotient_of_isUnipotent
    [Smooth (Corepresented.groupScheme F e).X.hom]
    [ConnectedSpace (Corepresented.groupScheme F e).X.left]
    (hU : IsUnipotent (Corepresented.groupScheme F e))
    (hnt : SubgroupFunctor.range (𝟙 (Corepresented.groupScheme F e)) ≠ ⊥) :
    ∃ q : Corepresented.groupScheme F e ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
      q ≠ 0 ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q := by
  classical
  let : IsDomain B := isDomain_of_smooth_connected e
  have hconst : ∃ b : B, b ∉ k ∙ (1 : B) := by
    by_contra h
    exact hnt (range_id_eq_bot_of_all_mem_constants e (by simpa using h))
  let := bialgebra e
  obtain ⟨b, hb0, hb⟩ := exists_nonzero_primitive_of_oneMemStable
    (oneMemStable_of_isUnipotent e hU) hconst
  let hy := isPrimitiveFamily_of_isPrimitiveElem e hb
  exact ⟨VectorGroup.quotientMap hy, quotientMap_ne_zero e hy hb0,
    isFppfQuotient_quotientMap_of_isPrimitiveElem e hb hb0⟩

/-- Every nontrivial smooth connected affine unipotent group has an actual fppf
quotient to the one-dimensional additive vector group. -/
theorem exists_additive_fppf_quotient {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine U.X.left] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hnt : SubgroupFunctor.range (𝟙 U) ≠ ⊥) :
    ∃ q : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
      q ≠ 0 ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q := by
  let eU := AffineCoordinates.groupSchemeIso U
  have : IsIso eU.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map eU.hom))
  have : IsIso eU.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map eU.inv))
  let : Smooth (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)).X.hom := by
    rw [← Over.w eU.hom.hom.hom]
    infer_instance
  let : ConnectedSpace (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)).X.left :=
    Function.Surjective.connectedSpace
      (Scheme.homeoOfIso (asIso eU.inv.hom.hom.left)).surjective
      (Scheme.homeoOfIso (asIso eU.inv.hom.hom.left)).continuous
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  have hnt' : SubgroupFunctor.range
      (𝟙 (Corepresented.groupScheme (AffineCoordinates.functor U)
        (AffineCoordinates.corepresentation U))) ≠ ⊥ := by
    intro h
    apply hnt
    exact RelativeRoot.HasSplitSeries.of_iso eU (n := 0) h
  obtain ⟨q, hq0, hq⟩ := exists_additive_fppf_quotient_of_isUnipotent
    (AffineCoordinates.corepresentation U) hU' hnt'
  refine ⟨eU.inv ≫ q, ?_, ?_⟩
  · intro h0
    apply hq0
    calc q = eU.hom ≫ (eU.inv ≫ q) := by simp
         _ = 0 := by rw [h0, Limits.comp_zero]
  · obtain ⟨hf, hs, hl, -⟩ := hq.comapIso eU
    exact ⟨hf, hs, hl, rfl⟩

/-- A chosen nonzero fppf additive quotient of a nontrivial smooth connected
affine unipotent group. -/
def additiveFppfQuotient {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine U.X.left] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (hU : IsUnipotent U) (hnt : SubgroupFunctor.range (𝟙 U) ≠ ⊥) :
    {q : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1 //
      q ≠ 0 ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι q)) q} :=
  ⟨Classical.choose (exists_additive_fppf_quotient hU hnt),
    Classical.choose_spec (exists_additive_fppf_quotient hU hnt)⟩

end Langlands.GroupScheme.Unipotent
