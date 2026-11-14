import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianColengthOnePullback
import Langlands.AlgebraicGeometry.Picard.FlatPicardInfinitesimalGluing
import Langlands.AlgebraicGeometry.Picard.TwoAxisValuationClassSurjectivity
import Langlands.AlgebraicGeometry.Picard.TwoAxisBundleNormalization

/-! # Murre's condition (F4′) for the two-axis class presheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AbelianScheme

namespace TwoAxisRigidifiedLineBundle

open TwoAxisFamily

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S) (T : Over S)

/-- The comparison from the self-product over the composite test object `U → T.left → S`
to the base change along `U → T.left` of the self-product over `T`. -/
def selfProductComparison (U : Over T.left) :
    (mumfordProduct (abelian A (Over.mk (U.hom ≫ T.hom)))).left ⟶
      Limits.pullback U.hom (mumfordProduct (abelian A T)).hom :=
  pullback.lift (mumfordProduct (abelian A (Over.mk (U.hom ≫ T.hom)))).hom
    (productMap A (compTestHom U.hom)) (by
      change (pullback.fst _ _ ≫ (abelian A (Over.mk (U.hom ≫ T.hom))).X.hom) ≫ U.hom =
        productMap A (compTestHom U.hom) ≫ (pullback.fst _ _ ≫ (abelian A T).X.hom)
      rw [productMap_fst_assoc, carrierMap_snd, Category.assoc]
      rfl)

@[reassoc (attr := simp)]
lemma selfProductComparison_fst (U : Over T.left) :
    selfProductComparison A T U ≫ pullback.fst U.hom (mumfordProduct (abelian A T)).hom =
      (mumfordProduct (abelian A (Over.mk (U.hom ≫ T.hom)))).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma selfProductComparison_snd (U : Over T.left) :
    selfProductComparison A T U ≫ pullback.snd U.hom (mumfordProduct (abelian A T)).hom =
      productMap A (compTestHom U.hom) :=
  pullback.lift_snd _ _ _

lemma selfProductComparison_eq (U : Over T.left) :
    selfProductComparison A T U = compProductHom A U.hom ≫
      (mumfordProductBaseChangeIso (abelian A T) U.hom).hom ≫
        (pullbackSymmetry (mumfordProduct (abelian A T)).hom U.hom).hom := by
  have hs : (mumfordProductBaseChangeIso (abelian A T) U.hom).hom ≫
      pullback.snd (mumfordProduct (abelian A T)).hom U.hom =
        pullback.fst ((baseChange U.hom).obj (abelian A T)).X.hom
          ((baseChange U.hom).obj (abelian A T)).X.hom ≫
            ((baseChange U.hom).obj (abelian A T)).X.hom :=
    selfProductBaseChangeIso_hom_snd _ _
  have hf : (mumfordProductBaseChangeIso (abelian A T) U.hom).hom ≫
      pullback.fst (mumfordProduct (abelian A T)).hom U.hom =
        mumfordProductBaseChangeMap (abelian A T) U.hom :=
    mumfordProductBaseChangeIso_hom_fst _ _
  have key : compProductHom A U.hom ≫
      pullback.fst ((baseChange U.hom).obj (abelian A T)).X.hom
        ((baseChange U.hom).obj (abelian A T)).X.hom ≫
          ((baseChange U.hom).obj (abelian A T)).X.hom =
      pullback.fst (abelian A (Over.mk (U.hom ≫ T.hom))).X.hom
        (abelian A (Over.mk (U.hom ≫ T.hom))).X.hom ≫
          (abelian A (Over.mk (U.hom ≫ T.hom))).X.hom := by
    simp only [compProductHom, cartesianMumfordProductMap, cartesianSelfProductMap_fst_assoc,
      compCarrierIso_hom_snd]
  apply pullback.hom_ext
  · rw [selfProductComparison_fst, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_fst, hs]
    exact key.symm
  · rw [selfProductComparison_snd, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_snd, hf, compProductHom_baseChangeMap]

instance (U : Over T.left) : IsIso (selfProductComparison A T U) := by
  rw [selfProductComparison_eq]
  have : IsIso (compProductHom A U.hom) :=
    ⟨compProductInv A U.hom, compProductHom_inv A U.hom, compProductInv_hom A U.hom⟩
  infer_instance

/-- The comparison commutes with the maps induced by a morphism of test objects. -/
lemma selfProductComparison_naturality {U U' : Over T.left} (w : U ⟶ U')
    (v : Over.mk (U.hom ≫ T.hom) ⟶ Over.mk (U'.hom ≫ T.hom)) (hv : v.left = w.left) :
    selfProductComparison A T U ≫ (relativeSpace (mumfordProduct (abelian A T)).hom).map w =
      productMap A v ≫ selfProductComparison A T U' := by
  apply pullback.hom_ext
  · have h₁ : (relativeSpace (mumfordProduct (abelian A T)).hom).map w ≫
        pullback.fst U'.hom (mumfordProduct (abelian A T)).hom =
          pullback.fst U.hom (mumfordProduct (abelian A T)).hom ≫ w.left :=
      pullback.lift_fst _ _ _
    rw [Category.assoc, Category.assoc, h₁, selfProductComparison_fst_assoc,
      selfProductComparison_fst, ← hv]
    change (pullback.fst _ _ ≫ (abelian A (Over.mk (U.hom ≫ T.hom))).X.hom) ≫ v.left =
      productMap A v ≫ (pullback.fst _ _ ≫ (abelian A (Over.mk (U'.hom ≫ T.hom))).X.hom)
    rw [productMap_fst_assoc, carrierMap_snd, Category.assoc]
  · rw [Category.assoc, Category.assoc, relativeSpace_map_snd, selfProductComparison_snd,
      selfProductComparison_snd, ← productMap_comp]
    congr 1
    apply Over.OverMorphism.ext
    change U.hom = v.left ≫ U'.hom
    rw [hv, Over.w w]

lemma productMap_hom {T U : Over S} (h : T ⟶ U) :
    productMap A h ≫ (mumfordProduct (abelian A U)).hom =
      (mumfordProduct (abelian A T)).hom ≫ h.left := by
  change productMap A h ≫ (Limits.pullback.fst _ _ ≫ (abelian A U).X.hom) =
    (Limits.pullback.fst _ _ ≫ (abelian A T).X.hom) ≫ h.left
  rw [productMap_fst_assoc, carrierMap_snd, Category.assoc]

section ArtinianLifting

open UnramifiedFunctor

variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

/-- The structure map to `Spec Λ` of the self-product over the test object `f`. -/
abbrev productStructure :
    (mumfordProduct (abelian A (Over.mk f))).left ⟶ Spec (CommRingCat.of Λ) :=
  (mumfordProduct (abelian A (Over.mk f))).hom

instance : Flat (productStructure A f) := by
  have : Smooth (productStructure A f) := by
    change Smooth (Limits.pullback.fst (abelian A (Over.mk f)).X.hom
      (abelian A (Over.mk f)).X.hom ≫ (abelian A (Over.mk f)).X.hom)
    infer_instance
  infer_instance

/-- The self-product comparison at the affine test object `Spec B ⟶ Spec Λ`. -/
abbrev affineComparison (B : Type u) [CommRing B] [Algebra Λ B] :
    (mumfordProduct (abelian A (algebraOver f B))).left ⟶
      (relativeSpace (productStructure A f)).obj (affineBase Λ B) :=
  selfProductComparison A (Over.mk f) (affineBase Λ B)

instance (B : Type u) [CommRing B] [Algebra Λ B] : IsIso (affineComparison A f B) :=
  inferInstanceAs (IsIso (selfProductComparison A (Over.mk f) (affineBase Λ B)))

@[reassoc]
lemma affineComparison_fst (B : Type u) [CommRing B] [Algebra Λ B] :
    affineComparison A f B ≫
      Limits.pullback.fst (affineBase Λ B).hom (productStructure A f) =
        (mumfordProduct (abelian A (algebraOver f B))).hom :=
  selfProductComparison_fst A (Over.mk f) (affineBase Λ B)

@[reassoc]
lemma affineComparison_snd (B : Type u) [CommRing B] [Algebra Λ B] :
    affineComparison A f B ≫
      Limits.pullback.snd (affineBase Λ B).hom (productStructure A f) =
        productMap A (algebraOverBase f B) :=
  selfProductComparison_snd A (Over.mk f) (affineBase Λ B)

lemma affineComparison_naturality {B B' : Type u} [CommRing B] [Algebra Λ B]
    [CommRing B'] [Algebra Λ B'] (φ : B →ₐ[Λ] B') :
    affineComparison A f B' ≫ (relativeSpace (productStructure A f)).map (affineBaseMap φ) =
      productMap A (algHomOver f φ) ≫ affineComparison A f B :=
  selfProductComparison_naturality A (Over.mk f) (affineBaseMap φ) (algHomOver f φ) rfl

lemma inv_affineComparison_naturality {B B' : Type u} [CommRing B] [Algebra Λ B]
    [CommRing B'] [Algebra Λ B'] (φ : B →ₐ[Λ] B') :
    (relativeSpace (productStructure A f)).map (affineBaseMap φ) ≫
        inv (affineComparison A f B) =
      inv (affineComparison A f B') ≫ productMap A (algHomOver f φ) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, affineComparison_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The self-product over `f` maps to the base change of itself along the identity
`Spec Λ ⟶ Spec Λ` of `Λ`-algebras. -/
def unitBaseSection :
    (mumfordProduct (abelian A (Over.mk f))).left ⟶
      (relativeSpace (productStructure A f)).obj (affineBase Λ Λ) :=
  Limits.pullback.lift (productStructure A f) (𝟙 _) (by
    change productStructure A f ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ Λ)) =
      𝟙 _ ≫ productStructure A f
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id,
      Category.id_comp])

lemma productMap_unitBaseSection (B : Type u) [CommRing B] [Algebra Λ B] :
    productMap A (algebraOverBase f B) ≫ unitBaseSection A f =
      affineComparison A f B ≫
        (relativeSpace (productStructure A f)).map (affineBaseMap (Algebra.ofId Λ B)) := by
  apply Limits.pullback.hom_ext
  · have h₁ : (relativeSpace (productStructure A f)).map (affineBaseMap (Algebra.ofId Λ B)) ≫
        Limits.pullback.fst (affineBase Λ Λ).hom (productStructure A f) =
          Limits.pullback.fst (affineBase Λ B).hom (productStructure A f) ≫
            (affineBaseMap (Algebra.ofId Λ B)).left :=
      Limits.pullback.lift_fst _ _ _
    have h₂ : unitBaseSection A f ≫
        Limits.pullback.fst (affineBase Λ Λ).hom (productStructure A f) =
          productStructure A f :=
      Limits.pullback.lift_fst _ _ _
    rw [Category.assoc, Category.assoc, h₁, h₂, affineComparison_fst_assoc]
    exact productMap_hom A (algebraOverBase f B)
  · have h₂ : unitBaseSection A f ≫
        Limits.pullback.snd (affineBase Λ Λ).hom (productStructure A f) = 𝟙 _ :=
      Limits.pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, relativeSpace_map_snd, h₂, Category.comp_id,
      affineComparison_snd]

local notation "𝕜" => IsLocalRing.ResidueField Λ

variable [IsLocalRing Λ] [IsArtinianRing Λ]

/-- Gluing step of (F4′): a line bundle `D` on the self-product over the residue field and a
line bundle `L` on the self-product over `A'` that agree over `A' ⊗[Λ] k` come from one line
bundle on the self-product over `Λ`, whose restriction to the residue field is `D`. -/
theorem exists_extension {A' : Type u} [CommRing A'] [Algebra Λ A']
    (hinj : Function.Injective (algebraMap Λ A'))
    (hlen : Module.length Λ (A' ⧸ LinearMap.range (Algebra.linearMap Λ A')) = 1)
    (D : LineBundle (mumfordProduct (abelian A (algebraOver f 𝕜))).left)
    (L : LineBundle (mumfordProduct (abelian A (algebraOver f A'))).left)
    (φ : (LineBundle.pullback (productMap A (algHomOver f
        (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜)))).obj L ≅
      (LineBundle.pullback (productMap A (algHomOver f
        (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)))).obj D) :
    ∃ E : LineBundle (mumfordProduct (abelian A (Over.mk f))).left,
      Nonempty ((LineBundle.pullback (productMap A (algebraOverBase f 𝕜))).obj E ≅ D) := by
  have hsq := ArtinianColengthOne.isPullback hinj hlen
  have := FlatInfinitesimalGluing.affineSquareComparison_isEquivalence (productStructure A f)
    (Algebra.ofId Λ 𝕜) (Algebra.ofId Λ A')
    (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)
    (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜) hsq
    (ArtinianColengthOne.includeLeft_surjective Λ A')
    (ArtinianColengthOne.isNilpotent_ker_includeLeft Λ A')
  let e : (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)))).obj
        ((LineBundle.pullback (inv (affineComparison A f 𝕜))).obj D) ≅
      (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜)))).obj
        ((LineBundle.pullback (inv (affineComparison A f A'))).obj L) :=
    LineBundle.pullbackCompEqIso ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)))
      (inv (affineComparison A f 𝕜)) (inv_affineComparison_naturality A f _) D ≪≫
    (LineBundle.pullbackCompEqIso (inv (affineComparison A f (A' ⊗[Λ] 𝕜)))
      (productMap A (algHomOver f
        (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜))) rfl D).symm ≪≫
    (LineBundle.pullback (inv (affineComparison A f (A' ⊗[Λ] 𝕜)))).mapIso φ.symm ≪≫
    LineBundle.pullbackCompEqIso (inv (affineComparison A f (A' ⊗[Λ] 𝕜)))
      (productMap A (algHomOver f
        (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜))) rfl L ≪≫
    (LineBundle.pullbackCompEqIso ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜)))
      (inv (affineComparison A f A')) (inv_affineComparison_naturality A f _) L).symm
  let Dat : PicardGroupoid.SquareGluingData
      ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)))
      ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜))) :=
    { left := ⟨(LineBundle.pullback (inv (affineComparison A f 𝕜))).obj D⟩
      right := ⟨(LineBundle.pullback (inv (affineComparison A f A'))).obj L⟩
      hom := ⟨e⟩ }
  obtain ⟨Z, ⟨eZ⟩⟩ := Functor.EssSurj.mem_essImage
    (PicardGroupoid.affineSquareComparison (productStructure A f)
      (Algebra.ofId Λ 𝕜) (Algebra.ofId Λ A')
      (Algebra.TensorProduct.includeRight : 𝕜 →ₐ[Λ] A' ⊗[Λ] 𝕜)
      (Algebra.TensorProduct.includeLeft : A' →ₐ[Λ] A' ⊗[Λ] 𝕜) hsq) Dat
  let eZl : (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap (Algebra.ofId Λ 𝕜)))).obj Z.of ≅
      (LineBundle.pullback (inv (affineComparison A f 𝕜))).obj D :=
    eZ.hom.left.iso
  refine ⟨(LineBundle.pullback (unitBaseSection A f)).obj Z.of, ⟨?_⟩⟩
  exact LineBundle.pullbackCompEqIso (productMap A (algebraOverBase f 𝕜)) (unitBaseSection A f)
      (productMap_unitBaseSection A f 𝕜) Z.of ≪≫
    (LineBundle.pullbackCompEqIso (affineComparison A f 𝕜)
      ((relativeSpace (productStructure A f)).map (affineBaseMap (Algebra.ofId Λ 𝕜)))
      rfl Z.of).symm ≪≫
    (LineBundle.pullback (affineComparison A f 𝕜)).mapIso eZl ≪≫
    LineBundle.pullbackCompEqIso (affineComparison A f 𝕜) (inv (affineComparison A f 𝕜))
      (IsIso.hom_inv_id _) D ≪≫
    (LineBundle.pullbackId _).app D

end ArtinianLifting

open UnramifiedFunctor in
/-- Murre's condition (F4′) for the two-axis class presheaf of an abelian scheme. -/
theorem classPresheaf_artinianLifting : ArtinianLifting (classPresheaf A) := by
  intro Λ _ _ _ f A' _ _ hinj hlen ξ₀ ξ' hξ
  induction ξ₀ using Quotient.inductionOn with
  | h D₀ =>
  induction ξ' using Quotient.inductionOn with
  | h L' =>
  have hξ' : (Quotient.mk _ ((relativePullback A (algHomOver f
        (Algebra.TensorProduct.includeLeft :
          A' →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ))).obj L') :
        Classes A (algebraOver f (A' ⊗[Λ] IsLocalRing.ResidueField Λ))) =
      Quotient.mk _ ((relativePullback A (algHomOver f
        (Algebra.TensorProduct.includeRight :
          IsLocalRing.ResidueField Λ →ₐ[Λ] A' ⊗[Λ] IsLocalRing.ResidueField Λ))).obj D₀) :=
    hξ
  obtain ⟨φ⟩ := Quotient.exact hξ'
  obtain ⟨E₀, ⟨e₀⟩⟩ := exists_extension A f hinj hlen
    ⟨D₀.obj.carrier, D₀.property⟩ ⟨L'.obj.carrier, L'.property⟩
    ((forget _ _ _ _ _).mapIso φ)
  let ρ := LineBundle.twoAxisNormalizedBundleRigidification pullbackTensorComparisonIsIso
    (abelian A (Over.mk f)) E₀
  let eN := LineBundle.twoAxisNormalizedBundleRestrictionIso pullbackTensorComparisonIsIso
    (abelian A (Over.mk f)) (abelian A (algebraOver f (IsLocalRing.ResidueField Λ)))
    (productMap A (algebraOverBase f (IsLocalRing.ResidueField Λ)))
    (carrierMap A (algebraOverBase f (IsLocalRing.ResidueField Λ)))
    (productMap_fst A _) (productMap_snd A _) (first_naturality A _) (second_naturality A _)
    E₀ ⟨D₀.obj.carrier, D₀.property⟩ ((LineBundle.forget _).mapIso e₀)
    D₀.obj.rigidification.first.symm D₀.obj.rigidification.second.symm
  refine ⟨Quotient.mk _ (ofLineBundle _ ρ), ?_⟩
  change (Quotient.mk _ ((relativePullback A
      (algebraOverBase f (IsLocalRing.ResidueField Λ))).obj (ofLineBundle _ ρ)) :
      Classes A (algebraOver f (IsLocalRing.ResidueField Λ))) = Quotient.mk _ D₀
  exact Quotient.sound (nonempty_iso_of_carrierIso
    (abelian A (algebraOver f (IsLocalRing.ResidueField Λ))) eN)

end TwoAxisRigidifiedLineBundle

/-- Murre's condition (F4′) holds for the two-axis class presheaf of every abelian scheme
over the spectrum of a noetherian ring. -/
theorem noetherianTwoAxisClassArtinianLifting :
    NoetherianTwoAxisClassArtinianLiftingStatement.{u} :=
  fun _ _ _ A ↦ TwoAxisRigidifiedLineBundle.classPresheaf_artinianLifting A

end Langlands.AlgebraicGeometry.Picard
