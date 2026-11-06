import Langlands.Algebra.FiniteBialgebraHom
import Langlands.GroupScheme.HomScheme.AffineTest
import Langlands.GroupScheme.HopfBaseChange

/-! # Homomorphisms out of a finite free Hopf spectrum -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.FiniteSource

open Langlands.FiniteBialgebraHom

variable (R : Type u) [CommRing R]

/-- The relative spectrum of a commutative Hopf `R`-algebra, as a group scheme over `Spec R`. -/
abbrev hopfGroup (A : Type u) [CommRing A] [HopfAlgebra R A] :
    GroupScheme (Spec (CommRingCat.of R)) :=
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A))

/-- `Spec C` as a scheme over `Spec R`. -/
abbrev specOver (C : Type u) [CommRing C] [Algebra R C] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C)))

variable {R}

section Coordinates

variable (A : Type u) [CommRing A] [HopfAlgebra R A] (C : Type u) [CommRing C] [Algebra R C]

/-- Tensor coordinates on the base change of a Hopf spectrum to `Spec C`. -/
def tensorIso :
    pullback (hopfGroup R A).X.hom (specOver R C).hom ≅ Spec (CommRingCat.of (C ⊗[R] A)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R C A

theorem baseChangeSpecIso_hom_left :
    (HopfCoordinates.baseChangeSpecIso R C A).hom.hom.hom.left = (tensorIso A C).hom :=
  rfl

theorem baseChangeSpecIso_inv_left :
    (HopfCoordinates.baseChangeSpecIso R C A).inv.hom.hom.left = (tensorIso A C).inv :=
  rfl

@[reassoc (attr := simp)]
theorem tensorIso_inv_fst :
    (tensorIso A C).inv ≫ pullback.fst _ _ =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        A →ₐ[R] C ⊗[R] A).toRingHom) :
          Spec (CommRingCat.of (C ⊗[R] A)) ⟶ Spec (CommRingCat.of A)) := by
  simp only [tensorIso, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R C A

@[reassoc (attr := simp)]
theorem tensorIso_inv_snd :
    (tensorIso A C).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] A))) := by
  simp only [tensorIso, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd]
  exact pullbackSpecIso_inv_fst R C A

@[reassoc (attr := simp)]
theorem tensorIso_hom_includeRight :
    (tensorIso A C).hom ≫
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        A →ₐ[R] C ⊗[R] A).toRingHom) :
          Spec (CommRingCat.of (C ⊗[R] A)) ⟶ Spec (CommRingCat.of A)) =
      pullback.fst _ _ := by
  rw [← tensorIso_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem tensorIso_hom_algebraMap :
    (tensorIso A C).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] A))) =
      pullback.snd _ _ := by
  rw [← tensorIso_inv_snd, Iso.hom_inv_id_assoc]

end Coordinates

section Equiv

variable (A P : Type u) [CommRing A] [CommRing P] [HopfAlgebra R A] [HopfAlgebra R P]
  (C : Type u) [CommRing C] [Algebra R C]

/-- Homomorphisms of Hopf spectra after base change to `Spec C` are `C`-bialgebra maps of the
scalar extensions. -/
def relativeHomEquiv :
    RelativeHom (hopfGroup R P) (hopfGroup R A) (specOver R C) ≃
      (C ⊗[R] A →ₐc[C] C ⊗[R] P) :=
  ((HopfCoordinates.baseChangeSpecIso R C P).homCongr
      (HopfCoordinates.baseChangeSpecIso R C A)).trans <|
    (hopfSpec.fullyFaithful.homEquiv).symm.trans <| (opEquiv _ _).trans
      { toFun := fun f => f.hom
        invFun := CommHopfAlgCat.ofHom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

variable {A P C}

theorem relativeHomEquiv_symm_fst (φ : C ⊗[R] A →ₐc[C] C ⊗[R] P) :
    ((relativeHomEquiv A P C).symm φ).hom.hom.left ≫ pullback.fst _ _ =
      (tensorIso P C).hom ≫ Spec.map (CommRingCat.ofHom
        ((φ : C ⊗[R] A →ₐ[C] C ⊗[R] P).restrictScalars R |>.comp
          Algebra.TensorProduct.includeRight).toRingHom) := by
  have h : ((relativeHomEquiv A P C).symm φ).hom.hom.left =
      (tensorIso P C).hom ≫
        Spec.map (CommRingCat.ofHom (φ : C ⊗[R] A →ₐ[C] C ⊗[R] P).toRingHom) ≫
          (tensorIso A C).inv :=
    rfl
  rw [h, Category.assoc, Category.assoc, tensorIso_inv_fst, ← Spec.map_comp]
  rfl

end Equiv

section Points

variable {A P : Type u} [CommRing A] [CommRing P] [HopfAlgebra R A] [HopfAlgebra R P]

variable (A P) in
/-- Homomorphisms of Hopf spectra after base change to `Spec C` are Hopf points
`A → C ⊗[R] P`. -/
def pointEquiv (C : Type u) [CommRing C] [Algebra R C] :
    RelativeHom (hopfGroup R P) (hopfGroup R A) (specOver R C) ≃
      {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f} :=
  (relativeHomEquiv A P C).trans (bialgHomEquiv R)

theorem pointEquiv_symm_fst {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}) :
    ((pointEquiv A P C).symm f).hom.hom.left ≫ pullback.fst _ _ =
      (tensorIso P C).hom ≫ Spec.map (CommRingCat.ofHom f.1.toRingHom) := by
  have h : ((((bialgHomEquiv R).symm f : C ⊗[R] A →ₐc[C] C ⊗[R] P) :
      C ⊗[R] A →ₐ[C] C ⊗[R] P).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      f.1 :=
    congrArg Subtype.val ((bialgHomEquiv R).apply_symm_apply f)
  rw [pointEquiv, Equiv.symm_trans_apply, relativeHomEquiv_symm_fst, h]

/-- The morphism `Spec D ⟶ Spec C` over `Spec R` induced by an `R`-algebra map `C → D`. -/
def specMap {C D : Type u} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (g : C →ₐ[R] D) : specOver R D ⟶ specOver R C :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    simp only [specOver, Over.mk_hom]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem baseChangeProj_specMap {C D : Type u} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (g : C →ₐ[R] D) :
    baseChangeProj (hopfGroup R P) (specMap g) =
      (tensorIso P D).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map g (AlgHom.id R P)).toRingHom) ≫ (tensorIso P C).inv := by
  apply pullback.hom_ext
  · rw [baseChangeProj_fst, Category.assoc, Category.assoc, tensorIso_inv_fst, ← Spec.map_comp,
      ← tensorIso_hom_includeRight P D]
    congr 2
    ext x
    simp
  · rw [baseChangeProj_snd, Category.assoc, Category.assoc, tensorIso_inv_snd, ← Spec.map_comp,
      ← tensorIso_hom_algebraMap P D, Category.assoc]
    change _ ≫ Spec.map _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom) = _
    rw [← Spec.map_comp]
    congr 2

/-- Evaluation along `Spec D ⟶ Spec C` pushes Hopf points forward. -/
theorem evaluate_specMap {C D : Type u} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (g : C →ₐ[R] D) (f : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f}) :
    evaluate (specMap g) ((pointEquiv A P C).symm f) =
      (pointEquiv A P D).symm ⟨pushPoint R g f.1, f.2.pushPoint R g⟩ := by
  apply relativeHom_ext
  rw [evaluate_fst, pointEquiv_symm_fst, pointEquiv_symm_fst, baseChangeProj_specMap,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  rfl

/-- Morphisms of affine spectra over `Spec R` are `R`-algebra maps. -/
def specOverHomEquiv {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] :
    (specOver R C ⟶ specOver R B) ≃ (B →ₐ[R] C) where
  toFun a :=
    { toRingHom := (Spec.preimage a.left).hom
      commutes' := fun r => by
        have h : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage a.left) =
            Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
          rw [Spec.map_comp, Spec.map_preimage]
          exact Over.w a
        exact congrArg (fun φ : CommRingCat.of R ⟶ CommRingCat.of C => φ.hom r)
          (Spec.map_injective h) }
  invFun := specMap
  left_inv a := Over.OverMorphism.ext (Spec.map_preimage a.left)
  right_inv g := by
    ext x
    show (Spec.preimage (Spec.map (CommRingCat.ofHom g.toRingHom))).hom x = g x
    rw [Spec.preimage_map]
    rfl

end Points

section Universal

variable (R) (A P : Type u) [CommRing A] [CommRing P] [HopfAlgebra R A] [HopfAlgebra R P]
  [Module.Finite R P] [Module.Free R P] [Algebra.FinitePresentation R A]

/-- The universal family of homomorphisms from the spectrum of `P` to the spectrum of `A`,
over the spectrum of `HomAlgebra R A P`. -/
def universalFamily :
    RelativeHom (hopfGroup R P) (hopfGroup R A) (specOver R (HomAlgebra R A P)) :=
  (pointEquiv A P _).symm ⟨universalPoint R A P, isHopfPoint_universalPoint R A P⟩

theorem bijective_evaluate_universalFamily_specOver (C : Type u) [CommRing C] [Algebra R C] :
    Function.Bijective (fun a : specOver R C ⟶ specOver R (HomAlgebra R A P) =>
      evaluate a (universalFamily R A P)) := by
  have h : (fun a : specOver R C ⟶ specOver R (HomAlgebra R A P) =>
      evaluate a (universalFamily R A P)) =
      (pointEquiv A P C).symm ∘ homEquiv R A P C ∘ specOverHomEquiv := by
    funext a
    simp only [Function.comp_apply]
    conv_lhs => rw [← specOverHomEquiv.symm_apply_apply a]
    exact evaluate_specMap _ _
  rw [h]
  exact (pointEquiv A P C).symm.bijective.comp
    ((homEquiv R A P C).bijective.comp specOverHomEquiv.bijective)

/-- The family over `Spec (HomAlgebra R A P)` is universal. -/
theorem isUniversal_universalFamily : IsUniversal (universalFamily R A P) := by
  refine isUniversal_of_affine _ fun T hT => ?_
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) :=
    Spec.preimage (T.left.isoSpec.inv ≫ T.hom : Spec Γ(T.left, ⊤) ⟶ Spec (CommRingCat.of R))
  let : Algebra R Γ(T.left, ⊤) := ψ.hom.toAlgebra
  let e : T ≅ specOver R Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.hom) = T.hom
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, Iso.hom_inv_id_assoc])
  exact bijective_evaluate_of_iso _ e (bijective_evaluate_universalFamily_specOver R A P _)

end Universal

end Langlands.GroupScheme.HomScheme.FiniteSource
