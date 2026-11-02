import Langlands.AlgebraicGeometry.Units.FiniteAlgebraAffine
import Mathlib.Algebra.Group.Units.Equiv

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- An affine test scheme with its prescribed scalar structure. -/
def affineTest (k B : Type u) [Field k] [CommRing B] [Algebra k B] : Over (base k) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))

variable {n : ℕ} (b : Module.Basis (Fin n) k A)
  {B : Type u} [CommRing B] [Algebra k B]

/-- Spectrum sends a coefficient homomorphism to the corresponding over-morphism. -/
def affineMorphism (φ : candidateRing b →ₐ[k] B) : affineTest k B ⟶ candidate b :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (candidateRing b))) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext φ.comp_algebraMap))

/-- Morphisms of the affine test are exactly algebra homomorphisms. -/
def affineHomEquiv : (affineTest k B ⟶ candidate b) ≃ (candidateRing b →ₐ[k] B) :=
  (show (affineTest k B ⟶ candidate b) ≃
      {f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (candidateRing b)) //
        f ≫ Spec.algebraMap k (candidateRing b) = Spec.algebraMap k B} from
    { toFun := fun h => ⟨h.left, h.w⟩
      invFun := fun h => Over.homMk h.val h.property
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans Spec.homEquivAlgHom

@[simp]
lemma affineHomEquiv_affineMorphism (φ : candidateRing b →ₐ[k] B) :
    affineHomEquiv b (affineMorphism b φ) = φ := by
  apply AlgHom.ext
  intro r
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom r = φ r
  simp

lemma affineMorphism_affineHomEquiv (h : affineTest k B ⟶ candidate b) :
    affineMorphism b (affineHomEquiv b h) = h :=
  (affineHomEquiv b).injective (affineHomEquiv_affineMorphism b _)

/-- Actual global functions of the affine fibre product in tensor coordinates. -/
def affineFibreCoordinates :
    Γ((Picard.relativeSpace (algebraSchemeMap k A)).obj (affineTest k B), ⊤) ≅
      CommRingCat.of (B ⊗[k] A) :=
  (Scheme.Γ.mapIso (pullbackSpecIso k B A).op).symm ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (B ⊗[k] A))

set_option backward.isDefEq.respectTransparency false in
lemma affineFibreMap (φ : candidateRing b →ₐ[k] B) :
    (pullbackSpecIso k B A).inv ≫
        (Picard.relativeSpace (algebraSchemeMap k A)).map (affineMorphism b φ) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom) ≫
        (fibreSpecIso b).inv := by
  have hf := (Picard.relativeProjection (algebraSchemeMap k A)).naturality
    (affineMorphism b φ)
  change (Picard.relativeSpace (algebraSchemeMap k A)).map (affineMorphism b φ) ≫
    pullback.fst _ _ = pullback.fst _ _ ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) at hf
  apply pullback.hom_ext
  · simp only [Category.assoc, hf, fibreSpecIso]
    change (pullbackSpecIso k B A).inv ≫
        pullback.fst (Spec.algebraMap k B) (Spec.algebraMap k A) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom) ≫
        (pullbackSpecIso k (candidateRing b) A).inv ≫
        pullback.fst (Spec.algebraMap k (candidateRing b)) (Spec.algebraMap k A)
    rw [pullbackSpecIso_inv_fst'_assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp,
      ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext r
    rfl
  · simp only [Category.assoc, Picard.relativeSpace_map_snd, fibreSpecIso]
    change (pullbackSpecIso k B A).inv ≫
        pullback.snd (Spec.algebraMap k B) (Spec.algebraMap k A) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom) ≫
        (pullbackSpecIso k (candidateRing b) A).inv ≫
        pullback.snd (Spec.algebraMap k (candidateRing b)) (Spec.algebraMap k A)
    rw [pullbackSpecIso_inv_snd, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext r
    simp

set_option backward.isDefEq.respectTransparency false in
lemma affineFibreCoordinates_naturality (φ : candidateRing b →ₐ[k] B) :
    ((Picard.relativeSpace (algebraSchemeMap k A)).map (affineMorphism b φ)).appTop ≫
        (affineFibreCoordinates (k := k) (A := A) (B := B)).hom =
      (fibreCoordinates b).hom ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k A)).toRingHom := by
  have h := congrArg Scheme.Hom.appTop (affineFibreMap b φ)
  simp only [Scheme.Hom.comp_appTop] at h
  change ((Picard.relativeSpace (algebraSchemeMap k A)).map
      (affineMorphism b φ)).appTop ≫
      ((pullbackSpecIso k B A).inv.appTop ≫ (Scheme.ΓSpecIso _).hom) =
    ((fibreSpecIso b).inv.appTop ≫ (Scheme.ΓSpecIso _).hom) ≫ _
  rw [← Category.assoc, h, Category.assoc, Scheme.ΓSpecIso_naturality,
    Category.assoc]

/-- In affine fibre coordinates the actual pullback is the algebraic universal-unit map. -/
lemma candidateMap_affine_coordinates (φ : candidateRing b →ₐ[k] B) :
    Units.map (affineFibreCoordinates (k := k) (A := A) (B := B)).hom.hom.toMonoidHom
      (((candidateMap b).app (op (affineTest k B)) ⟨affineMorphism b φ⟩).down) =
      algebraicPoint b φ := by
  apply Units.ext
  change (((Picard.relativeSpace (algebraSchemeMap k A)).map
      (affineMorphism b φ)).appTop ≫
      (affineFibreCoordinates (k := k) (A := A) (B := B)).hom)
    (universalUnit b : Γ(candidateFibre b, ⊤)) = _
  rw [affineFibreCoordinates_naturality]
  change (Algebra.TensorProduct.map φ (AlgHom.id k A))
    ((fibreCoordinates b).hom (universalUnit b : Γ(candidateFibre b, ⊤))) = _
  rw [universalUnit_coordinates]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical candidate map is bijective on every affine algebra test. -/
lemma candidateMap_affineTest_bijective :
    Function.Bijective ((candidateMap b).app (op (affineTest k B))) := by
  let e := Units.mapEquiv
    (Iso.commRingCatIsoToRingEquiv
      (affineFibreCoordinates (k := k) (A := A) (B := B))).toMulEquiv
  have formula (h : affineTest k B ⟶ candidate b) :
      e (((candidateMap b).app (op (affineTest k B)) ⟨h⟩).down) =
        algebraicPoint b (affineHomEquiv b h) := by
    apply Units.ext
    change (affineFibreCoordinates (k := k) (A := A) (B := B)).hom
      ((((candidateMap b).app (op (affineTest k B)) ⟨h⟩).down :
        Γ((Picard.relativeSpace (algebraSchemeMap k A)).obj (affineTest k B), ⊤))) = _
    have hh := candidateMap_affine_coordinates b (affineHomEquiv b h)
    rw [affineMorphism_affineHomEquiv] at hh
    exact congrArg Units.val hh
  constructor
  · intro x y h
    apply ULift.ext
    apply (affineHomEquiv b).injective
    apply algebraicPoint_injective b
    exact (formula x.down).symm.trans
      ((congrArg (fun z => e z.down) h).trans (formula y.down))
  · intro x
    let φ := (algebraicPointEquiv b).symm (e x.down)
    refine ⟨⟨affineMorphism b φ⟩, ?_⟩
    apply ULift.ext
    apply e.injective
    rw [formula, affineHomEquiv_affineMorphism]
    exact (algebraicPointEquiv b).apply_symm_apply (e x.down)

/-- The actual comparison is bijective on any affine scheme with any map to the base. -/
lemma candidateMap_affine_bijective (T : Over (base k)) [IsAffine T.left] :
    Function.Bijective ((candidateMap b).app (op T)) := by
  let f : Spec Γ(T.left, ⊤) ⟶ base k := T.left.isoSpec.inv ≫ T.hom
  let a : k →+* Γ(T.left, ⊤) := (Spec.preimage f).hom
  let : Algebra k Γ(T.left, ⊤) := a.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k Γ(T.left, ⊤))) = f := by
    change Spec.map (Spec.preimage f) = f
    simp
  let e : T ≅ affineTest k Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    change T.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(T.left, ⊤))) = T.hom
    rw [ha]
    simp [f])
  apply (isIso_iff_bijective _).mp
  apply (NatTrans.isIso_app_iff_of_iso (candidateMap b) e.op).mp
  exact (isIso_iff_bijective _).mpr (candidateMap_affineTest_bijective b)

end Langlands.AlgebraicGeometry.FiniteAlgebraUnits
