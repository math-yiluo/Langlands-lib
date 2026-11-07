import Langlands.GroupScheme.Rational.OrbitProductPullback
import Langlands.GroupScheme.Descent.RadicalTensorIdeal
import Langlands.GroupScheme.Descent.GaloisIdealSheafDescent
import Langlands.GroupScheme.Lie.BaseChange

/-! # Scheme-theoretic image ideals of actual orbit products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrbitProductImageDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (I : Type u)
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "A" => CocharacterDatum.coordAlgebra G
local notation "R" => MvPolynomial I K
local notation "GK" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance : IsAffine (pullback G.X.hom (algebraBaseMap k K)) := by
  infer_instance

local instance : IsAffine (GK).X.left := by
  change IsAffine (pullback G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The actual morphism over the extension field, expressed in tensor coordinates. -/
def morphism (x : Lie.AffinePoints G R) :
    Spec (CommRingCat.of R) ⟶ (GK).X.left :=
  Spec.map (CommRingCat.ofHom
    (OrbitProductPullback.pullbackK k K I G x).toRingHom) ≫
      (Descent.TensorCoordinates.baseChangeIso k K A G.X
        (CocharacterDatum.coordIso G)).hom

/-- Projection to the original group recovers the supplied actual point. -/
theorem morphism_fst (x : Lie.AffinePoints G R) :
    morphism k K I G x ≫ pullback.fst G.X.hom (algebraBaseMap k K) = x.left := by
  rw [morphism, Category.assoc, Descent.TensorCoordinates.baseChangeIso_hom_fst,
    ← Spec.map_comp_assoc]
  have h :
      (OrbitProductPullback.pullbackK k K I G x).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom =
      (CocharacterDatum.coord x).hom.toRingHom := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply]
  change Spec.map (CommRingCat.ofHom
    ((OrbitProductPullback.pullbackK k K I G x).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom)) ≫
      (CocharacterDatum.coordIso G).hom.left = x.left
  rw [show (OrbitProductPullback.pullbackK k K I G x).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom =
        (CocharacterDatum.coord x).hom.toRingHom from h]
  exact congrArg (fun f => f.left) (CocharacterDatum.map_coord x)

/-- The tensor-coordinate expression is a morphism over the extension field. -/
theorem morphism_snd (x : Lie.AffinePoints G R) :
    morphism k K I G x ≫ pullback.snd G.X.hom (algebraBaseMap k K) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  rw [morphism, Category.assoc, Descent.TensorCoordinates.baseChangeIso_hom_snd,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (OrbitProductPullback.pullbackK k K I G x).commutes c

/-- View the same actual morphism as a point of the base-changed group. -/
def point (x : Lie.AffinePoints G R) : Lie.AffinePoints GK R :=
  Over.homMk (morphism k K I G x) (morphism_snd k K I G x)

/-- This is precisely the usual equivalence on actual base-changed affine points. -/
theorem affineBaseChangeEquiv_point (x : Lie.AffinePoints G R) :
    Lie.affineBaseChangeEquiv k K G R (point k K I G x) = x := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left]
  exact morphism_fst k K I G x

/-- The actual global-section pullback is the polynomial pullback followed by
the spectrum/global-section identification. -/
theorem appTop_comp_sectionsEquiv (x : Lie.AffinePoints G R) :
    (morphism k K I G x).appTop.hom.comp
        (Descent.TensorCoordinates.sectionsEquiv k K A G.X
          (CocharacterDatum.coordIso G)).toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
        (OrbitProductPullback.pullback k K I G x).toRingHom := by
  have h : morphism k K I G x ≫
      (Descent.TensorCoordinates.baseChangeIso k K A G.X
        (CocharacterDatum.coordIso G)).inv =
      Spec.map (CommRingCat.ofHom
        (OrbitProductPullback.pullbackK k K I G x).toRingHom) := by
    simp [morphism]
  have ht := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at ht
  change (((Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A))).inv ≫
      (Descent.TensorCoordinates.baseChangeIso k K A G.X
        (CocharacterDatum.coordIso G)).inv.appTop) ≫
      (morphism k K I G x).appTop).hom =
    (CommRingCat.ofHom (OrbitProductPullback.pullback k K I G x).toRingHom ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom
  rw [Category.assoc, ht, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The full scheme-theoretic image ideal, in actual tensor coordinates, is
the kernel already controlled by polynomial equivariance. -/
theorem ideal_top_comap_sectionsEquiv (x : Lie.AffinePoints G R) :
    ((morphism k K I G x).ker.ideal
      ⟨⊤, isAffineOpen_top (GK).X.left⟩).comap
        (Descent.TensorCoordinates.sectionsEquiv k K A G.X
          (CocharacterDatum.coordIso G)).toRingHom =
      RingHom.ker (OrbitProductPullback.pullback k K I G x).toRingHom := by
  trans RingHom.ker ((morphism k K I G x).appTop.hom.comp
    (Descent.TensorCoordinates.sectionsEquiv k K A G.X
      (CocharacterDatum.coordIso G)).toRingHom)
  · simp [Scheme.ker_of_isAffine, RingHom.comap_ker]
  · rw [appTop_comp_sectionsEquiv]
    exact RingHom.ker_comp_of_injective
      (OrbitProductPullback.pullback k K I G x).toRingHom
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1

/-- Fixedness of the actual point makes its full image ideal stable under
coefficient conjugation in the actual tensor-coordinate presentation. -/
theorem coefficientConjugate_mem
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (x : Lie.AffinePoints G R)
    (hx : ∀ σ : K ≃ₐ[k] K,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) x = x)
    (σ : K ≃ₐ[k] K) (z : K ⊗[k] A)
    (hz : z ∈ ((morphism k K I G x).ker.ideal
      ⟨⊤, isAffineOpen_top (GK).X.left⟩).comap
        (Descent.TensorCoordinates.sectionsEquiv k K A G.X
          (CocharacterDatum.coordIso G)).toRingHom) :
    TensorGaloisPoint.coefficientConjugate k K A σ z ∈
      ((morphism k K I G x).ker.ideal
        ⟨⊤, isAffineOpen_top (GK).X.left⟩).comap
          (Descent.TensorCoordinates.sectionsEquiv k K A G.X
            (CocharacterDatum.coordIso G)).toRingHom := by
  rw [ideal_top_comap_sectionsEquiv] at hz ⊢
  exact PolynomialGalois.coefficientConjugate_mem_ker k K I A ρ
    (OrbitProductPullback.pullback k K I G x)
    (OrbitProductPullback.pullback_equivariant k K I G ρ x hx) σ z hz

/-- Over any Galois extension, the full image ideal of a fixed actual point
descends to an ideal sheaf on the original affine group scheme. -/
def definingIdealDescent [IsGalois k K]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (x : Lie.AffinePoints G R)
    (hx : ∀ σ : K ≃ₐ[k] K,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) x = x) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (morphism k K I G x).ker :=
  AffineIdealDescent.ofGaloisStableTensorIdeal k K A
    (pullback.fst G.X.hom (algebraBaseMap k K)) (morphism k K I G x).ker
    (Descent.TensorCoordinates.groundSectionsEquiv k A G.X
      (CocharacterDatum.coordIso G))
    (Descent.TensorCoordinates.sectionsEquiv k K A G.X
      (CocharacterDatum.coordIso G))
    (Descent.TensorCoordinates.projection_comp_groundSectionsEquiv k K A G.X
      (CocharacterDatum.coordIso G))
    (coefficientConjugate_mem k K I G ρ x hx)

/-- Apply full defining-ideal descent to the actual ordered block product.
The supplied factors must still satisfy transport and commutation. -/
def blockProductDefiningIdealDescent [IsGalois k K]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I)
    (blocks : List (List I)) (f : I → Lie.AffinePoints G R)
    (hblocks : ∀ (σ : K ≃ₐ[k] K) l, l ∈ blocks → (l.map (ρ σ)).Perm l)
    (hcomm : ∀ l, l ∈ blocks → (l.map f).Pairwise Commute)
    (hf : ∀ (σ : K ≃ₐ[k] K) i,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ) (f i) =
        f (ρ σ i)) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (morphism k K I G (OrbitProductPullback.blockProduct k K I G blocks f)).ker :=
  definingIdealDescent k K I G ρ
    (OrbitProductPullback.blockProduct k K I G blocks f)
    (OrbitProductPullback.blockProduct_fixed k K I G ρ blocks f hblocks hcomm hf)

end Langlands.GroupScheme.OrbitProductImageDescent
