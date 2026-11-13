import Langlands.Geometry.FormalGroup.Tangent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Distinct tangent characters at geometric points -/

noncomputable section

universe u v w z q r

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {A : Type v} [Ring A] [Algebra O A]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {K : Type q} [CommRing K]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace Hom

/-- Differentiate an actual formal map after mapping its coefficients to a fibre. -/
def fiberTangent (f : Hom M N) (φ : R →+* K) : (σ → K) →ₗ[K] (τ → K) :=
  (f.toHom.map φ).tangent

@[simp]
theorem fiberTangent_id (φ : R →+* K) : (id M).fiberTangent φ = LinearMap.id := by
  change ((CommLaw.Hom.id M.groupLaw).map φ).tangent = _
  rw [CommLaw.Hom.map_id, CommLaw.Hom.tangent_id]

@[simp]
theorem fiberTangent_zero (φ : R →+* K) : (0 : Hom M N).fiberTangent φ = 0 := by
  change ((0 : CommLaw.Hom M.groupLaw N.groupLaw).map φ).tangent = _
  rw [CommLaw.Hom.map_zero, CommLaw.Hom.tangent_zero]

@[simp]
theorem fiberTangent_add (f g : Hom M N) (φ : R →+* K) :
    (f + g).fiberTangent φ = f.fiberTangent φ + g.fiberTangent φ := by
  change ((f.toHom + g.toHom).map φ).tangent = _
  rw [CommLaw.Hom.map_add_hom, CommLaw.Hom.tangent_add]
  rfl

@[simp]
theorem fiberTangent_comp (g : Hom N P) (f : Hom M N) (φ : R →+* K) :
    (g.comp f).fiberTangent φ = (g.fiberTangent φ).comp (f.fiberTangent φ) := by
  change ((g.toHom.comp f.toHom).map φ).tangent = _
  rw [CommLaw.Hom.map_comp, CommLaw.Hom.tangent_comp]
  rfl

end Hom

namespace Iso

/-- The derivative on a fibre of a formal O-module isomorphism is invertible. -/
def fiberTangent (f : Iso M N) (φ : R →+* K) : (σ → K) ≃ₗ[K] (τ → K) where
  toLinearMap := f.hom.fiberTangent φ
  invFun := f.inv.fiberTangent φ
  left_inv x := by
    change ((f.inv.fiberTangent φ).comp (f.hom.fiberTangent φ)) x = x
    rw [← Hom.fiberTangent_comp, f.inv_hom, Hom.fiberTangent_id, LinearMap.id_apply]
  right_inv x := by
    change ((f.hom.fiberTangent φ).comp (f.inv.fiberTangent φ)) x = x
    rw [← Hom.fiberTangent_comp, f.hom_inv, Hom.fiberTangent_id, LinearMap.id_apply]

end Iso

namespace OrderAction

variable (E : OrderAction A M) (E' : OrderAction A N)

/-- The actual tangent representation at a coefficient-ring point. -/
def fiberTangent (φ : R →+* K) : A →+* Module.End K (σ → K) where
  toFun a := (E.action a).fiberTangent φ
  map_zero' := by rw [_root_.map_zero, Hom.fiberTangent_zero]
  map_add' a b := by rw [_root_.map_add, Hom.fiberTangent_add]
  map_one' := by rw [_root_.map_one]; exact Hom.fiberTangent_id φ
  map_mul' a b := by rw [_root_.map_mul]; exact Hom.fiberTangent_comp _ _ φ

@[simp]
theorem fiberTangent_apply (φ : R →+* K) (a : A) :
    E.fiberTangent φ a = (E.action a).fiberTangent φ := rfl

/-- Fibre tangent matrices are the images of the actual formal linear coefficients. -/
theorem fiberTangent_apply_apply [Fintype σ] (φ : R →+* K) (a : A)
    (x : σ → K) (i : σ) :
    E.fiberTangent φ a x i =
      ∑ j, φ ((E.action a).toHom.toCoordinateMap.linearCoeff i j) * x j := by
  change ((E.action a).toHom.toCoordinateMap.map φ).linearPart x i = _
  simp only [CoordinateMap.linearPart_apply, CoordinateMap.linearCoeff_map]

/-- Restriction to central O-scalars remains the natural scalar action on each fibre. -/
theorem fiberTangent_scalar (φ : R →+* K) (a : O) (x : σ → K) :
    E.fiberTangent φ (algebraMap O A a) x = φ (algebraMap O R a) • x := by
  change ((E.action (algebraMap O A a)).toHom.toCoordinateMap.map φ).linearPart x = _
  rw [E.extends_scalars]
  apply CoordinateMap.linearPart_scalar
  intro i j
  rw [CoordinateMap.linearCoeff_map, M.linear_natural,
    CoordinateMap.map_scalarLinearCoeff]

/-- Taking a fibre after coefficient extension is taking the corresponding composite fibre. -/
theorem fiberTangent_map (θ : R →ₐ[O] S) (φ : S →+* K) :
    (E.map θ).fiberTangent φ = E.fiberTangent (φ.comp θ.toRingHom) := by
  apply RingHom.ext
  intro a
  change (((E.action a).toHom.toCoordinateMap.map θ.toRingHom).map φ).linearPart = _
  rw [CoordinateMap.map_ringHom_comp]
  rfl

namespace Hom

variable {E E'}

/-- Derivatives of order-linear maps intertwine the actual fibre representations. -/
theorem fiberTangent_commutes (f : Hom E E') (φ : R →+* K) (a : A) :
    (f.val.fiberTangent φ).comp (E.fiberTangent φ a) =
      (E'.fiberTangent φ a).comp (f.val.fiberTangent φ) := by
  have h := congrArg (fun g : ModuleLaw.Hom M N => g.fiberTangent φ) (f.commutes a)
  simpa only [ModuleLaw.Hom.fiberTangent_comp, fiberTangent_apply] using h

end Hom

variable {C : Type r} [CommRing C]

/-- A certificate that the restricted, actual fibre representation is a sum
of d distinct one-dimensional characters. -/
structure TangentCharacterDecomposition (ι : C →+* A) (d : ℕ) (φ : R →+* K) where
  characters : Fin d → C →+* K
  distinct : Function.Injective characters
  coordinates : (σ → K) ≃ₗ[K] (Fin d → K)
  diagonalizes : ∀ (c : C) (x : σ → K) (i : Fin d),
    coordinates (E.fiberTangent φ (ι c) x) i = characters i c * coordinates x i

/-- The distinct-character condition at every algebraically closed field point,
universe by universe. -/
def HasGeometricTangentCharacters (ι : C →+* A) (d : ℕ) : Prop :=
  ∀ (L : Type q) [Field L] [IsAlgClosed L] (φ : R →+* L),
    Nonempty (E.TangentCharacterDecomposition ι d φ)

namespace TangentCharacterDecomposition

variable {E E'} {ι : C →+* A} {d : ℕ}

/-- A decomposition into d one-dimensional characters has tangent dimension d. -/
theorem finrank {L : Type q} [Field L] {φ : R →+* L}
    (h : E.TangentCharacterDecomposition ι d φ) :
    Module.finrank L (σ → L) = d := by
  rw [h.coordinates.finrank_eq]
  exact Module.finrank_fin_fun L

/-- The characters restrict to the actual natural O-scalar character. -/
theorem character_scalar {φ : R →+* K} (h : E.TangentCharacterDecomposition ι d φ)
    {c : C} {a : O} (hc : ι c = algebraMap O A a) (i : Fin d) :
    h.characters i c = φ (algebraMap O R a) := by
  have hdiag := h.diagonalizes c (h.coordinates.symm (Pi.single i 1)) i
  rw [hc, E.fiberTangent_scalar, _root_.map_smul] at hdiag
  simpa using hdiag.symm

/-- A composite fibre identifies the character decomposition after coefficient extension. -/
def map (θ : R →ₐ[O] S) (φ : S →+* K)
    (h : E.TangentCharacterDecomposition ι d (φ.comp θ.toRingHom)) :
    (E.map θ).TangentCharacterDecomposition ι d φ where
  characters := h.characters
  distinct := h.distinct
  coordinates := h.coordinates
  diagonalizes c x i := by
    rw [E.fiberTangent_map]
    exact h.diagonalizes c x i

/-- Transport a decomposition along the derivative of an actual order-linear isomorphism. -/
def ofIso {φ : R →+* K} (h : E.TangentCharacterDecomposition ι d φ)
    (f : Iso E E') : E'.TangentCharacterDecomposition ι d φ where
  characters := h.characters
  distinct := h.distinct
  coordinates := (f.toModuleIso.fiberTangent φ).symm.trans h.coordinates
  diagonalizes c x i := by
    change h.coordinates
      (f.inv.val.fiberTangent φ (E'.fiberTangent φ (ι c) x)) i =
      h.characters i c * h.coordinates (f.inv.val.fiberTangent φ x) i
    have hcomm := LinearMap.congr_fun (Hom.fiberTangent_commutes f.inv φ (ι c)) x
    change f.inv.val.fiberTangent φ (E'.fiberTangent φ (ι c) x) =
      E.fiberTangent φ (ι c) (f.inv.val.fiberTangent φ x) at hcomm
    rw [hcomm, h.diagonalizes]

end TangentCharacterDecomposition

namespace HasGeometricTangentCharacters

variable {E E'} {ι : C →+* A} {d : ℕ}

/-- Geometric tangent characters are preserved by arbitrary coefficient extension. -/
theorem map (h : E.HasGeometricTangentCharacters.{u, v, w, q, r} ι d)
    (θ : R →ₐ[O] S) :
    (E.map θ).HasGeometricTangentCharacters.{u, v, z, q, r} ι d := by
  intro L _ _ φ
  obtain ⟨hφ⟩ := h L (φ.comp θ.toRingHom)
  exact ⟨hφ.map θ φ⟩

/-- Geometric tangent characters are preserved by order-linear isomorphisms. -/
theorem ofIso (h : E.HasGeometricTangentCharacters.{u, v, w, q, r} ι d)
    (f : Iso E E') :
    E'.HasGeometricTangentCharacters.{u, v, w, q, r} ι d := by
  intro L _ _ φ
  obtain ⟨hφ⟩ := h L φ
  exact ⟨hφ.ofIso f⟩

/-- The geometric character condition depends only on the order-linear isomorphism class. -/
theorem iff_of_iso (f : Iso E E') :
    E.HasGeometricTangentCharacters.{u, v, w, q, r} ι d ↔
      E'.HasGeometricTangentCharacters.{u, v, w, q, r} ι d := by
  constructor
  · intro h
    exact h.ofIso f
  · intro h
    exact h.ofIso ⟨f.inv, f.hom, f.hom_inv, f.inv_hom⟩

end HasGeometricTangentCharacters

end OrderAction

end Langlands.FormalGroup.ModuleLaw
