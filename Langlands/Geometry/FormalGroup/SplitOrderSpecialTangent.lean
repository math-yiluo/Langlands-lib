import Langlands.Geometry.FormalGroup.SplitOrderTangent

/-! # Structural scalars and special tangent characters of the division summand -/

noncomputable section

universe u v w z q r

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {B : Type v} [Ring B] [Algebra O B]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {L : Type q} [CommRing L]
variable {C : Type r} [CommRing C]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable (E : OrderAction (Bᵐᵒᵖ × B) M) {E' : OrderAction (Bᵐᵒᵖ × B) N}

/-- Central scalars on the division tangent act by the structural coefficient map
over the full base ring. -/
def HasStructuralDivisionTangent (ι : C →+* B) (α : C →+* R) : Prop :=
  ∀ a : C, E.fiberTangent (RingHom.id R) (0, ι a) =
    α a • E.divisionTangentProjector (RingHom.id R)

namespace HasStructuralDivisionTangent

variable {E} {ι : C →+* B} {α : C →+* R}

/-- The structural identity on the whole coefficient ring gives the identity
after any ring map on coefficients. -/
theorem fiber (h : E.HasStructuralDivisionTangent ι α) (φ : R →+* L) (a : C) :
    E.fiberTangent φ (0, ι a) = φ (α a) • E.divisionTangentProjector φ := by
  classical
  let := Fintype.ofFinite σ
  have entry (i j : σ) :
      (E.action (0, ι a)).toHom.toCoordinateMap.linearCoeff i j =
        α a * (E.action (0, (1 : B))).toHom.toCoordinateMap.linearCoeff i j := by
    have hBasis := LinearMap.congr_fun (h a) (Pi.single j 1)
    have hi := congrFun hBasis i
    unfold divisionTangentProjector at hi
    simpa only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, fiberTangent_apply_apply,
      RingHom.id_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hi
  apply LinearMap.ext
  intro x
  funext i
  unfold divisionTangentProjector
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, fiberTangent_apply_apply,
    entry, _root_.map_mul, mul_assoc, Finset.mul_sum]

/-- On the actual division summand the restricted action is scalar multiplication. -/
theorem action (h : E.HasStructuralDivisionTangent ι α) (φ : R →+* L) (a : C)
    (x : E.divisionTangent φ) :
    E.divisionTangentAction φ (ι a) x = φ (α a) • x := by
  apply Subtype.ext
  change E.fiberTangent φ (0, ι a) x = φ (α a) • (x : σ → L)
  rw [h.fiber φ a, LinearMap.smul_apply, E.divisionTangentProjector_apply]

/-- It suffices to check the scalar action on the actual division summand over the base. -/
theorem of_action
    (h : ∀ (a : C) (x : E.divisionTangent (RingHom.id R)),
      E.divisionTangentAction (RingHom.id R) (ι a) x = α a • x) :
    E.HasStructuralDivisionTangent ι α := by
  intro a
  let φ := RingHom.id R
  apply LinearMap.ext
  intro x
  let P := E.divisionTangentProjector φ
  have hScalar := congrArg Subtype.val (h a ⟨P x, ⟨x, rfl⟩⟩)
  change (E.fiberTangent φ (0, ι a) * E.fiberTangent φ (0, 1)) x = α a • P x at hScalar
  have hProd : ((0, ι a) : Bᵐᵒᵖ × B) * (0, 1) = (0, ι a) := Prod.ext (zero_mul 0) (mul_one _)
  rw [← _root_.map_mul, hProd] at hScalar
  exact hScalar

/-- Structural scalar action is preserved under coefficient extension. -/
theorem map (h : E.HasStructuralDivisionTangent ι α) (θ : R →ₐ[O] S) :
    (E.map θ).HasStructuralDivisionTangent ι (θ.toRingHom.comp α) := by
  intro a
  unfold divisionTangentProjector
  rw [fiberTangent_map, RingHom.id_comp]
  exact h.fiber θ.toRingHom a

/-- Structural scalar action is preserved under actual order isomorphisms. -/
theorem ofIso (h : E.HasStructuralDivisionTangent ι α) (f : Iso E E') :
    E'.HasStructuralDivisionTangent ι α := by
  intro a
  let φ := RingHom.id R
  apply LinearMap.ext
  intro x
  apply (f.toModuleIso.fiberTangent φ).symm.injective
  change f.inv.val.fiberTangent φ (E'.fiberTangent φ (0, ι a) x) =
    f.inv.val.fiberTangent φ (α a • E'.fiberTangent φ (0, 1) x)
  rw [map_smul]
  have hι := LinearMap.congr_fun (f.inv.fiberTangent_commutes φ (0, ι a)) x
  have hP := LinearMap.congr_fun (f.inv.fiberTangent_commutes φ (0, 1)) x
  change f.inv.val.fiberTangent φ (E'.fiberTangent φ (0, ι a) x) =
    E.fiberTangent φ (0, ι a) (f.inv.val.fiberTangent φ x) at hι
  change f.inv.val.fiberTangent φ (E'.fiberTangent φ (0, 1) x) =
    E.fiberTangent φ (0, 1) (f.inv.val.fiberTangent φ x) at hP
  exact hι.trans ((LinearMap.congr_fun (h a) (f.inv.val.fiberTangent φ x)).trans
    (congrArg (α a • ·) hP.symm))

end HasStructuralDivisionTangent

/-- Each of the distinct characters on the division tangent has multiplicity one. -/
structure DivisionTangentCharacterDecomposition (ι : C →+* B) (d : ℕ) (φ : R →+* L) where
  characters : Fin d → C →+* L
  distinct : Function.Injective characters
  coordinates : E.divisionTangent φ ≃ₗ[L] (Fin d → L)
  diagonalizes : ∀ (a : C) (x : E.divisionTangent φ) (i : Fin d),
    coordinates (E.divisionTangentAction φ (ι a) x) i = characters i a * coordinates x i

/-- The multiplicity-one condition on algebraically closed field tests in a
universe containing the base ring's residue fields. -/
def HasGeometricDivisionTangentCharacters (ι : C →+* B) (d : ℕ) : Prop :=
  ∀ (K : Type (max w q)) [Field K] [IsAlgClosed K] (φ : R →+* K),
    Nonempty (E.DivisionTangentCharacterDecomposition ι d φ)

namespace DivisionTangentCharacterDecomposition

variable {E} {ι : C →+* B} {d : ℕ}

/-- The multiplicity-one condition fixes the dimension of the actual division tangent. -/
theorem finrank {K : Type q} [Field K] {φ : R →+* K}
    (h : E.DivisionTangentCharacterDecomposition ι d φ) :
    Module.finrank K (E.divisionTangent φ) = d := by
  rw [h.coordinates.finrank_eq]
  exact Module.finrank_fin_fun K

/-- Each character above the central scalar ring restricts to the structural character. -/
theorem character_scalar {C₀ : Type*} [CommRing C₀]
    {φ : R →+* L} (h : E.DivisionTangentCharacterDecomposition ι d φ)
    (η : C₀ →+* C) (α : C₀ →+* R)
    (hs : E.HasStructuralDivisionTangent (ι.comp η) α) (i : Fin d) (a : C₀) :
    h.characters i (η a) = φ (α a) := by
  let x := h.coordinates.symm (Pi.single i 1)
  have hdiag := h.diagonalizes (η a) x i
  have hscalar := hs.action φ a x
  change E.divisionTangentAction φ (ι (η a)) x = φ (α a) • x at hscalar
  rw [hscalar, map_smul] at hdiag
  simpa [x] using hdiag.symm

end DivisionTangentCharacterDecomposition

namespace HasGeometricDivisionTangentCharacters

variable {E} {ι : C →+* B} {d : ℕ}

/-- Multiplicity one survives coefficient extension using a common test
universe for both bases. -/
theorem map (h : E.HasGeometricDivisionTangentCharacters.{u, v, w, max z q, r} ι d)
    (θ : R →ₐ[O] S) :
    (E.map θ).HasGeometricDivisionTangentCharacters.{u, v, z, max w q, r} ι d := by
  intro K _ _ φ
  obtain ⟨hφ⟩ := h K (φ.comp θ.toRingHom)
  let e := E.divisionTangentBaseChangeEquiv θ φ
  refine ⟨⟨hφ.characters, hφ.distinct, e.trans hφ.coordinates, ?_⟩⟩
  intro a x i
  change hφ.coordinates (e ((E.map θ).divisionTangentAction φ (ι a) x)) i =
    hφ.characters i a * hφ.coordinates (e x) i
  rw [E.divisionTangentBaseChangeEquiv_commutes, hφ.diagonalizes]

/-- Multiplicity one is invariant under the derivative of an actual order isomorphism. -/
theorem ofIso (h : E.HasGeometricDivisionTangentCharacters.{u, v, w, q, r} ι d)
    (f : Iso E E') :
    E'.HasGeometricDivisionTangentCharacters.{u, v, w, q, r} ι d := by
  intro K _ _ φ
  obtain ⟨hφ⟩ := h K φ
  let inverse : Iso E' E := ⟨f.inv, f.hom, f.hom_inv, f.inv_hom⟩
  let e := inverse.divisionTangentEquiv φ
  refine ⟨⟨hφ.characters, hφ.distinct, e.trans hφ.coordinates, ?_⟩⟩
  intro a x i
  change hφ.coordinates (e (E'.divisionTangentAction φ (ι a) x)) i =
    hφ.characters i a * hφ.coordinates (e x) i
  rw [inverse.divisionTangentEquiv_commutes, hφ.diagonalizes]

end HasGeometricDivisionTangentCharacters

end Langlands.FormalGroup.ModuleLaw.OrderAction
