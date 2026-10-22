import Langlands.Geometry.Analytic.WeierstrassPresentation.Statement
import Langlands.Geometry.Analytic.TatePresentation

/-! # Bounded extensions from actual Weierstrass presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic.WeierstrassPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- Every point of the constructed quotient maps into the indicated norm locus.
The reverse inclusion and analytic-domain representability are separate results. -/
theorem comap_mem_locus (x : BanachSpectrum (algebra K n m S f)) :
    BanachSpectrum.comap (baseMap K n m S f).toBoundedRingHom x ∈ locus K n m S f := by
  intro j
  change x (baseMap K n m S f (presentationMap K (ofRelations K n S) (f j))) ≤ 1
  rw [← coordinate_equation]
  calc
    x (coordinate K (algebra K n m S f) (Fin.natAdd n j))
        ≤ ‖coordinate K (algebra K n m S f) (Fin.natAdd n j)‖ := x.le_norm _
    _ ≤ ‖X (Fin (n + m)) K (Fin.natAdd n j)‖ :=
      Ideal.Quotient.norm_mk_le _ _
    _ = 1 := norm_X _ _ _

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

/-- The old coordinate images, followed by the forced images of the new coordinates. -/
def solutionTuple (φ : BoundedAlgHom K (ofRelations K n S) B) : Fin (n + m) → B :=
  Fin.append (fun i => φ (coordinate K (ofRelations K n S) i))
    (fun j => φ (presentationMap K (ofRelations K n S) (f j)))

omit [CompleteSpace K] [IsUltrametricDist B] [CompleteSpace B] in
theorem solutionTuple_bounded (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hf : ∀ j, ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C) :
    HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S f B φ) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h := hasBoundedMonomials_map_X (Fin n) K B
      (φ.comp (presentationMap K (ofRelations K n S)))
    have hi := h.pow_bound (Fin n) B i
    change ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (coordinate K (ofRelations K n S) i) ^ r‖ ≤ C at hi
    simpa only [solutionTuple, Fin.append_left] using hi
  · simpa only [solutionTuple, Fin.append_right] using hf j

theorem evaluate_included (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hb : HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S f B φ))
    (h : StrictTateAlgebra (Fin n) K) :
    evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ)
      (adjoinVariables K n m h) = φ (presentationMap K (ofRelations K n S) h) := by
  have hmaps :
      (evaluateHom (Fin (n + m)) K B (solutionTuple K n m S f B φ) hb).comp
        (adjoinVariables K n m) = φ.comp (presentationMap K (ofRelations K n S)) := by
    apply StrictTateAlgebra.hom_ext
    intro i
    change evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ)
      (adjoinVariables K n m (X (Fin n) K i)) = _
    rw [adjoinVariables_X, evaluate_X]
    exact Fin.append_left _ _ i
  exact congrArg (fun χ => χ h) hmaps

theorem solutionTuple_relations (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hb : HasBoundedMonomials (Fin (n + m)) B (solutionTuple K n m S f B φ)) :
    ∀ h ∈ relations K n m S f,
      evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ) h = 0 := by
  intro h hh
  rcases hh with hh | hh
  · obtain ⟨h, hh, rfl⟩ := hh
    rw [evaluate_included K n m S f B φ hb,
      presentationMap_relation K n S hh]
    exact map_zero φ.toAlgHom
  · obtain ⟨j, rfl⟩ := hh
    change (evaluateHom (Fin (n + m)) K B (solutionTuple K n m S f B φ) hb).toAlgHom
      (_ - _) = 0
    rw [map_sub]
    change evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ)
      (X (Fin (n + m)) K (Fin.natAdd n j)) -
        evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ)
          (adjoinVariables K n m (f j)) = 0
    rw [evaluate_X, evaluate_included K n m S f B φ hb]
    simp only [solutionTuple, Fin.append_right, sub_self]

/-- The actual extension of a bounded base map whose constrained elements
have bounded powers. It is constructed by convergent evaluation and quotient descent. -/
def liftFromBase (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hf : ∀ j, ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C) :
    BoundedAlgHom K (algebra K n m S f) B :=
  liftRelations K (n + m) (relations K n m S f) B
    (solutionTuple K n m S f B φ) (solutionTuple_bounded K n m S f B φ hf)
    (solutionTuple_relations K n m S f B φ (solutionTuple_bounded K n m S f B φ hf))

theorem liftFromBase_comp_baseMap (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hf : ∀ j, ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C) :
    (liftFromBase K n m S f B φ hf).comp (baseMap K n m S f) = φ := by
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (ofRelations K n S) a
  change evaluate (Fin (n + m)) K B (solutionTuple K n m S f B φ)
    (adjoinVariables K n m h) = φ (presentationMap K (ofRelations K n S) h)
  exact evaluate_included K n m S f B φ (solutionTuple_bounded K n m S f B φ hf) h

omit [IsUltrametricDist B] [CompleteSpace B] in
/-- A bounded map out of this presentation is determined by its restriction
to the base, because the new coordinates are the images of the constrained elements. -/
theorem hom_ext_base (φ ψ : BoundedAlgHom K (algebra K n m S f) B)
    (h : φ.comp (baseMap K n m S f) = ψ.comp (baseMap K n m S f)) : φ = ψ := by
  apply hom_ext_coordinates K (n + m) (relations K n m S f) B
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · exact (congrArg φ (baseMap_coordinate K n m S f i)).symm.trans
      ((congrArg (fun χ => χ (coordinate K (ofRelations K n S) i)) h).trans
        (congrArg ψ (baseMap_coordinate K n m S f i)))
  · exact (congrArg φ (coordinate_equation K n m S f j)).trans
      ((congrArg (fun χ => χ (presentationMap K (ofRelations K n S) (f j))) h).trans
        (congrArg ψ (coordinate_equation K n m S f j)).symm)

/-- Existence and uniqueness of bounded extension, under the explicit
power-boundedness condition. No analytic-domain theorem is assumed. -/
theorem existsUnique_extension (φ : BoundedAlgHom K (ofRelations K n S) B)
    (hf : ∀ j, ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ, ‖φ (presentationMap K (ofRelations K n S) (f j)) ^ r‖ ≤ C) :
    ∃! ψ : BoundedAlgHom K (algebra K n m S f) B,
      ψ.comp (baseMap K n m S f) = φ := by
  refine ⟨liftFromBase K n m S f B φ hf, liftFromBase_comp_baseMap K n m S f B φ hf,
    fun ψ hψ => ?_⟩
  apply hom_ext_base K n m S f B
  rw [hψ, liftFromBase_comp_baseMap]

/-- The actual Weierstrass presentation has the stated forward spectrum map
and bounded extension property, with target hypotheses separated. -/
theorem boundedExtension : BoundedExtensionStatement.{u, v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ _ n m S f x
    exact comap_mem_locus K n m S f x
  · intro K _ _ _ n m S f B _ _ φ ψ h
    exact hom_ext_base K n m S f B φ ψ h
  · intro K _ _ _ n m S f B _ _ _ _ φ hf
    exact existsUnique_extension K n m S f B φ hf

end Langlands.Analytic.WeierstrassPresentation
