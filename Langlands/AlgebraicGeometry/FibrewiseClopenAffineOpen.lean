import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Irreducible

/-! # An affine-open criterion across a principal divisor -/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.FibrewiseClopenAffineOpen

/-- In a space with irreducible open neighborhoods, the closure of an open set is open. -/
lemma isOpen_closure_of_irreducible_neighborhoods
    {T : Type u} [TopologicalSpace T]
    (hlocal : ∀ x : T, ∃ N : Opens T, x ∈ N ∧ IsIrreducible (N : Set T))
    {W : Set T} (hW : IsOpen W) : IsOpen (closure W) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨N, hxN, hN⟩ := hlocal x
  have hNW : ((N : Set T) ∩ W).Nonempty :=
    mem_closure_iff.mp hx N N.isOpen hxN
  refine ⟨N, ?_, N.isOpen, hxN⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hN.2 hW hNW).trans
    (closure_mono Set.inter_subset_right)

/-- An open is affine when it is closed on a dense principal open and on its complement,
provided the ambient affine scheme has irreducible open neighborhoods. -/
theorem isAffineOpen_of_closed_on_principal_and_complement
    (X : Scheme.{u}) [IsAffine X] (f : Γ(X, ⊤)) (U : X.Opens)
    (hlocal : ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ IsIrreducible (N : Set X))
    (hdense : Dense (X.basicOpen f : Set X))
    (hgeneric : IsClosed ((Subtype.val : X.basicOpen f → X) ⁻¹' (U : Set X)))
    (hspecial : IsClosed ((U : Set X) \ (X.basicOpen f : Set X))) :
    IsAffineOpen U := by
  classical
  let D : X.Opens := X.basicOpen f
  let C : X.Opens := ⟨closure ((U : Set X) ∩ (D : Set X)),
    isOpen_closure_of_irreducible_neighborhoods hlocal (U.isOpen.inter D.isOpen)⟩
  have hUC : U ≤ C := by
    intro x hxU
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, ⟨hyO, hyU⟩, hyD⟩ :=
      hdense.inter_open_nonempty (O ∩ (U : Set X)) (hO.inter U.isOpen) ⟨x, hxO, hxU⟩
    exact ⟨y, hyO, hyU, hyD⟩
  have hCD : (C : Set X) ∩ (D : Set X) ⊆ (U : Set X) := by
    intro x hx
    apply (Topology.IsInducing.subtypeVal.isClosed_iff'.mp hgeneric) ⟨x, hx.2⟩
    change x ∈ closure ((Subtype.val : D → X) ''
      ((Subtype.val : D → X) ⁻¹' (U : Set X)))
    have heq : (Subtype.val : D → X) ''
        ((Subtype.val : D → X) ⁻¹' (U : Set X)) =
        (U : Set X) ∩ (D : Set X) := by
      ext z
      simp
    rw [heq]
    exact hx.1
  have hι : IsAffineHom U.ι := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro x
    by_cases hxU : x ∈ U
    · obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
      refine ⟨V, hxV, hV, ?_⟩
      exact hV.preimage_of_isOpenImmersion U.ι (by simpa using hVU)
    · by_cases hxC : x ∈ C
      · let E : X.Opens := ⟨((U : Set X) \ (D : Set X))ᶜ, hspecial.isOpen_compl⟩
        have hxE : x ∈ E := fun hx => hxU hx.1
        obtain ⟨V, hV, hxV, hVW⟩ :=
          exists_isAffineOpen_mem_and_subset (show x ∈ C ⊓ E from ⟨hxC, hxE⟩)
        refine ⟨V, hxV, hV, ?_⟩
        rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion,
          Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        have heq : U ⊓ V =
            X.basicOpen (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op f) := by
          rw [Scheme.basicOpen_res]
          ext y
          constructor
          · rintro ⟨hyU, hyV⟩
            exact ⟨hyV, by
              by_contra hyD
              exact (hVW hyV).2 ⟨hyU, hyD⟩⟩
          · rintro ⟨hyV, hyD⟩
            exact ⟨hCD ⟨(hVW hyV).1, hyD⟩, hyV⟩
        rw [heq]
        exact hV.basicOpen _
      · let E : X.Opens := ⟨(C : Set X)ᶜ, isClosed_closure.isOpen_compl⟩
        obtain ⟨V, hV, hxV, hVE⟩ :=
          exists_isAffineOpen_mem_and_subset (show x ∈ E from hxC)
        refine ⟨V, hxV, hV, ?_⟩
        have heq : U.ι ⁻¹ᵁ V = ⊥ := by
          ext y
          change y.1 ∈ V ↔ False
          exact ⟨fun hyV => hVE hyV (hUC y.2), False.elim⟩
        rw [heq]
        exact isAffineOpen_bot _
  exact isAffine_of_isAffineHom U.ι

end Langlands.AlgebraicGeometry.FibrewiseClopenAffineOpen
