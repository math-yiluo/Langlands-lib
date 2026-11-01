import Langlands.Representation.Aubert.CorrectedOrbitCoefficientJacquet
import Langlands.Representation.Geometric.RefinementSolomonCoefficients

/-! Common actual coefficient quotients across whole-target active cuts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear

universe uF

/-- A whole target intersection makes the source intersection the inverse
conjugate of that whole target. -/
theorem intersectionSource_eq_of_intersectionTarget_eq
    {G : Type*} [Group G] (M N : Subgroup G) (w : G)
    (h : N ⊓ M.comap (MulAut.conj w⁻¹).toMonoidHom = N) :
    M ⊓ N.comap (MulAut.conj w).toMonoidHom =
      N.comap (MulAut.conj w).toMonoidHom := by
  apply inf_eq_right.mpr
  intro x hx
  have he := congrArg (fun H : Subgroup G => w * x * w⁻¹ ∈ H) h
  have hh : w * x * w⁻¹ ∈ N ⊓ M.comap (MulAut.conj w⁻¹).toMonoidHom :=
    he.mpr hx
  have hm : w⁻¹ * (w * x * w⁻¹) * (w⁻¹)⁻¹ ∈ M := hh.2
  simpa [mul_assoc] using hm

/-- Actual source refinements at whole-target cuts all flatten to the same
standard block shape, without a choice of coordinates or representative. -/
theorem wholeTarget_flattened_eq
    {F : Type uF} [CommRing F] [Nontrivial F] {n : ℕ}
    (B D C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement D)
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F D C w = refinedLevi F D R)
    (hB : blockWeyl C ⊓ (blockWeyl B).comap
      (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C)
    (hD : blockWeyl C ⊓ (blockWeyl D).comap
      (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C) :
    B.flatten S = D.flatten R := by
  apply blockWeyl_injective
  rw [blockWeyl_flatten_eq_intersection F B C w S hS,
    blockWeyl_flatten_eq_intersection F D C w R hR,
    intersectionSource_eq_of_intersectionTarget_eq _ _ _ hB,
    intersectionSource_eq_of_intersectionTarget_eq _ _ _ hD]

end Langlands.Geometric

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))

/-- Relabel an actual Jacquet quotient by equality of its block shape. -/
def jacquetShapeCongr (B D : BlockShape n) (h : B = D) :
    letI := T.topology
    B.JacquetModule A.representation ≃ₗ[ℂ] D.JacquetModule A.representation := by
  subst D
  exact LinearEquiv.refl _ _

@[simp]
theorem jacquetShapeCongr_mk (B D : BlockShape n) (h : B = D) :
    letI := T.topology
    ∀ v : A, jacquetShapeCongr T A B D h (B.jacquetMk A.representation v) =
      D.jacquetMk A.representation v := by
  subst D
  intro v
  rfl

variable (B D C Q : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement D)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)
  (hR : IsIntersectionRefinement (F := F.Carrier) D C w R)

/-- Compare a genuine nested orbit coefficient with a supplied common actual
flattened Jacquet quotient. -/
def cutOrbitCoefficientCommonEquiv (hQ : B.flatten S = Q) :
    letI := T.topology
    Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B) ≃ₗ[ℂ]
      Q.JacquetModule A.representation := by
  let := T.topology
  exact (cutOrbitCoefficientJacquetEquiv T A B C w S hS).trans
    (jacquetShapeCongr T A (B.flatten S) Q hQ)

@[simp]
theorem cutOrbitCoefficientCommonEquiv_mk_mk (hQ : B.flatten S = Q) :
    letI := T.topology
    ∀ v : A,
      cutOrbitCoefficientCommonEquiv T A B C Q w S hS hQ
        (Representation.Coinvariants.mk (cutOrbitNestedCoefficient T A.representation C w B)
          (B.jacquetMk A.representation v)) = Q.jacquetMk A.representation v := by
  let := T.topology
  intro v
  change jacquetShapeCongr T A (B.flatten S) Q hQ
    (cutOrbitCoefficientJacquetEquiv T A B C w S hS
      (Representation.Coinvariants.mk (cutOrbitNestedCoefficient T A.representation C w B)
        (B.jacquetMk A.representation v))) = _
  rw [cutOrbitCoefficientJacquetEquiv_mk_mk, jacquetShapeCongr_mk]

/-- The genuine cross-cut coefficient projection is the identity after the
representative-preserving identifications with one common Jacquet quotient. -/
theorem cutOrbitCoefficientCommonEquiv_cutMap
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)
    (hBQ : B.flatten S = Q) (hDQ : D.flatten R = Q) :
    letI := T.topology
    ∀ z : Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B),
      cutOrbitCoefficientCommonEquiv T A D C Q w R hR hDQ
        (cutOrbitCoefficientMap T A.representation B D C w h hw z) =
      cutOrbitCoefficientCommonEquiv T A B C Q w S hS hBQ z := by
  let := T.topology
  intro z
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective
    (cutOrbitNestedCoefficient T A.representation C w B) z
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation x
  rw [cutOrbitCoefficientMap_mk, Transition.quotient_mk,
    cutOrbitCoefficientCommonEquiv_mk_mk, cutOrbitCoefficientCommonEquiv_mk_mk]

end Langlands.Aubert.Support
