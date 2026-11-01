import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChangeNaturality
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Adjoin

/-! # Strict scalar change of the actual variable-adjunction map -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K))

/-- The old ideal is sent into the actual enlarged closed relation ideal. -/
theorem appendLeft_mem_ideal (f : GeneralizedTateAlgebra A.polyradius K)
    (hf : f ∈ A.ideal) :
    rename A.polyradius (algebra K A s equations).polyradius (Fin.castAddEmb m)
      (fun i => PositivePolyradius.append_castAdd A.polyradius s i) K f ∈
        (algebra K A s equations).ideal :=
  relation_mem K (A.arity + m) (A.polyradius.append s) (relations K A s equations)
    (Set.mem_union_left _ ⟨f, hf, rfl⟩)

/-- The existing structural map is the generic actual quotient variable inclusion. -/
theorem baseMap_eq_renameHom :
    baseMap K A s equations =
      renameHom A (algebra K A s equations) (Fin.castAddEmb m)
        (fun i => PositivePolyradius.append_castAdd A.polyradius s i)
        (appendLeft_mem_ideal A s equations) := rfl

variable (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ i, ‖c i‖ = A.polyradius i)
  {t : Fin m → L} (ht : ∀ j, ‖t j‖ = s j)

omit [IsUltrametricDist L] in
include hc ht in
/-- The combined scalar tuple realizes the enlarged polyradius exactly. -/
theorem norm_addCases (i : Fin (A.arity + m)) :
    ‖(Fin.addCases c t : Fin (A.arity + m) → L) i‖ = (A.polyradius.append s) i := by
  refine Fin.addCases (motive := fun i => ‖(Fin.addCases c t : Fin (A.arity + m) → L) i‖ =
    (A.polyradius.append s) i) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left, PositivePolyradius.append_castAdd] using hc j
  · simpa only [Fin.addCases_right, PositivePolyradius.append_natAdd] using ht j

/-- Include the old normalized strict variables in the strict scalar extension
of the actual variable-adjunction quotient. -/
def strictBaseChangeMap :
    BoundedAlgHom L (strictBaseChange A ι hι hc)
      (strictBaseChange (algebra K A s equations) ι hι (norm_addCases A s hc ht)) :=
  strictBaseChangeRenameHom A (algebra K A s equations) (Fin.castAddEmb m)
    (fun i => PositivePolyradius.append_castAdd A.polyradius s i)
    (appendLeft_mem_ideal A s equations) ι hι hc (norm_addCases A s hc ht)
    (fun i => by
      change (Fin.addCases c t : Fin (A.arity + m) → L) (Fin.castAdd m i) = c i
      exact Fin.addCases_left i)

/-- This actual strict map commutes with the original structural map. -/
theorem strictBaseChangeMap_strictBaseChangeHom (a : A) :
    strictBaseChangeMap A s equations ι hι hc ht (strictBaseChangeHom A ι hι hc a) =
      strictBaseChangeHom (algebra K A s equations) ι hι (norm_addCases A s hc ht)
        (baseMap K A s equations a) := by
  rw [baseMap_eq_renameHom]
  exact strictBaseChangeRenameHom_strictBaseChangeHom A (algebra K A s equations)
    (Fin.castAddEmb m) (fun i => PositivePolyradius.append_castAdd A.polyradius s i)
    (appendLeft_mem_ideal A s equations) ι hι hc (norm_addCases A s hc ht)
    (fun i => by
      change (Fin.addCases c t : Fin (A.arity + m) → L) (Fin.castAdd m i) = c i
      exact Fin.addCases_left i) a

variable (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

/-- Coefficient descent is natural for the actual variable-adjunction map,
including rational-chart structural maps. -/
theorem strictBaseChangeRetraction_baseMap (a : strictBaseChange A ι hι hc) :
    strictBaseChangeRetraction (algebra K A s equations) ι hι (norm_addCases A s hc ht)
        π hπ hD hπD (strictBaseChangeMap A s equations ι hι hc ht a) =
      baseMap K A s equations (strictBaseChangeRetraction A ι hι hc π hπ hD hπD a) := by
  rw [baseMap_eq_renameHom]
  exact strictBaseChangeRetraction_renameHom A (algebra K A s equations)
    (Fin.castAddEmb m) (fun i => PositivePolyradius.append_castAdd A.polyradius s i)
    (appendLeft_mem_ideal A s equations) ι hι hc (norm_addCases A s hc ht)
    (fun i => by
      change (Fin.addCases c t : Fin (A.arity + m) → L) (Fin.castAdd m i) = c i
      exact Fin.addCases_left i) π hπ hD hπD a

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
