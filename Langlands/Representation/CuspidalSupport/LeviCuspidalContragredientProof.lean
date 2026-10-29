import Langlands.Representation.Parabolic.RefinementReversal
import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.Parabolic.NaturalJacquetDualityProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Group.GL.ReverseBlocks
import Langlands.Group.GL.CompactOpen

/-!
# Smooth contragredients of cuspidal product-Levi representations

Blockwise block reversal carries every upper refined radical to an opposite
refined radical. The natural refined Jacquet duality then turns vanishing
opposite coinvariants into vanishing upper coinvariants of the smooth dual.
-/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

section Geometry

variable (R : Type*) [CommRing R] {n : ℕ} (B : BlockShape n)

/-- Conjugation by the blockwise reversal carries the upper radical of the
reversed refinement onto the opposite radical of the original refinement. -/
theorem innerReverseRefinement_refinedUnipotent_map_conj (S : BlockRefinement B) :
    (refinedUnipotent R B (ProductLeviDualOpposite.reverseRefinement B S)).map
        (MulAut.conj (ProductLeviDualOpposite.reverseWeyl B S R)).toMonoidHom =
      refinedOppositeUnipotent R B S := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_refinedOppositeUnipotent]
  simp only [refinedUnipotent, Subgroup.mem_pi, Set.mem_univ, forall_true_left]
  refine forall_congr' fun i => ?_
  rw [← (S i).reverse_unipotentSubgroup_map_conj R, Subgroup.mem_map_equiv]
  rfl

/-- A refined parabolic is the whole product Levi exactly when every block
parabolic is the whole block group. -/
theorem refinedParabolic_eq_top_iff (S : BlockRefinement B) :
    refinedParabolic R B S = ⊤ ↔ ∀ i, (S i).parabolic R = ⊤ := by
  constructor
  · intro h i
    rw [Subgroup.eq_top_iff']
    intro g
    have hg : (Pi.mulSingle i g : B.Levi R) ∈ refinedParabolic R B S :=
      h ▸ Subgroup.mem_top _
    simpa using ((Subgroup.mem_pi _).mp hg) i (Set.mem_univ i)
  · intro h
    rw [Subgroup.eq_top_iff']
    intro g
    exact (Subgroup.mem_pi _).mpr fun i _ => (h i).symm ▸ Subgroup.mem_top (g i)

/-- Blockwise reversal preserves properness of the refined parabolic. -/
theorem innerReverseRefinement_refinedParabolic_ne_top_iff (S : BlockRefinement B) :
    refinedParabolic R B (ProductLeviDualOpposite.reverseRefinement B S) ≠ ⊤ ↔ refinedParabolic R B S ≠ ⊤ := by
  rw [Ne, Ne, refinedParabolic_eq_top_iff, refinedParabolic_eq_top_iff]
  exact not_congr (forall_congr' fun i => (S i).reverse_parabolic_eq_top_iff R)

end Geometry

/-- Vanishing opposite refined coinvariants of an admissible representation
imply vanishing upper refined coinvariants of its smooth contragredient. -/
theorem refinedJacquet_smoothContragredient_subsingleton_of_opposite
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ ρ : Representation ℂ (B.Levi F.Carrier) V, IsAdmissible ρ →
      Subsingleton (Jacquet.Coinvariants ρ (refinedOppositeUnipotent F.Carrier B S)) →
      Subsingleton (Jacquet.Coinvariants (smoothContragredient ρ)
        (refinedUnipotent F.Carrier B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hadm hvan
  obtain ⟨E, _⟩ := Parabolic.refinedNaturalJacquetDuality p F T n B S
  let e := E (Rep.of ρ) hadm
  let : Subsingleton (RefinedOppositeJacquetModule B S (Rep.of ρ).ρ) := hvan
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-- The smooth contragredient of a cuspidal representation of an actual
product Levi is cuspidal. -/
theorem leviCuspidalContragredient {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviCuspidalContragredientTheorem.{uF, uV} F T B := by
  let := T.topology
  let := T.leviTopologicalGroup B
  rintro A ⟨hadm, hvan⟩
  refine ⟨isAdmissible_smoothContragredient_of_compact_cofinal ?_ A.representation hadm, ?_⟩
  · intro K
    obtain ⟨L, hL, hLK⟩ := T.leviCompactOpen B K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, fun _ hx => hLK hx⟩
  · intro S hS
    have hrev := hvan (ProductLeviDualOpposite.reverseRefinement B S)
      ((innerReverseRefinement_refinedParabolic_ne_top_iff F.Carrier B S).mpr hS)
    have hopp := (Jacquet.coinvariants_conj_subsingleton_iff A.representation _
      (ProductLeviDualOpposite.reverseWeyl B S F.Carrier)).mpr hrev
    rw [innerReverseRefinement_refinedUnipotent_map_conj] at hopp
    exact refinedJacquet_smoothContragredient_subsingleton_of_opposite F T B S _
      A.representation hadm hopp

end Langlands.CuspidalSupport
