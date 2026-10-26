import Langlands.Representation.CuspidalSupport.RefinedJacquetLengthStatement
import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-! Finite length detected by the proper refined Jacquet modules of a product Levi. -/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.CuspidalSupport

universe uF uV uW uX

namespace RefinedJacquetLengthProof

open GeneralLinear Representation JacquetDetectingFamilyLengthProof

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (C : Geometric.BlockRefinement B)

/-- Normalization changes the action, but the actual quotient linear map is
precisely the refined unipotent coinvariant map. -/
theorem map_toLinearMap
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap σ) :
    (T.normalizedRefinedJacquetMap B C f).toLinearMap =
      Coinvariants.map _ _ (Jacquet.restrictMap f (Geometric.refinedUnipotent F.Carrier B C)) :=
  rfl

/-- Refined Jacquet descent preserves an injection into a smooth representation. -/
theorem map_injective
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap σ) :
    letI := T.topology
    IsSmooth σ → Function.Injective f →
      Function.Injective (T.normalizedRefinedJacquetMap B C f) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro hσ hf
  change Function.Injective (T.normalizedRefinedJacquetMap B C f).toLinearMap
  rw [map_toLinearMap]
  exact coinvariants_map_injective_of_smooth (T.refinedUnipotent_finite_containment B C)
    _ hf (isSmooth_comp _ continuous_subtype_val hσ)

/-- Exactness on the actual refined quotient maps, with only the middle
representation required to be smooth. -/
theorem map_exact
    {V : Type uV} {W : Type uW} {X : Type uX}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W}
    {τ : Representation ℂ (B.Levi F.Carrier) X}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) :
    letI := T.topology
    IsSmooth σ → Function.Injective i → Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    Function.Injective (T.normalizedRefinedJacquetMap B C i) ∧
      LinearMap.range (T.normalizedRefinedJacquetMap B C i).toLinearMap =
        LinearMap.ker (T.normalizedRefinedJacquetMap B C q).toLinearMap ∧
      Function.Surjective (T.normalizedRefinedJacquetMap B C q) := by
  let := T.topology
  intro hσ hi hq hex
  refine ⟨map_injective T B C i hσ hi, ?_, ?_⟩
  · rw [map_toLinearMap, map_toLinearMap]
    exact coinvariants_map_range_eq_ker _ _ hq hex
  · change Function.Surjective (T.normalizedRefinedJacquetMap B C q).toLinearMap
    rw [map_toLinearMap]
    exact Langlands.coinvariants_map_surjective _ hq

/-- Module length is monotone under the refined Jacquet map of a smooth injection. -/
theorem length_le :
    letI := T.topology
    ∀ {A D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)}
      (f : A.representation.IntertwiningMap D.representation),
      Function.Injective f →
      repLength (T.normalizedRefinedJacquet B C A.representation) ≤
        repLength (T.normalizedRefinedJacquet B C D.representation) := by
  let := T.topology
  intro A D f hf
  exact Module.length_le_of_injective
    (IntertwiningMap.equivLinearMapAsModule _ _ (T.normalizedRefinedJacquetMap B C f))
    (map_injective T B C f D.isSmooth hf)

/-- Additivity for the actual successive quotient of nested smooth invariant subspaces. -/
theorem length_step :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (S U : Subrepresentation A.representation) (_h : S ≤ U),
      repLength (T.normalizedRefinedJacquet B C
        (SmoothRep.subrepresentation A U).representation) =
        repLength (T.normalizedRefinedJacquet B C
          (SmoothRep.subrepresentation A S).representation) +
        repLength (T.normalizedRefinedJacquet B C
          (SmoothRep.subquotient A U (lower A S U)).representation) := by
  let := T.topology
  intro A S U h
  let i := inclusion A S U h
  let q := SmoothRep.hom (SmoothRep.mkQ (SmoothRep.subrepresentation A U) (lower A S U))
  obtain ⟨hi, hex, hq⟩ := map_exact T B C i q
    (SmoothRep.subrepresentation A U).isSmooth (Submodule.inclusion_injective h)
    (SmoothRep.mkQ_surjective _ _) (inclusion_exact A S U h)
  exact repLength_eq_add_of_exact (T.normalizedRefinedJacquetMap B C i)
    (T.normalizedRefinedJacquetMap B C q) hi hq hex

end RefinedJacquetLengthProof

open JacquetDetectingFamilyLengthProof RefinedJacquetLengthProof in
/-- The closed product-Levi criterion: absence of nonzero quasicuspidal
subquotients and finite length of all proper refined Jacquet modules imply finite length. -/
theorem refinedJacquetFiniteLengthDetection :
    RefinedJacquetFiniteLengthDetectionStatement.{uF, uV} := by
  classical
  intro p hp F T n B
  let := T.topology
  intro A hvanish hlength
  let : Fintype (Geometric.BlockRefinement B) := Fintype.ofFinite _
  let s : Finset (Geometric.BlockRefinement B) :=
    Finset.univ.filter fun C => Geometric.refinedParabolic F.Carrier B C ≠ ⊤
  let b := fun C : Geometric.BlockRefinement B =>
    (repLength (T.normalizedRefinedJacquet B C A.representation)).toNat
  have hbound (C : Geometric.BlockRefinement B) (hC : C ∈ s) :
      repLength (T.normalizedRefinedJacquet B C A.representation) ≤ b C := by
    have hfinite : repLength (T.normalizedRefinedJacquet B C A.representation) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr (hlength C (Finset.mem_filter.mp hC).2)
    exact le_of_eq (ENat.natCast_toNat hfinite).symm
  let L := fun (S : Subrepresentation A.representation) (C : Geometric.BlockRefinement B) =>
    repLength (T.normalizedRefinedJacquet B C (SmoothRep.subrepresentation A S).representation)
  have hL (S : Subrepresentation A.representation) (C : Geometric.BlockRefinement B)
      (hC : C ∈ s) : L S C ≤ b C :=
    (RefinedJacquetLengthProof.length_le T B C (SmoothRep.hom (SmoothRep.subtype A S))
      (SmoothRep.subtype_injective A S)).trans (hbound C hC)
  have hfinite (S : Subrepresentation A.representation) (C : Geometric.BlockRefinement B)
      (hC : C ∈ s) : L S C ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hL S C hC)
  have hmono (S U : Subrepresentation A.representation) (h : S ≤ U)
      (C : Geometric.BlockRefinement B) (hC : C ∈ s) :
      (L S C).toNat ≤ (L U C).toNat :=
    ENat.toNat_le_toNat (RefinedJacquetLengthProof.length_le T B C (inclusion A S U h)
      (Submodule.inclusion_injective h)) (hfinite U C hC)
  let measure := fun S : Subrepresentation A.representation => ∑ C ∈ s, (L S C).toNat
  have hmeasure_bound (S : Subrepresentation A.representation) :
      measure S ≤ ∑ C ∈ s, b C :=
    Finset.sum_le_sum fun C hC => ENat.toNat_le_of_le_natCast (hL S C hC)
  have hmeasure_strict : StrictMono measure := by
    intro S U hSU
    let D := SmoothRep.subquotient A U (lower A S U)
    have hD : SmoothRep.IsSubquotient D A := ⟨U, lower A S U, ⟨Iso.refl _⟩⟩
    have hnontrivial : Nontrivial D := quotient_nontrivial A S U hSU
    have hdetect : ∃ C ∈ s, Nontrivial (Geometric.RefinedJacquetModule B C D.representation) := by
      by_contra! hn
      have hz : Subsingleton D := hvanish D hD (by
        intro C hC
        exact hn C (by simp [s, hC]))
      exact not_nontrivial_iff_subsingleton.mpr hz hnontrivial
    obtain ⟨C, hC, hnonzero⟩ := hdetect
    have hpos : 0 < repLength (T.normalizedRefinedJacquet B C D.representation) :=
      repLength_pos_iff.mpr hnonzero
    have hadd := length_step T B C A S U hSU.le
    have hlt : L S C < L U C := by
      change L U C = L S C + repLength (T.normalizedRefinedJacquet B C D.representation) at hadd
      rw [hadd]
      simpa only [add_zero] using
        (ENat.add_lt_add_iff_left (hfinite S C hC)).mpr hpos
    have hnat : (L S C).toNat < (L U C).toNat := by
      have hcast : ((L S C).toNat : ℕ∞) < ((L U C).toNat : ℕ∞) := by
        simpa only [ENat.natCast_toNat (hfinite S C hC),
          ENat.natCast_toNat (hfinite U C hC)] using hlt
      exact_mod_cast hcast
    exact Finset.sum_lt_sum (fun C hC => hmono S U hSU.le C hC) ⟨C, hC, hnat⟩
  have hchain (m : ℕ) (c : Fin (m + 1) → Subrepresentation A.representation)
      (hc : StrictMono c) : m ≤ ∑ C ∈ s, b C := by
    let q := LTSeries.mk m (fun i => measure (c i)) (hmeasure_strict.comp hc)
    have h := q.head_add_length_le_nat
    have hb := hmeasure_bound (c (Fin.last m))
    change measure (c 0) + m ≤ measure (c (Fin.last m)) at h
    omega
  have hcomp := LengthCriterionProof.hasCompositionLengthAtMost_of_bound hchain
  exact (objectCompositionLengthCriterion ℂ (B.Levi F.Carrier)
    (Rep.of A.representation) (∑ C ∈ s, b C)).2 hcomp

end Langlands.CuspidalSupport
