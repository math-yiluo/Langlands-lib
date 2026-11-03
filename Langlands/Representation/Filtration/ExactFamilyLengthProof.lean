import Langlands.Representation.Filtration.ExactFamilyLengthStatement
import Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Representation.Category.IrreducibleSubquotientExistence

/-! Finite-family detection bounds actual composition length. -/

noncomputable section
open CategoryTheory

namespace Langlands.ExactFamilyLength

universe uI uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An injective intertwiner cannot increase composition length. -/
theorem length_le_of_injective {H : Type uH} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uH, uV} ℂ H} (f : A ⟶ B)
    (hf : Function.Injective (SmoothRep.hom f)) :
    repLength A.representation ≤ repLength B.representation :=
  Module.length_le_of_injective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)) hf

/-- A nonzero actual subquotient has a nonzero ambient carrier. -/
theorem nontrivial_of_isSubquotient {H : Type uH} [Group H] [TopologicalSpace H]
    {A B : SmoothRep.{0, uH, uV} ℂ H} (hBA : SmoothRep.IsSubquotient B A)
    [Nontrivial B] : Nontrivial A := by
  classical
  by_contra hn
  have hA : Subsingleton A := not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hBA
  have hC : Subsingleton C := ⟨fun x y => hi (hA.elim _ _)⟩
  have hB : Subsingleton B := ⟨fun x y => by
    obtain ⟨x, rfl⟩ := hq x
    obtain ⟨y, rfl⟩ := hq y
    exact congrArg (SmoothRep.hom q) (hC.elim x y)⟩
  exact (not_nontrivial_iff_subsingleton.mpr hB) inferInstance

variable (A : SmoothRep.{0, uG, uV} ℂ G)

open Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof (lower)

/-- Inclusion between nested actual invariant subspaces. -/
def inclusion (S T : Subrepresentation A.representation) (hST : S ≤ T) :
    A.subrepresentation S ⟶ A.subrepresentation T :=
  SmoothRep.ofHom
    { toLinearMap := Submodule.inclusion hST
      isIntertwining' := fun _ => rfl }

theorem inclusion_injective (S T : Subrepresentation A.representation) (hST : S ≤ T) :
    Function.Injective (SmoothRep.hom (inclusion A S T hST)) :=
  Submodule.inclusion_injective hST

theorem inclusion_range (S T : Subrepresentation A.representation) (hST : S ≤ T) :
    LinearMap.range (SmoothRep.hom (inclusion A S T hST)).toLinearMap =
      LinearMap.ker (SmoothRep.hom ((A.subrepresentation T).mkQ (lower A S T))).toLinearMap := by
  change LinearMap.range (Submodule.inclusion hST) =
    LinearMap.ker (lower A S T).toSubmodule.mkQ
  rw [Submodule.ker_mkQ]
  ext v
  change (∃ w, Submodule.inclusion hST w = v) ↔ v.val ∈ S
  exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property,
    fun hv => ⟨⟨v.val, hv⟩, rfl⟩⟩

theorem quotient_nontrivial {S T : Subrepresentation A.representation} (hST : S < T) :
    Nontrivial ((A.subrepresentation T).quotient (lower A S T)) := by
  classical
  have hex : ∃ v ∈ T, v ∉ S := by
    by_contra h
    exact hST.not_ge fun v hv => by_contra fun hvS => h ⟨v, hv, hvS⟩
  obtain ⟨v, hvT, hvS⟩ := hex
  refine ⟨⟨Submodule.Quotient.mk (⟨v, hvT⟩ : T.toSubmodule), 0, ?_⟩⟩
  exact fun h => hvS ((Submodule.Quotient.mk_eq_zero (lower A S T).toSubmodule).mp h)

variable {ι : Type uI}
  {H : ι → Type uH} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  (F : ∀ i, SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ (H i))
  (hF : ∀ i, Derivative.Mirabolic.MapsShortExactIntertwiners (F i))

include hF in
/-- Irreducible detection suffices to detect every nonzero actual subquotient,
without assuming source finite length. -/
theorem detects_subquotients
    (hdet : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A → ∃ i, Nontrivial ((F i).obj D))
    (B : SmoothRep.{0, uG, uV} ℂ G) (hBA : SmoothRep.IsSubquotient B A)
    [Nontrivial B] : ∃ i, Nontrivial ((F i).obj B) := by
  obtain ⟨D, hD, hDB⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial B
  obtain ⟨i, hi⟩ := hdet D hD (smoothSubquotientTransitivity ℂ G A B D hDB hBA)
  let := hi
  exact ⟨i, nontrivial_of_isSubquotient
    (ExactSmoothTransport.map_isSubquotient (F i) (hF i) hDB)⟩

variable [Fintype ι]

include hF in
/-- Counting image lengths gives a bounded strictly monotone measure on the
actual invariant-subspace lattice. -/
theorem length_bound_of_detects_subquotients (b : ι → ℕ)
    (hb : ∀ i, repLength ((F i).obj A).representation ≤ (b i : ℕ∞))
    (hdet : ∀ B : SmoothRep.{0, uG, uV} ℂ G, SmoothRep.IsSubquotient B A →
      Nontrivial B → ∃ i, Nontrivial ((F i).obj B)) :
    HasCompositionLengthAtMost A.obj (∑ i, b i) := by
  classical
  let l (i : ι) (S : Subrepresentation A.representation) : ℕ∞ :=
    repLength ((F i).obj (A.subrepresentation S)).representation
  have hle (i : ι) (S : Subrepresentation A.representation) : l i S ≤ (b i : ℕ∞) :=
    (length_le_of_injective ((F i).map (A.subtype S))
      (ExactSmoothTransport.map_injective (F i) (hF i) _ (A.subtype_injective S))).trans (hb i)
  have hfin (i : ι) (S : Subrepresentation A.representation) : l i S ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hle i S)
  let μ (S : Subrepresentation A.representation) : ℕ := ∑ i, (l i S).toNat
  have hμb (S : Subrepresentation A.representation) : μ S ≤ ∑ i, b i :=
    Finset.sum_le_sum fun i _ => ENat.toNat_le_of_le_natCast (hle i S)
  have hμ : StrictMono μ := by
    intro S T hST
    let Q := (A.subrepresentation T).quotient (lower A S T)
    have hex (i : ι) := hF i (A.subrepresentation S) (A.subrepresentation T) Q
      (inclusion A S T hST.le) ((A.subrepresentation T).mkQ (lower A S T))
      (inclusion_injective A S T hST.le) ((A.subrepresentation T).mkQ_surjective _)
      (inclusion_range A S T hST.le)
    have hadd (i : ι) :
        l i T = l i S + repLength ((F i).obj Q).representation :=
      repLength_eq_add_of_exact
        (SmoothRep.hom ((F i).map (inclusion A S T hST.le)))
        (SmoothRep.hom ((F i).map ((A.subrepresentation T).mkQ (lower A S T))))
        (hex i).1 (hex i).2.2 (hex i).2.1
    have hqfin (i : ι) : repLength ((F i).obj Q).representation ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin i T) (by rw [hadd i]; exact le_add_self)
    have haddNat (i : ι) :
        (l i T).toNat = (l i S).toNat +
          (repLength ((F i).obj Q).representation).toNat := by
      rw [hadd i, ENat.toNat_add (hfin i S) (hqfin i)]
    have hm (i : ι) : (l i S).toNat ≤ (l i T).toNat := by
      rw [haddNat i]
      exact Nat.le_add_right _ _
    have hQA : SmoothRep.IsSubquotient Q A := ⟨T, lower A S T, ⟨Iso.refl _⟩⟩
    obtain ⟨i, hi⟩ := hdet Q hQA (quotient_nontrivial A hST)
    have hpos : 0 < (repLength ((F i).obj Q).representation).toNat :=
      ENat.toNat_pos (ne_of_gt (repLength_pos_iff.mpr hi)) (hqfin i)
    have hlt : (l i S).toNat < (l i T).toNat := by
      rw [haddNat i]
      omega
    exact Finset.sum_lt_sum (fun j _ => hm j) ⟨i, Finset.mem_univ i, hlt⟩
  apply LengthCriterionProof.hasCompositionLengthAtMost_of_bound
  intro m c hc
  have hmc : StrictMono (fun i => μ (c i)) := hμ.comp hc
  have hj : ∀ j : Fin (m + 1), j.val ≤ μ (c j) := by
    apply Fin.induction
    · exact Nat.zero_le _
    · intro i ih
      have hi := hmc (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      change i.val ≤ μ (c i.castSucc) at ih
      change μ (c i.castSucc) < μ (c i.succ) at hi
      change i.val + 1 ≤ μ (c i.succ)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hi)
  exact (hj (Fin.last m)).trans (hμb _)

end Langlands.ExactFamilyLength

namespace Langlands

theorem exactFamilyLengthBound.{uI, uG, uH, uV} :
    ExactFamilyLengthBoundStatement.{uI, uG, uH, uV} := by
  intro ι _ G _ _ H _ _ F hF A b hb hdet
  apply ExactFamilyLength.length_bound_of_detects_subquotients A F hF b hb
  intro B hBA hB
  let := hB
  exact ExactFamilyLength.detects_subquotients A F hF hdet B hBA

end Langlands
