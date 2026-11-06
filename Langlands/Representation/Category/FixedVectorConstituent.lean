import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Smooth.FixedVectors.LawsProof

/-! # Irreducible detection of fixed vectors and finite class support

Retaining the cyclic generator in a maximal quotient preserves a given nonzero
fixed vector. No openness, compactness, admissibility or finite length is used.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- There is an actual irreducible subquotient with a nonzero fixed vector. -/
def HasFixedVectorConstituent (A : SmoothRep.{0, uG, uV} ℂ G)
    (H : Subgroup G) : Prop :=
  ∃ D : SmoothRep.{0, uG, uV} ℂ G,
    D.IsIrreducible ∧ IsSubquotient D A ∧ Nontrivial (fixedVectors D.representation H)

/-- A nonzero fixed vector survives in an irreducible quotient of its actual
cyclic subrepresentation, in the same carrier universe. -/
theorem hasFixedVectorConstituent_of_nontrivial
    (A : SmoothRep.{0, uG, uV} ℂ G) (H : Subgroup G)
    (hA : Nontrivial (fixedVectors A.representation H)) :
    HasFixedVectorConstituent A H := by
  classical
  have := hA
  obtain ⟨w, hw⟩ := exists_ne (0 : fixedVectors A.representation H)
  let v : A := w.val
  have hv : v ≠ 0 := fun hz => hw (Subtype.ext hz)
  let S := CompactSplitting.orbitSpan A.representation v
  have hvS : v ∈ S.toSubmodule := CompactSplitting.mem_orbitSpan_self _ v
  let B := subrepresentation A S
  let v' : B := ⟨v, hvS⟩
  have hv' : v' ≠ 0 := fun hz => hv (congrArg Subtype.val hz)
  have : Nontrivial B := ⟨⟨v', 0, hv'⟩⟩
  have hgen : ∀ T : Subrepresentation B.representation,
      (∀ x ∈ ({v'} : Finset B), x ∈ T) → T = ⊤ := by
    intro T hT
    have hvT : v' ∈ T := hT v' (Finset.mem_singleton_self v')
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ Submodule.span ℂ (Set.range fun g : G => A.representation g v) := hx
    refine Submodule.span_induction
      (p := fun x hx => (⟨x, hx⟩ : B) ∈ T) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨g, rfl⟩
      have he : (⟨A.representation g v, Submodule.subset_span ⟨g, rfl⟩⟩ : B) =
          B.representation g v' := rfl
      rw [he]
      exact T.apply_mem_toSubmodule g hvT
    · exact T.toSubmodule.zero_mem
    · intro y z hy hz ihy ihz
      exact T.toSubmodule.add_mem ihy ihz
    · intro a y hy ihy
      exact T.toSubmodule.smul_mem a ihy
  obtain ⟨T, hT⟩ :=
    CuspidalSupport.QuasicuspidalEmbedding.exists_isCoatom_subrepresentation
      B.representation {v'} hgen
  let D := quotient B T
  have hD : D.IsIrreducible :=
    CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom
      (hom (mkQ B T)) (mkQ_surjective B T) T hT
      (fun x => Submodule.Quotient.mk_eq_zero _)
  have hqv : hom (mkQ B T) v' ≠ 0 := by
    intro hz
    have hvT : v' ∈ T := (Submodule.Quotient.mk_eq_zero _).mp hz
    apply hT.1
    apply hgen T
    intro x hx
    have hx' : x = v' := Finset.mem_singleton.mp hx
    exact hx' ▸ hvT
  have hvH : v' ∈ fixedVectors B.representation H := by
    intro h
    apply Subtype.ext
    exact w.property h
  let z : fixedVectors D.representation H :=
    fixedVectorsMap (hom (mkQ B T)) H ⟨v', hvH⟩
  have hz : z ≠ 0 := fun he => hqv (congrArg Subtype.val he)
  exact ⟨D, hD, ⟨S, T, ⟨Iso.refl _⟩⟩, ⟨⟨z, 0, hz⟩⟩⟩

/-- A finite set of visible irreducible classes bounds the visible support of
arbitrary objects whose actual irreducible subquotients have their given class. -/
theorem finite_fixedVectorSupport_of_finite_constituent_classes
    {κ : Type uI} (A : κ → SmoothRep.{0, uG, uV} ℂ G) (H : Subgroup G)
    (Q : SmoothRep.{0, uG, uV} ℂ G → Prop)
    (c : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible → κ)
    (hblocks : ∀ i D hD, IsSubquotient D (A i) → Q D ∧ c D hD = i)
    (hfinite : Set.Finite {i | ∃ (D : SmoothRep.{0, uG, uV} ℂ G)
      (hD : D.IsIrreducible), Q D ∧ c D hD = i ∧
        Nontrivial (fixedVectors D.representation H)}) :
    Set.Finite {i | Nontrivial (fixedVectors (A i).representation H)} := by
  apply hfinite.subset
  intro i hi
  obtain ⟨D, hD, hDA, hfix⟩ := hasFixedVectorConstituent_of_nontrivial (A i) H hi
  obtain ⟨hQ, hc⟩ := hblocks i D hD hDA
  exact ⟨D, hD, hQ, hc, hfix⟩

end Langlands.SmoothRep
