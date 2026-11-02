import Langlands.Representation.Derivative.MirabolicPairingLevelComparison
import Langlands.Representation.Filtration.InvariantBilinearSmoothDual
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Group.GL.CompactOpen

/-! # Actual constituents and smooth-dual quotients of highest derivatives -/

noncomputable section

namespace Langlands

universe uF uG uV uW

namespace InvariantBilinear

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual left constituent and right quotient obtained from an invariant
left-separating form, retaining that form and the quotient's evaluation formula. -/
structure ConstituentDualQuotientData
    (A : SmoothRep.{0, uG, uV} ℂ G) (B : SmoothRep.{0, uG, uW} ℂ G) where
  constituent : Subrepresentation A.representation
  irreducible : (SmoothRep.subrepresentation A constituent).IsIrreducible
  admissible : (SmoothRep.subrepresentation A constituent).IsAdmissible
  form : forms A.representation B.representation (fun _ => 1)
  separatingLeft : form.val.SeparatingLeft
  quotient : B.representation.IntertwiningMap
    (smoothContragredient (SmoothRep.subrepresentation A constituent).representation)
  surjective : Function.Surjective quotient
  quotient_apply : ∀ (w : B) (x : SmoothRep.subrepresentation A constituent),
    (quotient w).val x = form.val x.val w

end InvariantBilinear

private theorem existsIrreducibleSubrepresentation
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : Nontrivial A) (hfinite : A.HasFiniteLength) :
    ∃ S : Subrepresentation A.representation,
      (SmoothRep.subrepresentation A S).IsIrreducible := by
  let := hA
  let : Nontrivial A.representation.asModule :=
    A.representation.asModuleEquiv.toEquiv.nontrivial
  let : IsArtinian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
  obtain ⟨N, hN, _⟩ :=
    (eq_bot_or_exists_atom_le (⊤ : Submodule (MonoidAlgebra ℂ G)
      A.representation.asModule)).resolve_left top_ne_bot
  let S : Subrepresentation A.representation := Subrepresentation.ofSubmodule' N
  let j : (SmoothRep.subrepresentation A S).representation.asModule →ₗ[MonoidAlgebra ℂ G] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom (SmoothRep.subtype A S))).codRestrict N (fun v => v.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  refine ⟨S, (Representation.irreducible_iff_isSimpleModule_asModule _).mpr ?_⟩
  exact (j.isSimpleModule_iff_of_bijective hj).mpr (isSimpleModule_iff_isAtom.mpr hN)

namespace Derivative.Mirabolic

open GeneralLinear HarmonicAnalysis

open scoped NNReal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Choose an actual irreducible constituent of a finite-length highest left
derivative, together with an actual quotient of the right derivative onto its
smooth contragredient. Only the first input is assumed highest. -/
def chooseHighestDerivativeConstituentQuotient (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier)),
      Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj A) →
      ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).HasFiniteLength →
      (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
        Subsingleton ((mirabolicDerivativeOfOrder T ψ N j hj).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        InvariantBilinear.ConstituentDualQuotientData
          ((mirabolicDerivativeOfOrder T ψ N k hk).obj A)
          ((mirabolicDerivativeOfOrder T ψ N k hk).obj B) := by
  letI := T.topology
  intro A B hA hfinite hhigh β hβ
  letI := T.generalLinearTopologicalGroup (N + 1 - k)
  let DA := (mirabolicDerivativeOfOrder T ψ N k hk).obj A
  let DB := (mirabolicDerivativeOfOrder T ψ N k hk).obj B
  let γ := chooseHighestDerivativePairing T ψ N k hk A B hA hhigh β hβ
  let S := Classical.choose (existsIrreducibleSubrepresentation DA hA hfinite)
  have hS : (SmoothRep.subrepresentation DA S).IsIrreducible :=
    Classical.choose_spec (existsIrreducibleSubrepresentation DA hA hfinite)
  have hadm : (SmoothRep.subrepresentation DA S).IsAdmissible :=
    (CuspidalSupport.cuspidalEmbedding F T (N + 1 - k)
      (SmoothRep.subrepresentation DA S) hS).1
  have hcofinal : ∀ H : OpenSubgroup (GeneralLinear (N + 1 - k) F.Carrier),
      ∃ K : OpenSubgroup (GeneralLinear (N + 1 - k) F.Carrier),
        IsCompact (K : Set (GeneralLinear (N + 1 - k) F.Carrier)) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := T.generalLinearCompactOpen (N + 1 - k)
      (H : Set _) (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  let q := InvariantBilinear.smoothDualQuotientOfLeftEmbedding hcofinal hadm hS
    DB.isSmooth (SmoothRep.hom (SmoothRep.subtype DA S))
    (SmoothRep.subtype_injective DA S) γ.val γ.property
  exact
    { constituent := S
      irreducible := hS
      admissible := hadm
      form := γ.val
      separatingLeft := γ.property
      quotient := q.val
      surjective := q.property
      quotient_apply := fun _ _ => rfl }

end Derivative.Mirabolic

end Langlands
