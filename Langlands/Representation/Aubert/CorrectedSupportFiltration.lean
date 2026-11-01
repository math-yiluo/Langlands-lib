import Langlands.Representation.Aubert.BruhatSupportCore
import Langlands.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Geometric.ParabolicSupportJacquetProof

/-! Actual normalized induction support and Jacquet images for corrected Weyl cores. -/

noncomputable section

namespace Langlands.Aubert.Support

open GeneralLinear Geometric CategoryTheory

universe uF uV

section Quotient

variable {G : Type*} [Group G] (P Q : Subgroup G) (U : Set G)
    (hU : IsTwoSidedInvariant P Q U)

include hU in
theorem quotientMap_mem_image_iff (g : G) :
    Induction.quotientMap P g ∈ Induction.quotientMap P '' U ↔ g ∈ U := by
  constructor
  · rintro ⟨x, hx, heq⟩
    have hp : g * x⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact heq)
    have h := hU x hx (g * x⁻¹) hp 1 Q.one_mem
    simpa only [mul_one, inv_mul_cancel_right] using h
  · intro hg
    exact ⟨g, hg, rfl⟩

include hU in
theorem quotientSupport_right_invariant (q : Q) (x : Induction.LeftQuotient P)
    (hx : x ∈ Induction.quotientMap P '' U) :
    Induction.quotientRight P q x ∈ Induction.quotientMap P '' U := by
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨g * q, ?_, rfl⟩
  simpa only [one_mul] using hU g hg 1 P.one_mem q q.property

end Quotient

section Field

variable (F : Type uF) [Field F] {n : ℕ} (B C : BlockShape n)

/-- The corrected support as an actual subset of the inducing left quotient. -/
def correctedQuotientSupport (θ : Set (Equiv.Perm (Fin n))) :
    Set (Induction.LeftQuotient (B.parabolic F)) :=
  Induction.quotientMap (B.parabolic F) '' bruhatSupport F (weylSupport B C θ)

theorem quotientMap_mem_correctedQuotientSupport_iff
    (θ : Set (Equiv.Perm (Fin n))) (g : GeneralLinear n F) :
    Induction.quotientMap (B.parabolic F) g ∈ correctedQuotientSupport F B C θ ↔
      g ∈ bruhatSupport F (weylSupport B C θ) :=
  quotientMap_mem_image_iff _ _ _ (corrected_bruhatSupport_invariant F B C θ) g

theorem correctedQuotientSupport_right_invariant
    (θ : Set (Equiv.Perm (Fin n))) (q : C.parabolic F)
    (x : Induction.LeftQuotient (B.parabolic F))
    (hx : x ∈ correctedQuotientSupport F B C θ) :
    Induction.quotientRight (B.parabolic F) q x ∈ correctedQuotientSupport F B C θ :=
  quotientSupport_right_invariant _ _ _ (corrected_bruhatSupport_invariant F B C θ) q x hx

theorem correctedQuotientSupport_mono {θ η : Set (Equiv.Perm (Fin n))} (h : θ ⊆ η) :
    correctedQuotientSupport F B C θ ⊆ correctedQuotientSupport F B C η :=
  Set.image_mono (bruhatSupport_mono F (twoSidedCore_mono _ _ h))

@[simp] theorem correctedQuotientSupport_empty :
    correctedQuotientSupport F B C (∅ : Set (Equiv.Perm (Fin n))) = ∅ := by
  simp [correctedQuotientSupport, weylSupport]

@[simp] theorem correctedQuotientSupport_univ :
    correctedQuotientSupport F B C (Set.univ : Set (Equiv.Perm (Fin n))) = Set.univ := by
  ext x
  induction x using Quotient.inductionOn with
  | h g =>
    change Induction.quotientMap (B.parabolic F) g ∈
      correctedQuotientSupport F B C Set.univ ↔ True
    rw [quotientMap_mem_correctedQuotientSupport_iff]
    simp [weylSupport]

end Field

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- Actual normalized induction functions supported in the corrected core,
as a parabolic-stable subfunctor of restricted induction. -/
def correctedInductionSupport (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    RepSubfunctor
      (T.normalizedParabolicInductionFunctor.{uF,uV} B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F.Carrier).subtype) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (rawSmoothSupportSubfunctor
    (R := ℂ) (B.parabolic F.Carrier) (C.parabolic F.Carrier)
    (correctedQuotientSupport F.Carrier B C θ)
    (correctedQuotientSupport_right_invariant F.Carrier B C θ)).precomp
      (B.inducingFunctor (T.leviHalfCharacter B))

theorem mem_correctedInductionSupport_iff (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A (f : (T.normalizedParabolicInductionFunctor.{uF,uV} B).obj A),
      f ∈ (correctedInductionSupport T B C θ).obj A ↔
        ∀ g : GeneralLinear n F.Carrier,
          Induction.eval (B.parabolic F.Carrier)
            (B.inducingRepresentation (T.leviHalfCharacter B) A.representation) f g ≠ 0 →
            g ∈ bruhatSupport F.Carrier (weylSupport B C θ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A f
  exact forall_congr' fun g =>
    imp_congr_right fun _ => quotientMap_mem_correctedQuotientSupport_iff F.Carrier B C θ g

theorem correctedInductionSupport_mono {θ η : Set (Equiv.Perm (Fin n))}
    (h : θ ⊆ η) :
    letI := T.topology
    ∀ A, (correctedInductionSupport.{uF,uV} T B C θ).obj A ≤
      (correctedInductionSupport T B C η).obj A := by
  let := T.topology
  intro A f hf x hx
  exact correctedQuotientSupport_mono F.Carrier B C h (hf x hx)

theorem correctedInductionSupport_empty :
    letI := T.topology
    ∀ A, (correctedInductionSupport.{uF,uV} T B C ∅).obj A = ⊥ := by
  let := T.topology
  intro A
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_contra hx
    have h := hf x hx
    simp only [correctedQuotientSupport_empty, Set.notMem_empty] at h
  · exact bot_le

theorem correctedInductionSupport_univ :
    letI := T.topology
    ∀ A, (correctedInductionSupport.{uF,uV} T B C Set.univ).obj A = ⊤ := by
  let := T.topology
  intro A
  apply le_antisymm le_top
  intro f _ x _
  rw [correctedQuotientSupport_univ]
  trivial

/-- The actual image of the corrected support subspace in normalized Jacquet. -/
def correctedJacquetSupport (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    RepSubfunctor (jacquetInductionFunctor.{uF,uV} T B C) := by
  letI := T.topology
  exact parabolicJacquetImageSubfunctor T B C (correctedInductionSupport T B C θ)

theorem mem_correctedJacquetSupport_iff (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A (q : C.JacquetModule
      ((T.normalizedParabolicInductionFunctor.{uF,uV} B).obj A).representation),
      q ∈ (correctedJacquetSupport T B C θ).obj A ↔
        ∃ f : (T.normalizedParabolicInductionFunctor B).obj A,
          (∀ g : GeneralLinear n F.Carrier,
            Induction.eval (B.parabolic F.Carrier)
              (B.inducingRepresentation (T.leviHalfCharacter B) A.representation) f g ≠ 0 →
              g ∈ bruhatSupport F.Carrier (weylSupport B C θ)) ∧
          C.jacquetMk ((T.normalizedParabolicInductionFunctor B).obj A).representation f = q := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A q
  change (∃ f, f ∈ (correctedInductionSupport T B C θ).obj A ∧
    C.jacquetMk ((T.normalizedParabolicInductionFunctor B).obj A).representation f = q) ↔ _
  constructor
  · rintro ⟨f, hf, hq⟩
    exact ⟨f, (mem_correctedInductionSupport_iff T B C θ A f).mp hf, hq⟩
  · rintro ⟨f, hf, hq⟩
    exact ⟨f, (mem_correctedInductionSupport_iff T B C θ A f).mpr hf, hq⟩

theorem correctedJacquetSupport_eq_of_core_eq {θ η : Set (Equiv.Perm (Fin n))}
    (hcore : weylSupport B C θ = weylSupport B C η) :
    letI := T.topology
    correctedJacquetSupport.{uF,uV} T B C θ = correctedJacquetSupport T B C η := by
  let := T.topology
  unfold correctedJacquetSupport correctedInductionSupport correctedQuotientSupport
  congr 3
  rw [hcore]

theorem correctedJacquetSupport_mono {θ η : Set (Equiv.Perm (Fin n))}
    (h : θ ⊆ η) :
    letI := T.topology
    ∀ A, (correctedJacquetSupport.{uF,uV} T B C θ).obj A ≤
      (correctedJacquetSupport T B C η).obj A := by
  let := T.topology
  intro A
  exact C.normalizedJacquetImage_mono _ _
    (correctedInductionSupport_mono T B C h A)

theorem correctedJacquetSupport_empty :
    letI := T.topology
    ∀ A, (correctedJacquetSupport.{uF,uV} T B C ∅).obj A = ⊥ := by
  let := T.topology
  intro A
  change C.normalizedJacquetImage _ _ _ = ⊥
  rw [correctedInductionSupport_empty, C.normalizedJacquetImage_bot]

theorem correctedJacquetSupport_univ :
    letI := T.topology
    ∀ A, (correctedJacquetSupport.{uF,uV} T B C Set.univ).obj A = ⊤ := by
  let := T.topology
  intro A
  change C.normalizedJacquetImage _ _ _ = ⊤
  rw [correctedInductionSupport_univ, C.normalizedJacquetImage_top]

/-- The quotient of the two actual corrected support images is the normalized
Jacquet module of the actual support quotient, naturally in the inducing object. -/
def correctedSupportQuotientIso {θ η : Set (Equiv.Perm (Fin n))} (h : θ ⊆ η) :
    letI := T.topology
    (correctedJacquetSupport.{uF,uV} T B C θ).quotientFunctor
        (correctedJacquetSupport T B C η) ≅
      (correctedInductionSupport T B C θ).quotientFunctor
          (correctedInductionSupport T B C η) ⋙
        Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C) := by
  letI := T.topology
  exact supportImageQuotientIso T B C
    (correctedInductionSupport T B C θ) (correctedInductionSupport T B C η)
    (correctedInductionSupport_mono T B C h)

/-- Any increasing empty-to-full chain of Weyl supports gives an actual
corrected Jacquet support filtration. Openness is a separate obligation. -/
def correctedJacquetFiltration {m : ℕ}
    (θ : Fin (m + 1) → Set (Equiv.Perm (Fin n)))
    (hmono : Monotone θ) (hzero : θ 0 = ∅) (htop : θ (Fin.last m) = Set.univ) :
    letI := T.topology
    RepFunctorFiltration (jacquetInductionFunctor.{uF,uV} T B C) m := by
  letI := T.topology
  exact {
    step k := correctedJacquetSupport T B C (θ k)
    monotone A := fun i j hij => correctedJacquetSupport_mono T B C (hmono hij) A
    zero A := by rw [hzero]; exact correctedJacquetSupport_empty T B C A
    top A := by rw [htop]; exact correctedJacquetSupport_univ T B C A }

end Padic
end Langlands.Aubert.Support
