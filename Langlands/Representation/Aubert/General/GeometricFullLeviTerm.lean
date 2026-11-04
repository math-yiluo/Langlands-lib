import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Aubert.General.SourceJacquetComparison
import Langlands.Representation.Aubert.General.Endpoint
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof

/-! # Actual geometric terms whose intersection Levis are full -/

noncomputable section

universe uI uG uV

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

section Algebra

variable {H : Type*} [Group H] {P M U : Subgroup H}

/-- Actual conjugation onto the target Levi makes the source intersection full. -/
theorem geometricSourceIntersection_eq_of_conjugation
    (A B : Subgroup H) (n : H)
    (hAB : ∀ x : H, x ∈ A ↔ n⁻¹ * x * n ∈ B) :
    geometricSourceIntersection A B n = B := by
  apply le_antisymm inf_le_left
  intro x hx
  refine ⟨hx, ?_⟩
  change x ∈ A.map (MulAut.conj n⁻¹).toMonoidHom
  rw [Subgroup.mem_map_equiv]
  simpa only [MulAut.conj_symm_apply, inv_inv] using
    (hAB (n * x * n⁻¹)).mpr (by simpa [mul_assoc] using hx)

/-- Actual conjugation onto the target Levi makes the target intersection full. -/
theorem geometricTargetIntersection_eq_of_conjugation
    (A B : Subgroup H) (n : H)
    (hAB : ∀ x : H, x ∈ A ↔ n⁻¹ * x * n ∈ B) :
    geometricTargetIntersection A B n = A := by
  apply le_antisymm inf_le_left
  intro x hx
  refine ⟨hx, ?_⟩
  change x ∈ B.map (MulAut.conj n).toMonoidHom
  rw [Subgroup.mem_map_equiv]
  exact (hAB x).mp hx

end Algebra

section Characters

variable {H : Type*} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [IsTopologicalGroup H]

private theorem fullLevi_normalizerCharacter_eq_one
    (U : Subgroup H) (hU : IsClosed (U : Set H)) (hbot : U = ⊥)
    (g : Subgroup.normalizer (U : Set H)) :
    HaarModulus.closedNormalizerCharacter U hU g = 1 := by
  let _ := hU.locallyCompactSpace
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  have : Subsingleton U := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj U g = ContinuousMulEquiv.refl U :=
    DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U g) = 1
  rw [he]
  simp

private theorem fullLevi_halfCharacter_eq_one
    (U : Subgroup H) (hU : IsClosed (U : Set H)) (hbot : U = ⊥)
    (M : Subgroup H) (hMU : M ≤ Subgroup.normalizer (U : Set H)) (m : M) :
    HaarModulus.closedHalfCharacter U hU M hMU m = 1 := by
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedNormalizerCharacter U hU ⟨m, hMU m.property⟩ : NNReal) : ℝ) : ℂ) = 1
  rw [fullLevi_normalizerCharacter_eq_one U hU hbot]
  simp

private theorem fullLevi_inverseHalfCharacter_eq_one
    (U : Subgroup H) (hU : IsClosed (U : Set H)) (hbot : U = ⊥)
    (M : Subgroup H) (hMU : M ≤ Subgroup.normalizer (U : Set H)) (m : M) :
    HaarModulus.closedInverseHalfCharacter U hU M hMU m = 1 := by
  apply Units.ext
  rw [show (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) =
      (((NNReal.sqrt
        (HaarModulus.closedNormalizerCharacter U hU ⟨m, hMU m.property⟩ : NNReal) : ℝ) : ℂ))⁻¹
    from Jacquet.inverseHalfCharacter_apply _ _]
  rw [fullLevi_normalizerCharacter_eq_one U hU hbot]
  simp

end Characters

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {M Q L N : Subgroup G}

/-- Jacquet restriction inside a coarse Levi is identity transport when
its intersection Levi is the entire coarse Levi. -/
def leviFullJacquetIso
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition
      (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hL : L = M)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    (leviNormalizedJacquetFunctor hM hLM h hN).obj A ≅
      (conjugationFunctor 1 (identityConjugationMembership hL.symm)).obj A := by
  subst L
  let _ := hM.locallyCompactSpace
  have htop : M.subgroupOf M = ⊤ := by ext x; simp
  have hbot : N.subgroupOf M = ⊥ :=
    h.unipotent_eq_bot_of_levi_eq_top htop
  have hNM : IsClosed ((N.subgroupOf M) : Set M) := hN.preimage continuous_subtype_val
  let e := endpointCoinvariantsEquiv (N.subgroupOf M) hbot A
  refine (SmoothRep.mkIso (Representation.Equiv.mk e ?_)) ≪≫
    (conjugationFunctorOneIso _ A).symm
  intro m
  ext q
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    A.representation (N.subgroupOf M) 1 q
  change e
      (((HaarModulus.closedInverseHalfCharacter (N.subgroupOf M)
        hNM (M.subgroupOf M)
        h.levi_le_normalizer ((subgroupOfContinuousEquiv hLM).symm m) : ℂˣ) : ℂ) •
          Jacquet.Localization.mk A.representation (N.subgroupOf M) 1
            (A.representation m v)) =
    A.representation m (e (Jacquet.Localization.mk A.representation (N.subgroupOf M) 1 v))
  rw [fullLevi_inverseHalfCharacter_eq_one (N.subgroupOf M) hNM hbot
    (M.subgroupOf M) h.levi_le_normalizer ((subgroupOfContinuousEquiv hLM).symm m)]
  simp only [Units.val_one, one_smul, e, endpointCoinvariantsEquiv_mk]

/-- Induction inside a coarse Levi is identity transport when its
intersection Levi is the entire coarse Levi. Its map is evaluation at one. -/
def leviFullInductionIso
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition
      (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hL : L = M)
    (A : SmoothRep.{0, uG, max uG uV} ℂ L) :
    (leviNormalizedInductionFunctor hM hLM h hN).obj A ≅
      (conjugationFunctor 1 (identityConjugationMembership hL)).obj A := by
  subst L
  let _ := hM.locallyCompactSpace
  have htop : M.subgroupOf M = ⊤ := by ext x; simp
  have hbot : N.subgroupOf M = ⊥ :=
    h.unipotent_eq_bot_of_levi_eq_top htop
  have hNM : IsClosed ((N.subgroupOf M) : Set M) := hN.preimage continuous_subtype_val
  have hQ : Q.subgroupOf M = ⊤ := top_unique (htop ▸ h.levi_le)
  refine SmoothRep.mkIso (Induction.smoothInducedTopEquiv (Q.subgroupOf M) hQ
    (inducingRepresentation h (hN.preimage continuous_subtype_val)
      ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM)).obj A))
    A.representation ?_ A.isSmooth) ≪≫
      (conjugationFunctorOneIso _ A).symm
  intro p
  ext v
  have hprojection : (h.projection p : M) = (p : M) := by
    have hm : (p : M) ∈ M.subgroupOf M := by rw [htop]; trivial
    exact congrArg Subtype.val (h.projection_levi ⟨p, hm⟩)
  change ((HaarModulus.closedHalfCharacter (N.subgroupOf M)
    hNM (Q.subgroupOf M) h.le_normalizer p : ℂˣ) : ℂ) •
      A.representation (subgroupOfContinuousEquiv hLM (h.projection p)) v =
    A.representation (p : M) v
  rw [fullLevi_halfCharacter_eq_one (N.subgroupOf M) hNM hbot
    (Q.subgroupOf M) h.le_normalizer p]
  simp only [Units.val_one, one_smul]
  exact congrArg (fun m => A.representation m v) hprojection

end Levi

section FullTerm

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
  (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- When the two actual Levis are conjugate by the chosen representative,
the actual normalized geometric term is that conjugation transport. -/
def geometricTermFullLeviIso (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hConj : ∀ x : G, x ∈ M I ↔ n⁻¹ * x * n ∈ M J)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) :
    (geometricTermFunctor P M U hM hU I J n hs ht).obj A ≅
      (conjugationFunctor n hConj).obj A := by
  let hS := geometricSourceIntersection_eq_of_conjugation (M I) (M J) n hConj
  let hT := geometricTargetIntersection_eq_of_conjugation (M I) (M J) n hConj
  let C := conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n)
  let T := geometricTargetInductionFunctor P M U hM hU I J n ht
  let S₁ := conjugationFunctor 1 (identityConjugationMembership hS.symm)
  let eS := leviFullJacquetIso (hM J) inf_le_left hs
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n) hS A
  let eT := leviFullInductionIso (hM I) inf_le_left ht
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)
    hT (C.obj (S₁.obj A))
  refine T.mapIso (C.mapIso eS) ≪≫ eT ≪≫ ?_
  refine SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) ?_)
  intro m
  ext v
  change A.representation _ v = A.representation _ v
  apply congrArg (fun x => A.representation x v)
  apply Subtype.ext
  change 1⁻¹ * (n⁻¹ * (1⁻¹ * (m : G) * 1) * n) * 1 = n⁻¹ * (m : G) * n
  simp only [inv_one, one_mul, mul_one]

end FullTerm

end Langlands.Aubert.General
