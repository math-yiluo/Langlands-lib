import Langlands.LocalFactor.CommonClosureAbelianNormalBrauer
import Langlands.Representation.Finite.RelativeDegreeZeroBrauer
import Langlands.VirtualRepresentation.Weil.DegreeZeroReduction
import Langlands.VirtualRepresentation.Weil.ExactCoefficients

/-!
# Degree-zero Brauer induction relative to a normal subgroup, on actual Weil groups

Let `E` be a finite intermediate field in the common closure and `N` a normal
subgroup of the actual Weil subgroup `W_E` contained in inertia. A degree-zero
virtual representation spanned by classes of continuous representations on which
`N` acts trivially is an integral combination of inductions
`Ind_{W_L}^{W_E} (η - 1)` from Weil subgroups `W_L ⊇ N`, by continuous characters
`η` of `W_L` trivial on `N`. This is the Brauer step in the proofs of
Deligne--Henniart 1981, Lemmas 4.3 and 4.7, where `N` is a ramification group.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual inductions `Ind_{W_L}^{W_E} (η - 1)` from Weil subgroups containing `N`,
by continuous characters `η` of `W_L` that are trivial on `N`. -/
def relativeDegreeZeroInductionGenerators (E : Extension F) (N : Subgroup (weilSubgroup F E)) :
    Set (Virtual.{uF, uV} F E) :=
  {x | ∃ (L : Extension F) (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ)
      (hN : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L),
    (∀ n : N, η ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ = 1) ∧
    x = induce F E L h (ExactGrothendieckGroup.characterClass η -
      ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ))}

/-- The integral span of the classes of continuous representations of `W_E` on which
`N` acts trivially. -/
def weilTrivialOnSpan (E : Extension F) (N : Subgroup (weilSubgroup F E)) :
    Submodule ℤ (Virtual.{uF, uV} F E) :=
  Submodule.span ℤ {x | ∃ (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
      (hc : A.IsContinuous), (∀ n ∈ N, A.representation n = 1) ∧
      x = ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨A, hc⟩}

/-- Degree-zero Brauer induction relative to a normal subgroup `N` of inertia, on the
actual Weil subgroup `W_E`: a degree-zero class spanned by continuous representations
trivial on `N` lies in the span of the inductions `Ind_{W_L} (η - 1)` with `N ≤ W_L`
and `η` trivial on `N`. -/
def WeilRelativeDegreeZeroBrauerStatement : Prop :=
  ∀ (E : Extension F) (N : Subgroup (weilSubgroup F E)), N.Normal →
    N ≤ CommonClosureWeilDeligne.inertia F E →
    ∀ x ∈ weilTrivialOnSpan.{uF, uV} F E N, x ∈ DegreeZero.{uF, uV} F E →
      x ∈ Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)

/-- A character of `W_E` trivial on `N`, minus the trivial character, is a generator
(induction from `W_E` itself). -/
theorem characterClass_sub_one_mem (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (χ : weilSubgroup F E →ₜ* ℂˣ) (hχ : ∀ n ∈ N, χ n = 1) :
    ExactGrothendieckGroup.characterClass.{uF, max uF uV} χ -
        ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  apply Submodule.subset_span
  refine ⟨E, le_rfl, χ, fun n _ => n.2, fun n => hχ n n.2, ?_⟩
  rw [induce_self]
  rfl

/-- Twisting by a character trivial on `N` preserves the span of the generators. -/
theorem continuousTwist_mem_relativeSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (χ : weilSubgroup F E →ₜ* ℂˣ) (hχ : ∀ n ∈ N, χ n = 1) {x : Virtual.{uF, uV} F E}
    (hx : x ∈ Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)) :
    ExactGrothendieckGroup.continuousTwist χ x ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  have hle : Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) ≤
      (Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)).comap
        (ExactGrothendieckGroup.continuousTwist χ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨L, h, η, hN, hη, rfl⟩
    let χ' := χ.comp (weilInclusion F E L h)
    have hχ' : ∀ n : N, χ' ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ = 1 :=
      fun n => hχ _ n.2
    have e : ExactGrothendieckGroup.continuousTwist χ
        (induce F E L h (ExactGrothendieckGroup.characterClass η -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ))) =
        induce F E L h (ExactGrothendieckGroup.characterClass (χ' * η) -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)) -
        induce F E L h (ExactGrothendieckGroup.characterClass (χ' * 1) -
          ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)) := by
      rw [continuousTwist_induce, map_sub,
        ExactGrothendieckGroup.continuousTwist_characterClass,
        ExactGrothendieckGroup.continuousTwist_characterClass, ← map_sub]
      congr 1
      abel
    change ExactGrothendieckGroup.continuousTwist χ _ ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)
    rw [e]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨L, h, χ' * η, hN, fun n => ?_, rfl⟩)
      (Submodule.subset_span ⟨L, h, χ' * 1, hN, fun n => ?_, rfl⟩)
    · change χ' _ * η _ = 1
      rw [hχ' n, hη n, one_mul]
    · change χ' _ * 1 = 1
      rw [hχ' n, one_mul]
  exact hle hx

/-- Inflation from a finite quotient carries each generator of the finite relative
degree-zero span, for the image of `N`, into the span of the Weil generators. -/
theorem inflate_relativeGenerator_mem (E : Extension F) (N : Subgroup (weilSubgroup F E))
    {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    {x : FiniteRep.VirtualRep ℂ Q}
    (hx : x ∈ FiniteRep.relativeDegreeZeroGenerators Q (N.map π)) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ x ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  obtain ⟨S, hNS, χ, hχ, rfl⟩ := hx
  obtain ⟨L, hEL, hL⟩ := exists_extension_of_le F E U hUo (S.comap π) (fun w hw => by
    change π w ∈ S
    rw [hU w hw]
    exact S.one_mem)
  obtain ⟨η, hηv, hη⟩ := inflate_induce_oneDimensional_apply F E L hEL π hπ hsurj S hL χ
  obtain ⟨η₁, hη₁v, hη₁⟩ := inflate_induce_oneDimensional_apply F E L hEL π hπ hsurj S hL 1
  have hη₁1 : η₁ = 1 := ContinuousMonoidHom.ext fun w => by
    rw [hη₁v]
    rfl
  have hNL : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L := fun n hn =>
    (hL n).mp (hNS ⟨n, hn, rfl⟩)
  have e1 : ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
      (FiniteRep.ofClass (FiniteRep.induceHom S
        (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
      induce.{uF, uV} F E L hEL (ExactGrothendieckGroup.characterClass η) := hη
  have e2 : ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
      (FiniteRep.ofClass (FiniteRep.induceHom S
        (FiniteRep.classOf (FiniteRep.oneDimensional (1 : S →* ℂˣ))))) =
      induce.{uF, uV} F E L hEL (ExactGrothendieckGroup.characterClass η₁) := hη₁
  rw [FiniteRep.virtualInduce, map_sub, FiniteRep.virtualMap_ofClass,
    FiniteRep.virtualMap_ofClass, map_sub, e1, e2, hη₁1, ← map_sub]
  apply Submodule.subset_span
  refine ⟨L, hEL, η, hNL, fun n => ?_, rfl⟩
  rw [hηv]
  exact hχ ⟨π n, n, n.2, rfl⟩

/-- On a finite quotient of `W_E`, the finite relative degree-zero Brauer theorem for
the image of `N`, inflated back to `W_E`. -/
theorem inflate_mem_relativeSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    {x : FiniteRep.VirtualRep ℂ Q} (hx : x ∈ FiniteRep.trivialOnSpan Q (N.map π))
    (hx0 : x ∈ FiniteRep.degreeZeroVirtualReps Q) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ x ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  have hmem := FiniteRep.relativeDegreeZeroBrauer Q (N.map π)
    (Subgroup.Normal.map hN π hsurj) x hx hx0
  have hT : FiniteRep.relativeDegreeZeroSpan Q (N.map π) ≤
      (Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)).comap
        (ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ) :=
    Submodule.span_le.mpr fun x hx =>
      inflate_relativeGenerator_mem F E N π hπ hsurj U hUo hU hx
  exact hT hmem

/-- The coordinate model of a representation acts trivially wherever the
representation does. -/
theorem ofRepresentation_rho_eq_one {Q : Type uF} [Group Q] {X : Type*} [AddCommGroup X]
    [Module ℂ X] [Module.Finite ℂ X] (ρ : Representation ℂ Q X) {a : Q} (h : ρ a = 1) :
    (FiniteRep.ofRepresentation ρ).ρ a = 1 := by
  change ((Module.finBasis ℂ X).equivFun.conjRingEquiv.toMonoidHom.comp ρ) a = 1
  rw [MonoidHom.comp_apply, h, map_one]

/-- The trivial character line of a group acts trivially. -/
theorem oneDimensional_one_rho {Q : Type*} [Group Q] (a : Q) :
    (FiniteRep.oneDimensional (1 : Q →* ℂˣ)).ρ a = 1 := by
  refine LinearMap.ext fun v => ?_
  change ((1 : Q →* ℂˣ) a : ℂ) • v = v
  rw [MonoidHom.one_apply, Units.val_one, one_smul]

/-- For a representation trivial on `M`, the class `[ρ] - r · [1]` lies in the span of
the classes trivial on `M`. -/
theorem sub_mem_trivialOnSpan {Q : Type uF} [Group Q] (M : Subgroup Q) {X : Type*}
    [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X] (ρ : Representation ℂ Q X)
    (hρ : ∀ a ∈ M, ρ a = 1) (r : ℤ) :
    FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ) -
        r • FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional (1 : Q →* ℂˣ))) ∈
      FiniteRep.trivialOnSpan Q M :=
  Submodule.sub_mem _
    (Submodule.subset_span ⟨FiniteRep.ofRepresentation ρ,
      fun a ha => ofRepresentation_rho_eq_one ρ (hρ a ha), rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨FiniteRep.oneDimensional 1, fun a _ => oneDimensional_one_rho a, rfl⟩))

/-- The class `[ρ] - dim ρ · [1]` has degree zero. -/
theorem sub_finrank_mem_degreeZero {Q : Type uF} [Group Q] {X : Type*}
    [AddCommGroup X] [Module ℂ X] [Module.Finite ℂ X] (ρ : Representation ℂ Q X) :
    FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ) -
        (Module.finrank ℂ X : ℤ) •
          FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional (1 : Q →* ℂˣ))) ∈
      FiniteRep.degreeZeroVirtualReps Q := by
  simp only [FiniteRep.degreeZeroVirtualReps, LinearMap.mem_ker, FiniteRep.virtualDegree,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sub, map_zsmul,
    FiniteRep.virtualCharacter_ofClass, FiniteRep.character_classOfRepresentation,
    FiniteRep.character_classOf, FiniteRep.character_oneDimensional, Representation.char_one,
    MonoidHom.one_apply, Units.val_one]
  simp

/-- The finite-image case: for a continuous finite-image representation `B` on which
`N` acts trivially, `[B] - dim B · [1]` lies in the span of the generators. -/
theorem finiteImage_sub_mem_relativeSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hBc : B.IsContinuous) (hBf : B.HasFiniteImage)
    (hBN : ∀ n ∈ N, B.representation n = 1) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩ -
        (B.rank : ℤ) •
          ExactGrothendieckGroup.characterClass.{uF, max uF uV}
            (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_galois_kernel F E B hBc hBf
  have : U.Normal := hUn
  -- The finite quotient by the kernel of `B`.
  have hKo : IsOpen (B.representation.ker : Set (weilSubgroup F E)) :=
    Weil.open_kernel_of_finite_range_of_closed B.representation hBf
      (FiniteRepresentation.isClosed_ker_of_isContinuous B hBc)
  have hπeq : ∀ a b : weilSubgroup F E, B.representation a = B.representation b →
      QuotientGroup.mk' B.representation.ker a = QuotientGroup.mk' B.representation.ker b := by
    intro a b h
    apply QuotientGroup.eq.mpr
    change B.representation (a⁻¹ * b) = 1
    rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]
  have hfin : Finite (weilSubgroup F E ⧸ B.representation.ker) := by
    have : Finite (Set.range B.representation) := hBf.to_subtype
    have hmem : ∀ q : weilSubgroup F E ⧸ B.representation.ker,
        QuotientGroup.lift B.representation.ker B.representation le_rfl q ∈
          Set.range B.representation := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H w => exact ⟨w, rfl⟩
    refine Finite.of_injective (fun q => (⟨_, hmem q⟩ : Set.range B.representation)) ?_
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b => exact hπeq a b (congrArg Subtype.val h)
  let : Fintype (weilSubgroup F E ⧸ B.representation.ker) := Fintype.ofFinite _
  have hπ : IsOpen ((QuotientGroup.mk' B.representation.ker).ker :
      Set (weilSubgroup F E)) := by
    rw [QuotientGroup.ker_mk']
    exact hKo
  let ρ : Representation ℂ (weilSubgroup F E ⧸ B.representation.ker) B :=
    QuotientGroup.lift B.representation.ker B.representation le_rfl
  have hΦx : ExactGrothendieckGroup.inflate.{uF, uF, max uF uV}
      (QuotientGroup.mk' B.representation.ker) hπ
      (FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ) -
        (B.rank : ℤ) • FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional
          (1 : weilSubgroup F E ⧸ B.representation.ker →* ℂˣ)))) =
      ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩ -
        (B.rank : ℤ) •
          ExactGrothendieckGroup.characterClass.{uF, max uF uV}
            (1 : weilSubgroup F E →ₜ* ℂˣ) := by
    simp only [map_sub, map_zsmul, ExactGrothendieckGroup.inflate_ofClass]
    congr 2
    change ExactGrothendieckGroup.ofRepresentation _
      ⟨FiniteRepresentation.inflate _ (FiniteRep.ofRepresentation ρ), _⟩ = _
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact (FiniteRepresentation.inflateEquiv _ _ (FiniteRep.modelEquiv ρ).symm).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun g => LinearMap.ext fun v => rfl))
  rw [← hΦx]
  exact inflate_mem_relativeSpan F E N hN (QuotientGroup.mk' B.representation.ker) hπ
    (QuotientGroup.mk'_surjective _) U hUo
    (fun w hw => (QuotientGroup.eq_one_iff w).mpr (MonoidHom.mem_ker.mpr (hU w hw)))
    (sub_mem_trivialOnSpan _ ρ (by rintro _ ⟨n, hn, rfl⟩; exact hBN n hn) _)
    (sub_finrank_mem_degreeZero ρ)

/-- The finite-image case, for the reduced class. -/
theorem finiteImage_reduced_mem (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hBc : B.IsContinuous) (hBf : B.HasFiniteImage)
    (hBN : ∀ n ∈ N, B.representation n = 1) :
    Weil.reducedClass (weilSubgroup F E)
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩) ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  rw [Weil.reducedClass_apply, ExactGrothendieckGroup.degree_ofRepresentation]
  exact finiteImage_sub_mem_relativeSpan F E N hN B hBc hBf hBN

/-- The irreducible case, by the unramified twist to finite image. -/
theorem irreducible_reduced_mem (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (hNI : N ≤ CommonClosureWeilDeligne.inertia F E)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (hA : ∀ n ∈ N, A.representation n = 1) :
    Weil.reducedClass (weilSubgroup F E)
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨A, hc⟩) ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  obtain ⟨χ, B, hχ, hBc, hBf, ⟨e⟩⟩ := irreducible_finiteImage_unramifiedTwist F E A hc hi
  have hχN : ∀ n ∈ N, χ n = 1 := fun n hn => hχ n (hNI hn)
  -- On `N` the finite-image representation `B` is `A`, transported by `e`.
  have hBN : ∀ n ∈ N, B.representation n = 1 := by
    intro n hn
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective v
    have h := congrArg (fun f => f u) (e.isIntertwining' n)
    change e.toLinearEquiv (A.representation n u) =
      ((χ n : ℂˣ) : ℂ) • B.representation n (e.toLinearEquiv u) at h
    rw [hA n hn, hχN n hn, Units.val_one, one_smul, Module.End.one_apply] at h
    exact h.symm
  have hA' : ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E)
      ⟨A, hc⟩ = ExactGrothendieckGroup.continuousTwist χ
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩) := by
    change ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ =
      ExactGrothendieckGroup.twist χ.toMonoidHom _ _ _
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩)
    rw [ExactGrothendieckGroup.twist_ofRepresentation]
    exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ e
  rw [hA', Weil.reducedClass_continuousTwist]
  exact Submodule.add_mem _
    (continuousTwist_mem_relativeSpan F E N χ hχN (finiteImage_reduced_mem F E N hN B hBc hBf hBN))
    (Submodule.smul_mem _ _ (characterClass_sub_one_mem F E N χ hχN))

/-- A surjective intertwiner carries triviality at a group element to its target. -/
theorem eq_one_of_surjective_intertwiner {G : Type*} [Group G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (q : ρ.IntertwiningMap σ)
    (hq : Function.Surjective q) {g : G} (hg : ρ g = 1) : σ g = 1 := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := hq w
  rw [← q.isIntertwining, hg]
  rfl

/-- The general case, through an actual composition series. -/
theorem reducedClass_mem_of_trivialOn (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (hNI : N ≤ CommonClosureWeilDeligne.inertia F E)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hc : A.IsContinuous) (hA : ∀ n ∈ N, A.representation n = 1) :
    Weil.reducedClass (weilSubgroup F E)
        (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨A, hc⟩) ∈
      Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N) := by
  let A' : ContinuousObjects.{uF, max uF uV} (weilSubgroup F E) := ⟨A, hc⟩
  let s := Weil.ExactCoefficients.series A'
  have h : ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E)
      ⟨A, hc⟩ = ∑ i, ExactGrothendieckGroup.ofRepresentation _
        (continuousFiltrationGraded A' s i) :=
    Weil.exactClass_eq_sum_of_filtration A' s
  rw [h, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine irreducible_reduced_mem F E N hN hNI _ (continuousFiltrationGraded A' s i).property
    (Weil.ExactCoefficients.series_hasSimpleFactors A' i) fun n hn => ?_
  refine eq_one_of_surjective_intertwiner (s.gradedProjection i).hom
    (s.gradedProjection_surjective i) (LinearMap.ext fun v => Subtype.ext ?_)
  change A.representation n (v : A) = v
  rw [hA n hn]
  rfl

/-- Degree-zero Brauer induction relative to a normal subgroup of inertia, on the
actual Weil subgroup `W_E`. -/
theorem weilRelativeDegreeZeroBrauer : WeilRelativeDegreeZeroBrauerStatement.{uF, uV} F := by
  intro E N hN hNI x hx hx0
  have hle : weilTrivialOnSpan.{uF, uV} F E N ≤
      (Submodule.span ℤ (relativeDegreeZeroInductionGenerators.{uF, uV} F E N)).comap
        (Weil.reducedClass.{uF, max uF uV} (weilSubgroup F E)) := by
    rw [weilTrivialOnSpan, Submodule.span_le]
    rintro _ ⟨A, hc, hA, rfl⟩
    exact reducedClass_mem_of_trivialOn F E N hN hNI A hc hA
  have h := hle hx
  rw [Submodule.mem_comap, Weil.reducedClass_eq_self _ hx0] at h
  exact h

end Langlands.LocalFactor.CommonClosure
