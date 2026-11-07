import Langlands.LocalFactor.CommonClosureFiniteQuotient
import Langlands.LocalFactor.CommonClosureInductionTwist
import Langlands.LocalFactor.CommonClosureIrreducibleReduction
import Langlands.LocalFactor.CommonClosureIntermediateWeil
import Langlands.Representation.Finite.AbelianNormalBrauer

/-!
# Brauer induction relative to an abelian normal subgroup, on actual Weil groups

Deligne--Henniart 1981, 2.3, on the actual Weil subgroup `W_E` of a finite
intermediate field `E` in the common closure. Let `N` be a normal subgroup contained
in inertia, and `A` a continuous irreducible representation such that the operators
`A(n)` for `n ∈ N` commute and have no common nonzero fixed vector. Then `[A]` is an
integral combination of inductions from Weil subgroups `W_L ⊇ N` of continuous
characters that are nontrivial on `N`.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual inductions `Ind_{W_L}^{W_E} η` from Weil subgroups containing `N`, by
continuous characters `η` of `W_L` that are nontrivial on `N`. -/
def abelianNormalInductionGenerators (E : Extension F) (N : Subgroup (weilSubgroup F E)) :
    Set (Virtual.{uF, uV} F E) :=
  {x | ∃ (L : Extension F) (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ)
      (hN : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L),
    (∃ n : N, η ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ ≠ 1) ∧
    x = induce F E L h (ExactGrothendieckGroup.characterClass η)}

/-- Deligne--Henniart 2.3 on the actual Weil subgroup `W_E`, for a normal subgroup `N`
of inertia acting through commuting operators without common nonzero fixed vectors. -/
def WeilAbelianNormalBrauerStatement : Prop :=
  ∀ (E : Extension F) (N : Subgroup (weilSubgroup F E)), N.Normal →
    N ≤ CommonClosureWeilDeligne.inertia F E →
    ∀ (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
      (hc : A.IsContinuous), A.IsIrreducible →
      (∀ a ∈ N, ∀ b ∈ N,
        A.representation a * A.representation b = A.representation b * A.representation a) →
      (∀ v : A, (∀ n ∈ N, A.representation n v = v) → v = 0) →
      ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨A, hc⟩ ∈
        Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N)

set_option backward.isDefEq.respectTransparency false in
/-- The irreducible finite-image reduction, keeping that the twisting character is
unramified: it is trivial on the inertia subgroup of `W_E`. -/
theorem irreducible_finiteImage_unramifiedTwist (E : Extension F)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) :
    ∃ (χ : weilSubgroup F E →ₜ* ℂˣ)
      (B : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E)),
      (∀ w ∈ CommonClosureWeilDeligne.inertia F E, χ w = 1) ∧
      B.IsContinuous ∧ B.HasFiniteImage ∧
        Nonempty (FiniteRepresentation.Equiv A
          (FiniteRepresentation.twist χ.toMonoidHom B)) := by
  let e : localWeilGroup E.asPadicField ≃ₜ* weilSubgroup F E :=
    intermediateWeilEquiv F E
  let A' := restrict e.toMulEquiv.toMonoidHom A
  have hc' : A'.IsContinuous :=
    isContinuous_restrict _ e.continuous hc
  have hi' : A'.IsIrreducible :=
    isIrreducible_restrict_of_surjective _ e.surjective A hi
  obtain ⟨z, B, hBc, _, hBf, _, ⟨he⟩⟩ :=
    ((localWeilIrreducibleReductionFor E.asPadicField) A' hc' hi').1
  let B' := restrict e.symm.toMulEquiv.toMonoidHom B
  let ei := toIntermediateLocalWeil F E
  let χ := (localUnramifiedCharacter E.asPadicField z).comp ei
  refine ⟨χ, B', ?_, isContinuous_restrict _ e.symm.continuous hBc, ?_, ?_⟩
  · intro w hw
    exact unramifiedCharacter_on_kernel _ z
      ((standaloneWeilEquiv_symm_mem_inertia F E w).mpr hw)
  · exact hBf.subset (Set.range_comp_subset_range e.symm B.representation)
  · refine ⟨{ toLinearEquiv := he.toLinearEquiv, isIntertwining' := ?_ }⟩
    intro g
    ext v
    have h := congrArg (fun f => f v) (he.isIntertwining' (e.symm g))
    change he (A.representation (e (e.symm g)) v) =
      ((FiniteRepresentation.twist χ.toMonoidHom B').representation g) (he v) at h
    simpa [FiniteRepresentation.twist, FiniteRepresentation.restrict,
      B', LinearMap.comp_apply, e.apply_symm_apply] using! h

/-- `inflate_induce_oneDimensional`, with the inflated character made explicit. -/
theorem inflate_induce_oneDimensional_apply (E L : Extension F) (h : E.field ≤ L.field)
    {Q : Type uF} [Group Q] [Finite Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (S : Subgroup Q)
    (hS : ∀ w : weilSubgroup F E, π w ∈ S ↔ (w : localWeilGroup F) ∈ weilSubgroup F L)
    (χ : S →* ℂˣ) :
    ∃ η : weilSubgroup F L →ₜ* ℂˣ,
      (∀ w : weilSubgroup F L,
        η w = χ ⟨π (Subgroup.inclusion (weilSubgroup_antitone F E L h) w), (hS _).mpr w.2⟩) ∧
      ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
          (FiniteRep.ofClass (FiniteRep.induce S
            (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
        induce.{uF, uV} F E L h (ExactGrothendieckGroup.characterClass η) := by
  let T := (weilSubgroup F L).subgroupOf (weilSubgroup F E)
  have hT : ∀ g, g ∈ T ↔ π g ∈ S := fun g => (hS g).symm
  let ι := Subgroup.inclusion (weilSubgroup_antitone F E L h)
  let ψ : weilSubgroup F L →* S := (π.comp ι).codRestrict S (fun w => (hS _).mpr w.2)
  have hψ : IsOpen ((χ.comp ψ).ker : Set (weilSubgroup F L)) := by
    have hι : IsOpen ((π.comp ι).ker : Set (weilSubgroup F L)) := by
      rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
      exact hπ.preimage (continuous_subtype_val.subtype_mk _)
    refine Subgroup.isOpen_mono ?_ hι
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    have : ψ w = 1 := Subtype.ext hw
    change χ (ψ w) = 1
    rw [this, map_one]
  let η : weilSubgroup F L →ₜ* ℂˣ := ⟨χ.comp ψ, Weil.continuous_of_open_kernel _ hψ⟩
  refine ⟨η, fun w => rfl, ?_⟩
  let ν := ContinuousMonoidHom.toContinuousMonoidHom (nestedWeilEquiv F E L h)
  have hP : ∀ A : FiniteRepresentation.{0, uF, max uF uV} ℂ T, A.IsContinuous →
      (FiniteRepresentation.induce T A).IsContinuous :=
    fun _ hA => FiniteRepresentation.isContinuous_induce _ (nestedWeil_open F E L) hA
  rw [ExactGrothendieckGroup.inflate_ofClass_induce π hπ hsurj S T hT hP
    (FiniteRep.oneDimensional χ)
    (FiniteRepresentation.restrict ν.toMonoidHom
      (FiniteRepresentation.characterLine.{uF, max uF uV} η.toMonoidHom))
    (FiniteRepresentation.isContinuous_restrict _ ν.continuous
      (FiniteRepresentation.characterLine_isContinuous η))
    (ULift.moduleEquiv : ULift.{max uF uV} ℂ ≃ₗ[ℂ] ℂ).symm (fun t v => rfl)]
  change _ = ExactGrothendieckGroup.induce T _ _ _
    (ExactGrothendieckGroup.restrict ν.toMonoidHom _ _ _
      (ExactGrothendieckGroup.ofRepresentation _ ⟨_, _⟩))
  rw [ExactGrothendieckGroup.restrict_ofRepresentation]

/-- Twisting by a character trivial on `N` preserves the span of the generators. -/
theorem continuousTwist_mem_abelianNormalSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (χ : weilSubgroup F E →ₜ* ℂˣ) (hχ : ∀ n ∈ N, χ n = 1) {x : Virtual.{uF, uV} F E}
    (hx : x ∈ Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N)) :
    ExactGrothendieckGroup.continuousTwist χ x ∈
      Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N) := by
  have hle : Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N) ≤
      (Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N)).comap
        (ExactGrothendieckGroup.continuousTwist χ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨L, h, η, hN, ⟨n, hn⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨L, h, χ.comp (weilInclusion F E L h) * η, hN, ⟨n, ?_⟩, ?_⟩
    · have h1 : χ ((weilInclusion F E L h)
          ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩) = 1 := hχ _ n.2
      change χ ((weilInclusion F E L h)
          ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩) *
        η ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ ≠ 1
      rw [h1, one_mul]
      exact hn
    · change ExactGrothendieckGroup.continuousTwist χ (induce F E L h _) = _
      rw [continuousTwist_induce, ExactGrothendieckGroup.continuousTwist_characterClass]
  exact hle hx

/-- Inflation from a finite quotient carries each generator of the finite abelian
normal Brauer span, for the image of `N`, into the span of the Weil generators. -/
theorem inflate_abelianNormalGenerator_mem (E : Extension F) (N : Subgroup (weilSubgroup F E))
    {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    {x : FiniteRep.VirtualRep ℂ Q}
    (hx : x ∈ FiniteRep.abelianNormalBrauerGenerators Q (N.map π)) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ x ∈
      Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N) := by
  obtain ⟨S, hNS, χ, ⟨a, ha⟩, rfl⟩ := hx
  obtain ⟨L, hEL, hL⟩ := exists_extension_of_le F E U hUo (S.comap π) (fun w hw => by
    change π w ∈ S
    rw [hU w hw]
    exact S.one_mem)
  obtain ⟨η, hηv, hη⟩ := inflate_induce_oneDimensional_apply F E L hEL π hπ hsurj S hL χ
  have hNL : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L := fun n hn =>
    (hL n).mp (hNS ⟨n, hn, rfl⟩)
  apply Submodule.subset_span
  refine ⟨L, hEL, η, hNL, ?_, hη⟩
  obtain ⟨n, hn, hna⟩ := a.2
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [hηv]
  convert ha using 2
  exact Subtype.ext hna

/-- On a finite quotient of `W_E`, the finite abelian normal Brauer theorem for the
image of `N`, inflated back to `W_E`. -/
theorem inflate_mem_abelianNormalSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    (hc : ∀ a ∈ N.map π, ∀ b ∈ N.map π, a * b = b * a)
    (V : FDRep ℂ Q) (hV : ∀ v : V, (∀ a ∈ N.map π, V.ρ a v = v) → v = 0) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
        (FiniteRep.ofClass (FiniteRep.classOf V)) ∈
      Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N) := by
  have hmem := FiniteRep.abelianNormalBrauer Q (N.map π) (Subgroup.Normal.map hN π hsurj) hc V hV
  have hT : FiniteRep.abelianNormalBrauerSpan Q (N.map π) ≤
      (Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N)).comap
        (ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ) :=
    Submodule.span_le.mpr fun x hx =>
      inflate_abelianNormalGenerator_mem F E N π hπ hsurj U hUo hU hx
  exact hT hmem

/-- The coordinate model of a representation without nonzero `M`-fixed vectors has none. -/
theorem ofRepresentation_fixed_eq_zero {Q : Type uF} [Group Q] {X : Type*} [AddCommGroup X]
    [Module ℂ X] [Module.Finite ℂ X] (ρ : Representation ℂ Q X) (M : Subgroup Q)
    (h : ∀ x : X, (∀ a ∈ M, ρ a x = x) → x = 0) (v : FiniteRep.ofRepresentation ρ)
    (hv : ∀ a ∈ M, (FiniteRep.ofRepresentation ρ).ρ a v = v) : v = 0 := by
  let m := FiniteRep.modelEquiv ρ
  obtain ⟨x, rfl⟩ := m.toLinearEquiv.surjective v
  have hx : x = 0 := h x (fun a ha => by
    apply m.toLinearEquiv.injective
    have h1 : m.toLinearEquiv (ρ a x) =
        (FiniteRep.ofRepresentation ρ).ρ a (m.toLinearEquiv x) :=
      LinearMap.congr_fun (m.isIntertwining' a) x
    rw [h1]
    exact hv a ha)
  rw [hx]
  exact map_zero m.toLinearEquiv

/-- The finite-image case: a continuous finite-image representation on which `N` acts
through commuting operators without common nonzero fixed vectors. -/
theorem finiteImage_mem_abelianNormalSpan (E : Extension F) (N : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hBc : B.IsContinuous) (hBf : B.HasFiniteImage)
    (hBcomm : ∀ a ∈ N, ∀ b ∈ N,
      B.representation a * B.representation b = B.representation b * B.representation a)
    (hBfix : ∀ v : B, (∀ n ∈ N, B.representation n v = v) → v = 0) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩ ∈
      Submodule.span ℤ (abelianNormalInductionGenerators.{uF, uV} F E N) := by
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
  have hc : ∀ a ∈ N.map (QuotientGroup.mk' B.representation.ker),
      ∀ b ∈ N.map (QuotientGroup.mk' B.representation.ker), a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact hπeq _ _ (by rw [map_mul, map_mul]; exact hBcomm a ha b hb)
  have hmem := inflate_mem_abelianNormalSpan F E N hN (QuotientGroup.mk' B.representation.ker)
    hπ (QuotientGroup.mk'_surjective _) U hUo
    (fun w hw => (QuotientGroup.eq_one_iff w).mpr (MonoidHom.mem_ker.mpr (hU w hw)))
    hc (FiniteRep.ofRepresentation ρ) (fun v hv => ofRepresentation_fixed_eq_zero ρ
      (N.map (QuotientGroup.mk' B.representation.ker))
      (fun x hx => hBfix x (fun n hn => hx _ ⟨n, hn, rfl⟩)) v hv)
  have hΦV : ExactGrothendieckGroup.inflate.{uF, uF, max uF uV}
      (QuotientGroup.mk' B.representation.ker) hπ
        (FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.ofRepresentation ρ))) =
      ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩ := by
    rw [ExactGrothendieckGroup.inflate_ofClass]
    change ExactGrothendieckGroup.ofRepresentation _
      ⟨FiniteRepresentation.inflate _ (FiniteRep.ofRepresentation ρ), _⟩ = _
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact (FiniteRepresentation.inflateEquiv _ _ (FiniteRep.modelEquiv ρ).symm).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun g => LinearMap.ext fun v => rfl))
  rw [← hΦV]
  exact hmem

/-- Deligne--Henniart 2.3 on the actual Weil subgroup `W_E`. -/
theorem weilAbelianNormalBrauer : WeilAbelianNormalBrauerStatement.{uF, uV} F := by
  intro E N hN hNI A hc hi hcomm hfix
  obtain ⟨χ, B, hχ, hBc, hBf, ⟨e⟩⟩ := irreducible_finiteImage_unramifiedTwist F E A hc hi
  -- On `N` the finite-image representation `B` is `A`, transported by `e`.
  have hBN : ∀ n ∈ N, ∀ v : A,
      e.toLinearEquiv (A.representation n v) = B.representation n (e.toLinearEquiv v) := by
    intro n hn v
    have h := congrArg (fun f => f v) (e.isIntertwining' n)
    change e.toLinearEquiv (A.representation n v) =
      ((χ n : ℂˣ) : ℂ) • B.representation n (e.toLinearEquiv v) at h
    rw [h, hχ n (hNI hn), Units.val_one, one_smul]
  have hBcomm : ∀ a ∈ N, ∀ b ∈ N,
      B.representation a * B.representation b = B.representation b * B.representation a := by
    intro a ha b hb
    ext v
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective v
    change B.representation a (B.representation b (e.toLinearEquiv u)) =
      B.representation b (B.representation a (e.toLinearEquiv u))
    rw [← hBN b hb, ← hBN a ha, ← hBN a ha, ← hBN b hb]
    congr 1
    exact congrArg (fun f => f u) (hcomm a ha b hb)
  have hBfix : ∀ v : B, (∀ n ∈ N, B.representation n v = v) → v = 0 := by
    intro v hv
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective v
    have hu : u = 0 := hfix u (fun n hn => e.toLinearEquiv.injective (by
      rw [hBN n hn]
      exact hv n hn))
    rw [hu]
    exact map_zero e.toLinearEquiv
  have hA : ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E)
      ⟨A, hc⟩ = ExactGrothendieckGroup.continuousTwist χ
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩) := by
    change ExactGrothendieckGroup.ofRepresentation _ ⟨A, hc⟩ =
      ExactGrothendieckGroup.twist χ.toMonoidHom _ _ _
        (ExactGrothendieckGroup.ofRepresentation _ ⟨B, hBc⟩)
    rw [ExactGrothendieckGroup.twist_ofRepresentation]
    exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ e
  rw [hA]
  exact continuousTwist_mem_abelianNormalSpan F E N χ (fun n hn => hχ n (hNI hn))
    (finiteImage_mem_abelianNormalSpan F E N hN B hBc hBf hBcomm hBfix)

end Langlands.LocalFactor.CommonClosure
