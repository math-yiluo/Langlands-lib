import Langlands.LocalFactor.CommonClosureAbelianNormalBrauer

/-!
# Brauer induction relative to an abelian normal subgroup, with a kernel condition

Deligne--Henniart 1981, 2.3, in the form used in 4.5 and 4.8: there `V` is viewed as a
representation of the quotient `G` of `W` by the part of inertia acting trivially, so the
induced characters `χᵢ` of the subgroups `Hᵢ ⊆ G` are trivial on that part. This module
records that extra property for the actual Weil subgroup `W_E`: if a subgroup `K` of the
inertia of `W_E` acts trivially on `A`, the characters `η` can be taken trivial on
`K ∩ W_L`.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual inductions `Ind_{W_L}^{W_E} η` from Weil subgroups containing `N`, by continuous
characters `η` of `W_L` that are nontrivial on `N` and trivial on `K ∩ W_L`. -/
def kernelInductionGenerators (E : Extension F) (N K : Subgroup (weilSubgroup F E)) :
    Set (Virtual.{uF, uV} F E) :=
  {x | ∃ (L : Extension F) (h : E.field ≤ L.field) (η : weilSubgroup F L →ₜ* ℂˣ)
      (hN : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L),
    (∃ n : N, η ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ ≠ 1) ∧
    (∀ g : weilSubgroup F L, weilInclusion F E L h g ∈ K → η g = 1) ∧
    x = induce F E L h (ExactGrothendieckGroup.characterClass η)}

/-- Twisting by a character trivial on `N` and on `K` preserves the span. -/
theorem continuousTwist_mem_kernelSpan (E : Extension F) (N K : Subgroup (weilSubgroup F E))
    (χ : weilSubgroup F E →ₜ* ℂˣ) (hχ : ∀ n ∈ N, χ n = 1) (hχK : ∀ k ∈ K, χ k = 1)
    {x : Virtual.{uF, uV} F E}
    (hx : x ∈ Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K)) :
    ExactGrothendieckGroup.continuousTwist χ x ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) := by
  have hle : Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) ≤
      (Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K)).comap
        (ExactGrothendieckGroup.continuousTwist χ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨L, h, η, hN, ⟨n, hn⟩, hK, rfl⟩
    apply Submodule.subset_span
    refine ⟨L, h, χ.comp (weilInclusion F E L h) * η, hN, ⟨n, ?_⟩, ?_, ?_⟩
    · have h1 : χ ((weilInclusion F E L h)
          ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩) = 1 := hχ _ n.2
      change χ ((weilInclusion F E L h)
          ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩) *
        η ⟨((n : weilSubgroup F E) : localWeilGroup F), hN n n.2⟩ ≠ 1
      rw [h1, one_mul]
      exact hn
    · intro g hg
      change χ (weilInclusion F E L h g) * η g = 1
      rw [hχK _ hg, hK g hg, one_mul]
    · change ExactGrothendieckGroup.continuousTwist χ (induce F E L h _) = _
      rw [continuousTwist_induce, ExactGrothendieckGroup.continuousTwist_characterClass]
  exact hle hx

/-- Inflation from a finite quotient whose kernel contains `K` carries each generator of
the finite abelian normal Brauer span, for the image of `N`, into the span. -/
theorem inflate_kernelGenerator_mem (E : Extension F) (N K : Subgroup (weilSubgroup F E))
    {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (hK : ∀ k ∈ K, π k = 1)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    {x : FiniteRep.VirtualRep ℂ Q}
    (hx : x ∈ FiniteRep.abelianNormalBrauerGenerators Q (N.map π)) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ x ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) := by
  obtain ⟨S, hNS, χ, ⟨a, ha⟩, rfl⟩ := hx
  obtain ⟨L, hEL, hL⟩ := exists_extension_of_le F E U hUo (S.comap π) (fun w hw => by
    change π w ∈ S
    rw [hU w hw]
    exact S.one_mem)
  obtain ⟨η, hηv, hη⟩ := inflate_induce_oneDimensional_apply F E L hEL π hπ hsurj S hL χ
  have hNL : ∀ n ∈ N, (n : localWeilGroup F) ∈ weilSubgroup F L := fun n hn =>
    (hL n).mp (hNS ⟨n, hn, rfl⟩)
  apply Submodule.subset_span
  refine ⟨L, hEL, η, hNL, ?_, ?_, hη⟩
  · obtain ⟨n, hn, hna⟩ := a.2
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [hηv]
    convert ha using 2
    exact Subtype.ext hna
  · intro g hg
    rw [hηv]
    have h1 : π (Subgroup.inclusion (weilSubgroup_antitone F E L hEL) g) = 1 := hK _ hg
    have h2 : (⟨π (Subgroup.inclusion (weilSubgroup_antitone F E L hEL) g),
        (hL _).mpr g.2⟩ : S) = 1 := Subtype.ext h1
    rw [h2, map_one]

/-- On a finite quotient of `W_E` whose kernel contains `K`, the finite abelian normal
Brauer theorem for the image of `N`, inflated back to `W_E`. -/
theorem inflate_mem_kernelSpan (E : Extension F) (N K : Subgroup (weilSubgroup F E))
    (hN : N.Normal) {Q : Type uF} [Group Q] [Fintype Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (hK : ∀ k ∈ K, π k = 1)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hUo : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (hU : ∀ w : weilSubgroup F E, localProjection F w ∈ U → π w = 1)
    (hc : ∀ a ∈ N.map π, ∀ b ∈ N.map π, a * b = b * a)
    (V : FDRep ℂ Q) (hV : ∀ v : V, (∀ a ∈ N.map π, V.ρ a v = v) → v = 0) :
    ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
        (FiniteRep.ofClass (FiniteRep.classOf V)) ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) := by
  have hmem := FiniteRep.abelianNormalBrauer Q (N.map π) (Subgroup.Normal.map hN π hsurj) hc V hV
  have hT : FiniteRep.abelianNormalBrauerSpan Q (N.map π) ≤
      (Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K)).comap
        (ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ) :=
    Submodule.span_le.mpr fun x hx =>
      inflate_kernelGenerator_mem F E N K π hπ hsurj hK U hUo hU hx
  exact hT hmem

/-- The finite-image case: a continuous finite-image representation, trivial on `K`, on
which `N` acts through commuting operators without common nonzero fixed vectors. -/
theorem finiteImage_mem_kernelSpan (E : Extension F) (N K : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hBc : B.IsContinuous) (hBf : B.HasFiniteImage)
    (hBK : ∀ k ∈ K, B.representation k = 1)
    (hBcomm : ∀ a ∈ N, ∀ b ∈ N,
      B.representation a * B.representation b = B.representation b * B.representation a)
    (hBfix : ∀ v : B, (∀ n ∈ N, B.representation n v = v) → v = 0) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hBc⟩ ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_galois_kernel F E B hBc hBf
  have : U.Normal := hUn
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
  have hmem := inflate_mem_kernelSpan F E N K hN (QuotientGroup.mk' B.representation.ker)
    hπ (QuotientGroup.mk'_surjective _)
    (fun k hk => (QuotientGroup.eq_one_iff k).mpr (MonoidHom.mem_ker.mpr (hBK k hk))) U hUo
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

/-- Deligne--Henniart 2.3 on `W_E`, keeping the kernel: if moreover a subgroup `K` of
inertia acts trivially on `A`, the characters `η` can be chosen trivial on `K ∩ W_L`. -/
theorem weilAbelianNormalBrauer_kernel (E : Extension F) (N K : Subgroup (weilSubgroup F E))
    (hN : N.Normal) (hNI : N ≤ CommonClosureWeilDeligne.inertia F E)
    (hKI : K ≤ CommonClosureWeilDeligne.inertia F E)
    (A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hc : A.IsContinuous) (hi : A.IsIrreducible)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N,
      A.representation a * A.representation b = A.representation b * A.representation a)
    (hfix : ∀ v : A, (∀ n ∈ N, A.representation n v = v) → v = 0)
    (hK : ∀ k ∈ K, A.representation k = 1) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨A, hc⟩ ∈
      Submodule.span ℤ (kernelInductionGenerators.{uF, uV} F E N K) := by
  obtain ⟨χ, B, hχ, hBc, hBf, ⟨e⟩⟩ := irreducible_finiteImage_unramifiedTwist F E A hc hi
  -- On inertia the finite-image representation `B` is `A`, transported by `e`.
  have hBI : ∀ n ∈ CommonClosureWeilDeligne.inertia F E, ∀ v : A,
      e.toLinearEquiv (A.representation n v) = B.representation n (e.toLinearEquiv v) := by
    intro n hn v
    have h := congrArg (fun f => f v) (e.isIntertwining' n)
    change e.toLinearEquiv (A.representation n v) =
      ((χ n : ℂˣ) : ℂ) • B.representation n (e.toLinearEquiv v) at h
    rw [h, hχ n hn, Units.val_one, one_smul]
  have hBN : ∀ n ∈ N, ∀ v : A,
      e.toLinearEquiv (A.representation n v) = B.representation n (e.toLinearEquiv v) :=
    fun n hn => hBI n (hNI hn)
  have hBK : ∀ k ∈ K, B.representation k = 1 := by
    intro k hk
    ext v
    obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective v
    rw [← hBI k (hKI hk), hK k hk]
    rfl
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
  exact continuousTwist_mem_kernelSpan F E N K χ (fun n hn => hχ n (hNI hn))
    (fun k hk => hχ k (hKI hk))
    (finiteImage_mem_kernelSpan F E N K hN B hBc hBf hBK hBcomm hBfix)

end Langlands.LocalFactor.CommonClosure
