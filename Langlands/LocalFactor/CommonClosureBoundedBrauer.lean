import Langlands.LocalFactor.CommonClosureFiniteQuotient
import Langlands.Representation.Finite.BrauerTheoryProof
import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.VirtualRepresentation.Weil.ExactRealization

/-!
# Brauer induction for local Weil representations trivial on a Weil subgroup

Let `N` be an open normal subgroup of finite index of the actual local Weil
group `W_F` of a p-adic field `F`. Every continuous representation of `W_F` that
is trivial on `N` has an exact class in the integral span of the inductions
`Ind_{W_L}^{W_F} η`, where `L` is a finite extension of `F` in the common
algebraic closure with `N ⊆ W_L` and `η` is a continuous character of `W_L`
trivial on `N`. The proof inflates the integral Brauer spanning theorem from the
finite quotient `W_F / N`.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every open subgroup of finite index of `W_F` contains the elements of `W_F`
whose Galois projection lies in some open normal subgroup of the absolute
Galois group. -/
theorem exists_open_normal_le (N : Subgroup (localWeilGroup F))
    (hN : IsOpen (N : Set (localWeilGroup F))) [N.FiniteIndex] :
    ∃ U : Subgroup (Field.absoluteGaloisGroup F.Carrier), U.Normal ∧
      IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)) ∧
      ∀ w : localWeilGroup F, localProjection F w ∈ U → w ∈ N := by
  -- The permutation representation on `W_F ⧸ N` is continuous with finite image.
  let R := Representation.ofMulAction ℂ (localWeilGroup F) (localWeilGroup F ⧸ N)
  let A : LocalWeilRepresentation.{uF, uF} F := FiniteRepresentation.of R
  have hcore : IsOpen (N.normalCore : Set (localWeilGroup F)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (N.normalCore_isClosed (N.isClosed_of_isOpen hN))
  have hRcore : N.normalCore ≤ R.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext fun r => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, Module.End.one_apply, R,
      Representation.ofMulAction_single]
    congr 1
    change ((n * g : localWeilGroup F) : localWeilGroup F ⧸ N) = g
    rw [QuotientGroup.eq]
    have h : g⁻¹ * n * g⁻¹⁻¹ ∈ N := hn g⁻¹
    rw [inv_inv] at h
    have h' := N.inv_mem h
    simpa [mul_assoc] using h'
  have hAc : A.IsContinuous :=
    FiniteRepresentation.isContinuous_of_le_ker A N.normalCore hcore
      (fun n hn => hRcore hn)
  have hAf : A.HasFiniteImage := by
    refine (Set.finite_range (QuotientGroup.lift N.normalCore R hRcore)).subset ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  -- Its Galois realization has open kernel.
  obtain ⟨τ, ⟨hτc, hτr⟩, -⟩ := (localWeilGaloisTypeFor.{uF, uF} F A).2 hAc hAf
  let := LocalClassField.absoluteGaloisNonarchimedean F.Carrier
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  refine ⟨τ.ker, MonoidHom.normal_ker τ,
    Weil.open_kernel_of_continuous_nonarchimedean_representation τ
      ((FiniteRepresentation.isContinuous_of_iff τ).mp hτc), ?_⟩
  intro w hw
  have hRw : R w = 1 := by
    change A.representation w = 1
    rw [← hτr]
    exact (MonoidHom.mem_ker).mp hw
  have h1 := congrArg (fun T => T (MonoidAlgebra.single ((1 : localWeilGroup F) :
    localWeilGroup F ⧸ N) (1 : ℂ))) hRw
  simp only [R, Representation.ofMulAction_single, Module.End.one_apply] at h1
  have h2 := MonoidAlgebra.single_left_injective (one_ne_zero (α := ℂ)) h1
  change (((w : localWeilGroup F) * 1 : localWeilGroup F) : localWeilGroup F ⧸ N) =
    ((1 : localWeilGroup F) : localWeilGroup F ⧸ N) at h2
  rw [QuotientGroup.eq] at h2
  simpa using h2

/-- A subgroup of `W_F` containing every element whose Galois projection lies in
an open normal subgroup `U` is the actual Weil subgroup of a finite intermediate
field fixed by `U`. -/
theorem exists_extension_eq (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (H : Subgroup (localWeilGroup F))
    (hH : ∀ w : localWeilGroup F, localProjection F w ∈ U → w ∈ H) :
    ∃ L : Extension F, L.field ≤ IntermediateField.fixedField U ∧ weilSubgroup F L = H := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let P : localWeilGroup F →* Field.absoluteGaloisGroup F.Carrier :=
    (localProjection F).toMonoidHom
  -- The Galois image of `H`, enlarged by `U`, is an open subgroup.
  let K := H.map P ⊔ U
  have hKo : IsOpen (K : Set (Field.absoluteGaloisGroup F.Carrier)) :=
    Subgroup.isOpen_mono le_sup_right hU
  let Kc : ClosedSubgroup (Field.absoluteGaloisGroup F.Carrier) :=
    ⟨K, K.isClosed_of_isOpen hKo⟩
  let L1 := IntermediateField.fixedField K
  have hL1 : L1.fixingSubgroup = K := InfiniteGalois.fixingSubgroup_fixedField Kc
  have : FiniteDimensional F.Carrier L1 :=
    (InfiniteGalois.isOpen_iff_finite L1).mp (by rw [hL1]; exact hKo)
  refine ⟨⟨L1, inferInstance⟩, IntermediateField.fixedField_le le_sup_right, ?_⟩
  ext w
  change localProjection F w ∈ L1.fixingSubgroup ↔ w ∈ H
  rw [hL1]
  constructor
  · intro hwK
    obtain ⟨_, ⟨h, hh, rfl⟩, u, hu, huw⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := H.map P) (t := U)).mp hwK
    have hu' : localProjection F (h⁻¹ * w) ∈ U := by
      have heq : localProjection F (h⁻¹ * w) = u := by
        change P (h⁻¹ * w) = u
        rw [map_mul, map_inv]
        change (P h)⁻¹ * localProjection F w = u
        rw [← huw]
        exact inv_mul_cancel_left (G := Field.absoluteGaloisGroup F.Carrier) (P h) u
      rw [heq]
      exact hu
    simpa using H.mul_mem hh (hH _ hu')
  · intro hw
    exact Subgroup.mem_sup_left ⟨w, hw, rfl⟩

/-- Inflating, from a finite quotient of `W_F`, the induction of a character of a
subgroup `S` whose preimage is `W_L` gives the induction to `W_F` of a continuous
character of `W_L` that is trivial on the kernel of the quotient map. -/
theorem inflate_induce_oneDimensional_weil (L : Extension F)
    {Q : Type uF} [Group Q] [Finite Q] (π : localWeilGroup F →* Q)
    (hπ : IsOpen (π.ker : Set (localWeilGroup F))) (hsurj : Function.Surjective π)
    (S : Subgroup Q)
    (hS : ∀ w : localWeilGroup F, π w ∈ S ↔ w ∈ weilSubgroup F L)
    (χ : S →* ℂˣ) :
    ∃ η : weilSubgroup F L →ₜ* ℂˣ,
      (∀ w : weilSubgroup F L, π w = 1 → η w = 1) ∧
      ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
          (FiniteRep.ofClass (FiniteRep.induce S
            (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
        ExactGrothendieckGroup.continuousInduce (weilSubgroup F L) (weilSubgroup_open F L)
          (ExactGrothendieckGroup.characterClass.{uF, uV} η) := by
  let T := weilSubgroup F L
  let ψ : T →* S := (π.comp T.subtype).codRestrict S (fun w => (hS _).mpr w.2)
  have hψ : IsOpen ((χ.comp ψ).ker : Set T) := by
    have hι : IsOpen ((π.comp T.subtype).ker : Set T) := by
      rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
      exact hπ.preimage continuous_subtype_val
    refine Subgroup.isOpen_mono ?_ hι
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    have : ψ w = 1 := Subtype.ext hw
    change χ (ψ w) = 1
    rw [this, map_one]
  let η : T →ₜ* ℂˣ := ⟨χ.comp ψ, Weil.continuous_of_open_kernel _ hψ⟩
  refine ⟨η, fun w hw => ?_, ?_⟩
  · have : ψ w = 1 := Subtype.ext hw
    change χ (ψ w) = 1
    rw [this, map_one]
  · have hP : ∀ A : FiniteRepresentation.{0, uF, uV} ℂ T, A.IsContinuous →
        (FiniteRepresentation.induce T A).IsContinuous :=
      fun _ hA => FiniteRepresentation.isContinuous_induce _ (weilSubgroup_open F L) hA
    rw [ExactGrothendieckGroup.inflate_ofClass_induce π hπ hsurj S T (fun g => (hS g).symm) hP
      (FiniteRep.oneDimensional χ)
      (FiniteRepresentation.characterLine.{uF, uV} η.toMonoidHom)
      (FiniteRepresentation.characterLine_isContinuous η)
      (ULift.moduleEquiv : ULift.{uV} ℂ ≃ₗ[ℂ] ℂ).symm (fun t v => rfl)]
    rfl

/-- The inductions to `W_F` of continuous characters `η` of Weil subgroups `W_L`
containing a given subgroup `N` of `W_F`, with `η` trivial on `N`. They are
classes in the exact Grothendieck group of continuous representations of `W_F`. -/
def inducedCharacterClassesAbove (N : Subgroup (localWeilGroup F)) :
    Set (LocalWeil.ContinuousExactGroup.{uF, max uF uV} F) :=
  {x | ∃ (L : Extension F) (_ : N ≤ weilSubgroup F L) (η : weilSubgroup F L →ₜ* ℂˣ),
    (∀ w : weilSubgroup F L, (w : localWeilGroup F) ∈ N → η w = 1) ∧
    x = ExactGrothendieckGroup.continuousInduce (weilSubgroup F L) (weilSubgroup_open F L)
      (ExactGrothendieckGroup.characterClass.{uF, uV} η)}

/-- Brauer induction for `W_F / N`: for an open normal subgroup `N` of finite
index of `W_F`, every continuous representation of `W_F` trivial on `N` has an
exact class in the integral span of `inducedCharacterClassesAbove F N`. -/
theorem ofRepresentation_mem_span_inducedCharacterClassesAbove
    (N : Subgroup (localWeilGroup F)) (hN : IsOpen (N : Set (localWeilGroup F)))
    [N.Normal] [N.FiniteIndex]
    (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F)) (hc : B.IsContinuous)
    (hB : ∀ w ∈ N, B.representation w = 1) :
    ExactGrothendieckGroup.ofRepresentation
        (fun A : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F) => A.IsContinuous)
        ⟨B, hc⟩ ∈
      Submodule.span ℤ (inducedCharacterClassesAbove.{uF, uV} F N) := by
  obtain ⟨U, hUn, hUo, hUN⟩ := exists_open_normal_le F N hN
  have : U.Normal := hUn
  -- The finite quotient `W_F ⧸ N`.
  let Q := localWeilGroup F ⧸ N
  have : Finite Q := Subgroup.finite_quotient_of_finiteIndex
  let : Fintype Q := Fintype.ofFinite Q
  let π : localWeilGroup F →* Q := QuotientGroup.mk' N
  have hπ : IsOpen (π.ker : Set (localWeilGroup F)) := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  let ρ : Representation ℂ Q B :=
    QuotientGroup.lift N B.representation (fun w hw => (MonoidHom.mem_ker).mpr (hB w hw))
  let Φ := ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
  have hΦ : Φ (FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ)) =
      ExactGrothendieckGroup.ofRepresentation
        (fun A : FiniteRepresentation.{0, uF, max uF uV} ℂ (localWeilGroup F) => A.IsContinuous)
        ⟨B, hc⟩ := by
    simp only [Φ, ExactGrothendieckGroup.inflate_ofClass]
    change ExactGrothendieckGroup.ofRepresentation _
      ⟨FiniteRepresentation.inflate π (FiniteRep.ofRepresentation ρ), _⟩ = _
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact (FiniteRepresentation.inflateEquiv π _ (FiniteRep.modelEquiv ρ).symm).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun g => LinearMap.ext fun v => rfl))
  -- Integral Brauer spanning in the finite quotient.
  let gen : FiniteRep.MonomialDatum ℂ Q → FiniteRep.VirtualRep ℂ Q := fun d =>
    FiniteRep.ofClass (FiniteRep.induce d.1 (FiniteRep.classOf (FiniteRep.oneDimensional d.2)))
  have hx : FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ) ∈
      Submodule.span ℤ (Set.range gen) := by
    obtain ⟨c, hc⟩ := FiniteRep.BrauerTheory.spanning (G := Q)
      (FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ))
    rw [← hc, FiniteRep.brauerExpansion, Finsupp.linearCombination_apply]
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, rfl⟩
  have hπN : ∀ w : localWeilGroup F, w ∈ N → π w = 1 := fun w hw =>
    (QuotientGroup.eq_one_iff w).mpr hw
  have hmap : Submodule.map Φ (Submodule.span ℤ (Set.range gen)) ≤
      Submodule.span ℤ (inducedCharacterClassesAbove.{uF, uV} F N) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨d, rfl⟩
    obtain ⟨L, -, hL⟩ := exists_extension_eq F U hUo (d.1.comap π) (fun w hw => by
      change π w ∈ d.1
      rw [hπN w (hUN w hw)]
      exact d.1.one_mem)
    obtain ⟨η, hη1, hη⟩ := inflate_induce_oneDimensional_weil.{uF, uV} F L π hπ hsurj d.1
      (fun w => by rw [hL]; rfl) d.2
    refine Submodule.subset_span ⟨L, fun w hw => ?_, η, fun w hw => hη1 w (hπN _ hw), hη⟩
    rw [hL]
    change π w ∈ d.1
    rw [hπN w hw]
    exact d.1.one_mem
  rw [← hΦ]
  exact hmap (Submodule.mem_map_of_mem hx)

end Langlands.LocalFactor.CommonClosure
