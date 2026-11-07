import Langlands.LocalFactor.NonabelianUniquenessStatement
import Langlands.VirtualRepresentation.FiniteInflation
import Langlands.Weil.Local.GaloisCorrectionProof
import Langlands.Representation.Finite.DegreeZeroBrauerProof
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Finite-image representations of common-closure Weil subgroups

A continuous finite-image representation of an actual common-closure Weil
subgroup `W_E` is trivial on the elements whose Galois projection lies in an
open normal subgroup of the absolute Galois group. Every subgroup of `W_E`
containing those elements is the Weil subgroup of a finite intermediate field
containing `E`. Inflating the finite degree-zero Brauer theorem from the finite
quotient then writes `[B] - dim B · [1]` as an integral combination of
inductions of differences of continuous character lines.
-/

noncomputable section

universe uG uV uF

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The kernel of a continuous finite-dimensional complex representation is closed. -/
theorem isClosed_ker_of_isContinuous (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hc : A.IsContinuous) : IsClosed (A.representation.ker : Set G) := by
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  have h := (isContinuous_of_iff A.representation).mp hc
  have hset : (A.representation.ker : Set G) =
      (fun g => (A.representation g).toContinuousLinearMap) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hg
      rw [hg]
      rfl
    · intro hg
      ext v
      exact congrArg (fun T : A →L[ℂ] A => T v) hg
  rw [hset]
  exact isClosed_singleton.preimage h

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A continuous finite-image representation of `W_E` is trivial on the
elements of `W_E` whose Galois projection lies in some open normal subgroup. -/
theorem exists_galois_kernel (E : Extension F)
    (B : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E))
    (hc : B.IsContinuous) (hf : B.HasFiniteImage) :
    ∃ U : Subgroup (Field.absoluteGaloisGroup F.Carrier), U.Normal ∧
      IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)) ∧
      ∀ w : weilSubgroup F E, localProjection F w ∈ U → B.representation w = 1 := by
  -- The kernel of `B`, viewed in the whole Weil group, is open of finite index.
  let K := B.representation.ker
  have hK : IsOpen (K : Set (weilSubgroup F E)) :=
    Weil.open_kernel_of_finite_range_of_closed B.representation hf
      (FiniteRepresentation.isClosed_ker_of_isContinuous B hc)
  let M : Subgroup (localWeilGroup F) := K.map (weilSubgroup F E).subtype
  have hM : IsOpen (M : Set (localWeilGroup F)) := by
    rw [Subgroup.coe_map]
    exact (weilSubgroup_open F E).isOpenMap_subtype_val _ hK
  let φ := Representation.asGroupHom B.representation
  have hφK : φ.ker = K := by
    ext g
    simp only [MonoidHom.mem_ker, φ, K]
    rw [← Units.val_inj, Representation.asGroupHom_apply, Units.val_one]
  have : Finite φ.range := by
    have h : (Set.range φ).Finite :=
      (hf.preimage Units.val_injective.injOn).subset (by
        rintro _ ⟨g, rfl⟩
        exact ⟨g, (Representation.asGroupHom_apply _ g).symm⟩)
    rw [← MonoidHom.coe_range] at h
    exact h.to_subtype
  have : K.FiniteIndex := hφK ▸ Subgroup.finiteIndex_ker φ
  have : M.FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  -- The permutation representation on `W_F ⧸ M` is continuous with finite image.
  let R := Representation.ofMulAction ℂ (localWeilGroup F) (localWeilGroup F ⧸ M)
  let A : LocalWeilRepresentation.{uF, uF} F := FiniteRepresentation.of R
  have hcore : IsOpen (M.normalCore : Set (localWeilGroup F)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (M.normalCore_isClosed (M.isClosed_of_isOpen hM))
  have hRcore : M.normalCore ≤ R.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext fun r => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, Module.End.one_apply, R,
      Representation.ofMulAction_single]
    congr 1
    change ((n * g : localWeilGroup F) : localWeilGroup F ⧸ M) = g
    rw [QuotientGroup.eq]
    have h : g⁻¹ * n * g⁻¹⁻¹ ∈ M := hn g⁻¹
    rw [inv_inv] at h
    have h' := M.inv_mem h
    simpa [mul_assoc] using h'
  have hAc : A.IsContinuous :=
    FiniteRepresentation.isContinuous_of_le_ker A M.normalCore hcore
      (fun n hn => hRcore hn)
  have hAf : A.HasFiniteImage := by
    refine (Set.finite_range (QuotientGroup.lift M.normalCore R hRcore)).subset ?_
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
    localWeilGroup F ⧸ M) (1 : ℂ))) hRw
  simp only [R, Representation.ofMulAction_single, Module.End.one_apply] at h1
  have h2 := MonoidAlgebra.single_left_injective (one_ne_zero (α := ℂ)) h1
  change (((w : localWeilGroup F) * 1 : localWeilGroup F) : localWeilGroup F ⧸ M) =
    ((1 : localWeilGroup F) : localWeilGroup F ⧸ M) at h2
  rw [QuotientGroup.eq] at h2
  have hwM : (w : localWeilGroup F) ∈ M := by simpa using h2
  obtain ⟨k, hk, hkw⟩ := Subgroup.mem_map.mp hwM
  have : k = w := Subtype.ext hkw
  rw [← this]
  exact hk

/-- A subgroup of `W_E` containing every element whose Galois projection lies in
an open normal subgroup `U` is the actual Weil subgroup of a finite intermediate
field containing `E`. -/
theorem exists_extension_of_le (E : Extension F)
    (U : Subgroup (Field.absoluteGaloisGroup F.Carrier)) [U.Normal]
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroup F.Carrier)))
    (H : Subgroup (weilSubgroup F E))
    (hH : ∀ w : weilSubgroup F E, localProjection F w ∈ U → w ∈ H) :
    ∃ (L : Extension F) (_ : E.field ≤ L.field),
      ∀ w : weilSubgroup F E, w ∈ H ↔ (w : localWeilGroup F) ∈ weilSubgroup F L := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let P : weilSubgroup F E →* Field.absoluteGaloisGroup F.Carrier :=
    (localProjection F).toMonoidHom.comp (weilSubgroup F E).subtype
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
  have hfix : ∀ σ : Gal(AlgebraicClosure F.Carrier/F.Carrier),
      σ ∈ (L1 ⊔ E.field).fixingSubgroup ↔ σ ∈ K ∧ σ ∈ E.field.fixingSubgroup := by
    intro σ
    rw [IntermediateField.fixingSubgroup_sup]
    exact Iff.and (SetLike.ext_iff.mp hL1 σ) Iff.rfl
  let L : Extension F := ⟨L1 ⊔ E.field, inferInstance⟩
  refine ⟨L, le_sup_right, fun w => ?_⟩
  have hw : localProjection F w ∈ E.field.fixingSubgroup := w.2
  change _ ↔ localProjection F w ∈ (L1 ⊔ E.field).fixingSubgroup
  refine Iff.trans ?_ (hfix (localProjection F w)).symm
  constructor
  · intro hwH
    exact ⟨Subgroup.mem_sup_left ⟨w, hwH, rfl⟩, hw⟩
  · rintro ⟨hwK, -⟩
    obtain ⟨_, ⟨h, hh, rfl⟩, u, hu, huw⟩ := (Subgroup.mem_sup_of_normal_right (s := H.map P) (t := U)).mp hwK
    have hu' : localProjection F ((h⁻¹ * w : weilSubgroup F E) : localWeilGroup F) ∈ U := by
      have heq : localProjection F ((h⁻¹ * w : weilSubgroup F E) : localWeilGroup F) = u := by
        change P (h⁻¹ * w) = u
        rw [map_mul, map_inv]
        change (P h)⁻¹ * localProjection F w = u
        rw [← huw]
        exact inv_mul_cancel_left (G := Field.absoluteGaloisGroup F.Carrier) (P h) u
      rw [heq]
      exact hu
    simpa using H.mul_mem hh (hH _ hu')

/-- Inflating, from a finite quotient of `W_E`, the induction of a character of a
subgroup `S` whose preimage is `W_L` gives the common-closure induction of a
continuous character line of `W_L`. -/
theorem inflate_induce_oneDimensional (E L : Extension F) (h : E.field ≤ L.field)
    {Q : Type uF} [Group Q] [Finite Q] (π : weilSubgroup F E →* Q)
    (hπ : IsOpen (π.ker : Set (weilSubgroup F E))) (hsurj : Function.Surjective π)
    (S : Subgroup Q)
    (hS : ∀ w : weilSubgroup F E, π w ∈ S ↔ (w : localWeilGroup F) ∈ weilSubgroup F L)
    (χ : S →* ℂˣ) :
    ∃ η : weilSubgroup F L →ₜ* ℂˣ,
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
  refine ⟨η, ?_⟩
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

end Langlands.LocalFactor.CommonClosure

namespace Langlands.LocalFactor

open CommonClosure Weil.Local VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Given the finite degree-zero Brauer inclusion for every finite group in the
universe `uF`, a continuous finite-image representation `B` of `W_E` satisfies
`[B] - dim B · [1] ∈ span` of the inductions of differences of continuous
character lines. -/
theorem finiteImage_sub_mem_span
    (hBrauer : ∀ (Q : Type uF) [Group Q] [Fintype Q] (x : FiniteRep.VirtualRep ℂ Q),
      FiniteRep.virtualCharacter (k := ℂ) (G := Q) x 1 = 0 →
        x ∈ Submodule.span ℤ (FiniteRep.degreeZeroBrauerGenerators Q))
    (E : Extension F) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hc : B.IsContinuous) (hf : B.HasFiniteImage) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hc⟩ -
        (B.rank : ℤ) •
          ExactGrothendieckGroup.characterClass.{uF, max uF uV}
            (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) := by
  obtain ⟨U, hUn, hUo, hU⟩ := exists_galois_kernel F E B hc hf
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  have : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  have : Finite (Field.absoluteGaloisGroup F.Carrier ⧸ U) :=
    Subgroup.quotient_finite_of_isOpen U hUo
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- The finite quotient of `W_E` through which `B` factors.
  let P : weilSubgroup F E →* Field.absoluteGaloisGroup F.Carrier :=
    (localProjection F).toMonoidHom.comp (weilSubgroup F E).subtype
  have hPc : Continuous P := (localProjection F).continuous.comp continuous_subtype_val
  let N := U.comap P
  have : N.Normal := Subgroup.normal_comap P
  let Q := weilSubgroup F E ⧸ N
  have : Finite Q := Subgroup.finite_quotient_of_finiteIndex
  let : Fintype Q := Fintype.ofFinite Q
  let π : weilSubgroup F E →* Q := QuotientGroup.mk' N
  have hπ : IsOpen (π.ker : Set (weilSubgroup F E)) := by
    rw [QuotientGroup.ker_mk']
    exact hUo.preimage hPc
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  let ρ : Representation ℂ Q B :=
    QuotientGroup.lift N B.representation (fun w hw => (MonoidHom.mem_ker).mpr (hU w hw))
  -- The finite degree-zero class and its inflation.
  let x : FiniteRep.VirtualRep ℂ Q :=
    FiniteRep.ofClass (FiniteRep.classOfRepresentation ρ) -
      (B.rank : ℤ) • FiniteRep.ofClass (FiniteRep.classOf (FiniteRep.oneDimensional (1 : Q →* ℂˣ)))
  have hx : FiniteRep.virtualCharacter (k := ℂ) (G := Q) x 1 = 0 := by
    simp only [x, map_sub, map_zsmul, FiniteRep.virtualCharacter_ofClass,
      FiniteRep.character_classOfRepresentation, FiniteRep.character_classOf, Pi.sub_apply,
      Pi.smul_apply, FiniteRep.character_oneDimensional, Representation.char_one,
      MonoidHom.one_apply, Units.val_one, FiniteRepresentation.rank]
    simp
  let Φ := ExactGrothendieckGroup.inflate.{uF, uF, max uF uV} π hπ
  have hΦx : Φ x = ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E)
      ⟨B, hc⟩ - (B.rank : ℤ) •
        ExactGrothendieckGroup.characterClass.{uF, max uF uV} (1 : weilSubgroup F E →ₜ* ℂˣ) := by
    simp only [Φ, x, map_sub, map_zsmul, ExactGrothendieckGroup.inflate_ofClass]
    congr 2
    change ExactGrothendieckGroup.ofRepresentation _
      ⟨FiniteRepresentation.inflate π (FiniteRep.ofRepresentation ρ), _⟩ = _
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact (FiniteRepresentation.inflateEquiv π _ (FiniteRep.modelEquiv ρ).symm).trans
      (Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun g => LinearMap.ext fun v => rfl))
  rw [← hΦx]
  have hmap : Submodule.map Φ (Submodule.span ℤ (FiniteRep.degreeZeroBrauerGenerators Q)) ≤
      Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨S, χ, χ', rfl⟩
    have : U.Normal := hUn
    obtain ⟨L, hEL, hL⟩ := exists_extension_of_le F E U hUo (S.comap π) (fun w hw => by
      have h1 : π w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
      change π w ∈ S
      rw [h1]
      exact S.one_mem)
    obtain ⟨η, hη⟩ := inflate_induce_oneDimensional F E L hEL π hπ hsurj S hL χ
    obtain ⟨η', hη'⟩ := inflate_induce_oneDimensional F E L hEL π hπ hsurj S hL χ'
    have e1 : Φ (FiniteRep.ofClass (FiniteRep.induceHom S
        (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) =
        induce.{uF, uV} F E L hEL (ExactGrothendieckGroup.characterClass η) := hη
    have e2 : Φ (FiniteRep.ofClass (FiniteRep.induceHom S
        (FiniteRep.classOf (FiniteRep.oneDimensional χ')))) =
        induce.{uF, uV} F E L hEL (ExactGrothendieckGroup.characterClass η') := hη'
    rw [FiniteRep.virtualInduce, map_sub, FiniteRep.virtualMap_ofClass,
      FiniteRep.virtualMap_ofClass, map_sub, e1, e2, ← map_sub]
    exact Submodule.subset_span ⟨L, hEL, η, η', rfl⟩
  exact hmap (Submodule.mem_map_of_mem (hBrauer Q x hx))

/-- A continuous finite-image representation `B` of `W_E` satisfies
`[B] - dim B · [1] ∈ span` of the inductions of differences of continuous
character lines; the finite degree-zero Brauer theorem is supplied by the
Library. -/
theorem finiteImage_sub_mem_span'
    (E : Extension F) (B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E))
    (hc : B.IsContinuous) (hf : B.HasFiniteImage) :
    ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate.{uF, uV} F E) ⟨B, hc⟩ -
        (B.rank : ℤ) •
          ExactGrothendieckGroup.characterClass.{uF, max uF uV}
            (1 : weilSubgroup F E →ₜ* ℂˣ) ∈
      Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) :=
  finiteImage_sub_mem_span F (fun Q _ _ x hx => by
    change x ∈ FiniteRep.degreeZeroBrauerSpan Q
    rw [FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer Q]
    exact hx) E B hc hf

end Langlands.LocalFactor
