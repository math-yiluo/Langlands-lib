import Langlands.Representation.Exponents.WeakCriticalTopLayerSplit
import Langlands.Representation.Exponents.WeakCriticalTopLayerCoarsening
import Langlands.Representation.Exponents.DualCharacterQuotient
import Langlands.Representation.Exponents.OppositeJacquetSubquotientInheritanceProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Dual exponents of quotients of a maximal central-defect layer

Let `W` be the image of the `k`-th power of the central character defect of `a`
on the dual-detected character quotient of the opposite Jacquet module of `A`
along `B`, and let `S` be a quotient of `W` with scalar block character `χ`.
A dual eigenfunctional of `S` on its refined opposite Jacquet quotient along a
block refinement `D` gives a dual exponent `ψ` of `A` along the flattened shape.
This file proves three facts about `ψ`: it restricts to `χ` on the block scalars
of `B`; its eigenfunctional is the image under the `k`-th power of the defect of
`a` of a vector in the generalized `ψ`-space; in particular the uniform
nilpotence order at `ψ` is larger than `k` along the flattened shape.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV uW uK uA uX

section Generalized

variable {K : Type uK} [Field K] {H : Type uA} [CommGroup H]
  {V : Type uX} [AddCommGroup V] [Module K V]

/-- Subrepresentations are stable under powers of a character defect. -/
theorem Subrepresentation.defect_pow_mem {ρ : Representation K H V}
    (U : Subrepresentation ρ) (a : H) (z : K) (k : ℕ) {x : V} (hx : x ∈ U) :
    ((ρ a - z • 1) ^ k) x ∈ U := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.toSubmodule.sub_mem (U.apply_mem_toSubmodule a ih) (U.toSubmodule.smul_mem z ih)

/-- If the full space is spanned by generalized character spaces and a power of a
defect sends a vector onto a nonzero vector of the generalized `ψ`-space, then
it already does so from a vector of the generalized `ψ`-space. -/
theorem exists_generalized_preimage (ρ : Representation K H V) (P : (H →* Kˣ) → Prop)
    (hspan : (⨆ (χ : H →* Kˣ) (_ : P χ),
      (generalizedCommutativeCharacterSpace ρ χ).toSubmodule) = ⊤)
    (ψ : H →* Kˣ) (a : H) (z : K) (k : ℕ) (L Λ : V)
    (hΛ : Λ ∈ generalizedCommutativeCharacterSpace ρ ψ)
    (hL : ((ρ a - z • 1) ^ k) L = Λ) :
    ∃ L' ∈ generalizedCommutativeCharacterSpace ρ ψ, ((ρ a - z • 1) ^ k) L' = Λ := by
  classical
  let G : (H →* Kˣ) → Submodule K V := fun χ =>
    (generalizedCommutativeCharacterSpace ρ χ).toSubmodule
  let Rest : Submodule K V := ⨆ (χ : H →* Kˣ) (_ : χ ≠ ψ), G χ
  have htop : (⊤ : Submodule K V) ≤ G ψ ⊔ Rest := by
    rw [← hspan]
    refine iSup₂_le fun χ _ => ?_
    by_cases h : χ = ψ
    · subst h
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le χ h le_rfl)
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (htop Submodule.mem_top : L ∈ G ψ ⊔ Rest)
  let Dm : V →ₗ[K] V := (ρ a - z • 1) ^ k
  have hDrest : Rest ≤ Rest.comap Dm := by
    refine iSup₂_le fun χ hχ x hx => ?_
    rw [Submodule.mem_comap]
    exact (le_iSup₂_of_le (f := fun χ (_ : χ ≠ ψ) => G χ) χ hχ le_rfl :
      G χ ≤ Rest) (Subrepresentation.defect_pow_mem _ a z k hx)
  have hDy : Dm y ∈ G ψ := Subrepresentation.defect_pow_mem _ a z k hy
  have hDw : Dm w ∈ Rest := hDrest hw
  have hdisj : Disjoint (G ψ) Rest := by
    have hind := (ScalarSubquotientDualSpectrum.independent_weights ρ).disjoint_biSup
      (x := ψ) (y := {χ | χ ≠ ψ}) (fun h => h rfl)
    refine Disjoint.mono (ScalarSubquotientDualSpectrum.generalized_le_weight ρ ψ) ?_ hind
    exact iSup₂_mono fun χ _ => ScalarSubquotientDualSpectrum.generalized_le_weight ρ χ
  have hw0 : Dm w = 0 := by
    have hmem : Dm w ∈ G ψ := by
      have he : Dm w = Λ - Dm y := by
        rw [← hL, ← hyw]
        change Dm w = Dm (y + w) - Dm y
        rw [map_add]
        abel
      rw [he]
      exact (G ψ).sub_mem hΛ hDy
    exact (Submodule.disjoint_def.mp hdisj) _ hmem hDw
  refine ⟨y, hy, ?_⟩
  change Dm y = Λ
  rw [← hL, ← hyw]
  change Dm y = Dm (y + w)
  rw [map_add, hw0, add_zero]

end Generalized

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The dual eigenfunctional of a quotient `S` of the `k`-th central-defect layer
along a refinement `D` gives a dual exponent `ψ` of `A` along the flattened shape
which restricts to the block character of `S`, and some generalized `ψ`-vector is
not killed by the `k`-th power of the defect of `a`. -/
theorem topLayer_flattened_dual (hn : 0 < n) (B : BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hAirr : Representation.IsIrreducible A.ρ) (hA : letI := T.topology; IsAdmissible A.ρ)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (a : Fin B.length → F.Carrierˣ) (k : ℕ)
    (S : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hS : Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ)
    (q : (T.dualJacquetCharacterDefectRangeRepresentation B A χ a k).ρ.IntertwiningMap S.ρ)
    (hq : Function.Surjective q)
    (D : BlockRefinement B) (ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ)
    (φ : Module.Dual ℂ (RefinedOppositeJacquetModule B D S.ρ)) (hφ : φ ≠ 0)
    (heig : ∀ (b : Fin (B.flatten D).length → F.Carrierˣ) (v : S),
      φ (T.normalizedRefinedOppositeJacquet B D S.ρ
          (flattenedLeviEquiv F.Carrier B D ((B.flatten D).blockScalarLevi F.Carrier b))
          (refinedOppositeJacquetMk B D S.ρ v)) =
        (ψ b : ℂ) * φ (refinedOppositeJacquetMk B D S.ρ v)) :
    (∀ c : Fin B.length → F.Carrierˣ, ψ (c ∘ B.flattenOuter D) = χ c) ∧
    commutativeCharacterSpace (T.splitCentreDualJacquet (B.flatten D) A).ρ ψ 1 ≠ ⊥ ∧
    ∃ L ∈ generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet (B.flatten D) A).ρ ψ,
      (((T.splitCentreDualJacquet (B.flatten D) A).ρ (a ∘ B.flattenOuter D) -
        (χ a : ℂ) • 1) ^ k) L ≠ 0 := by
  classical
  let := T.topology
  -- The restriction of `ψ` to the outer block scalars.
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ (refinedOppositeJacquetMk B D S.ρ v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := refinedOppositeJacquetMk_surjective B D S.ρ x
    exact h v
  have hkey : ∀ c : Fin B.length → F.Carrierˣ, ψ (c ∘ B.flattenOuter D) = χ c := by
    intro c
    have h := heig (c ∘ B.flattenOuter D) v₀
    rw [T.normalizedRefinedOppositeJacquet_mk, T.refinedLeviHalfModulus_blockScalarLevi_comp,
      B.flattenedLeviEquiv_blockScalarLevi_comp D F.Carrier c, hS c v₀, Units.val_one, one_smul,
      map_smul, map_smul, smul_eq_mul] at h
    exact (Units.ext (mul_right_cancel₀ hv₀ h)).symm
  refine ⟨hkey, ?_⟩
  -- The objects.
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T B A
  have hO : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B A A.ρ hA
  have hX : IsSmooth (T.dualJacquetCharacterQuotient B A χ).ρ :=
    isSmooth_of_surjective (T.dualJacquetCharacterQuotientMap B A χ)
      (T.dualJacquetCharacterQuotientMap_surjective B A χ) hO.1
  let πχ := T.dualJacquetCharacterQuotientMap B A χ
  let m := T.dualJacquetCharacterDefectRangeMap B A χ a k
  let incl := T.dualJacquetCharacterDefectRangeInclusion B A χ a k
  let Jq := T.normalizedRefinedOppositeJacquetMap B D q
  let Jm := T.normalizedRefinedOppositeJacquetMap B D m
  let Jπ := T.normalizedRefinedOppositeJacquetMap B D πχ
  let Ji := T.normalizedRefinedOppositeJacquetMap B D incl
  have hJi : Function.Injective Ji :=
    T.normalizedRefinedOppositeJacquetMap_injective B D incl hX Subtype.val_injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective Ji.toLinearMap
    (LinearMap.ker_eq_bot.mpr hJi)
  let lamX : Module.Dual ℂ (RefinedOppositeJacquetModule B D
      (T.dualJacquetCharacterQuotient B A χ).ρ) := (φ.comp Jq.toLinearMap).comp g
  have hlamX : ∀ y, lamX (Ji y) = φ (Jq y) := by
    intro y
    have h := LinearMap.congr_fun hg y
    change g (Ji y) = y at h
    change φ (Jq (g (Ji y))) = φ (Jq y)
    rw [h]
  -- The flattened opposite Jacquet module.
  obtain ⟨Et, hEt⟩ := Parabolic.normalizedOppositeRefinementTransitivity p F T n B D A
  obtain ⟨Ef, hEf⟩ := Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uV}.2 p F T n B D A
  let E : RefinedOppositeJacquetModule B D O.ρ ≃ₗ[ℂ]
      T.splitCentreOppositeJacquet (B.flatten D) A :=
    Et.toLinearEquiv.trans Ef.toLinearEquiv
  let scal : (Fin (B.flatten D).length → F.Carrierˣ) → refinedLevi F.Carrier B D :=
    fun b => flattenedLeviEquiv F.Carrier B D ((B.flatten D).blockScalarLevi F.Carrier b)
  have hE : ∀ (b : Fin (B.flatten D).length → F.Carrierˣ) z,
      E (T.normalizedRefinedOppositeJacquet B D O.ρ (scal b) z) =
        (T.splitCentreOppositeJacquet (B.flatten D) A).ρ b (E z) := by
    intro b z
    exact (congrArg (fun y => Ef y)
      (Representation.IntertwiningMap.isIntertwining _ _ Et.toIntertwiningMap (scal b) z)).trans
        (Representation.IntertwiningMap.isIntertwining _ _ Ef.toIntertwiningMap
          ((B.flatten D).blockScalarLevi F.Carrier b) (Et z))
  have hEmk : ∀ v : A, E.symm (T.splitCentreOppositeJacquetMk (B.flatten D) A v) =
      refinedOppositeJacquetMk B D O.ρ (T.splitCentreOppositeJacquetMk B A v) := by
    intro v
    rw [LinearEquiv.symm_apply_eq]
    exact ((congrArg (fun y => Ef y) (hEt v)).trans (hEf v)).symm
  -- The eigenfunctional and the lifted functional on the flattened quotient.
  let Λ : Module.Dual ℂ (RefinedOppositeJacquetModule B D O.ρ) :=
    φ.comp (Jq.toLinearMap.comp Jm.toLinearMap)
  let Λf : Module.Dual ℂ (T.splitCentreOppositeJacquet (B.flatten D) A) :=
    Λ.comp E.symm.toLinearMap
  let L : Module.Dual ℂ (T.splitCentreOppositeJacquet (B.flatten D) A) :=
    (lamX.comp Jπ.toLinearMap).comp E.symm.toLinearMap
  have hΛf : ∀ v : A, Λf (T.splitCentreOppositeJacquetMk (B.flatten D) A v) =
      φ (refinedOppositeJacquetMk B D S.ρ (q (m (T.splitCentreOppositeJacquetMk B A v)))) := by
    intro v
    change Λ (E.symm _) = _
    rw [hEmk v]
    rfl
  have hL : ∀ v : A, L (T.splitCentreOppositeJacquetMk (B.flatten D) A v) =
      lamX (refinedOppositeJacquetMk B D (T.dualJacquetCharacterQuotient B A χ).ρ
        (πχ (T.splitCentreOppositeJacquetMk B A v))) := by
    intro v
    change lamX (Jπ (E.symm _)) = _
    rw [hEmk v]
    rfl
  have heigS : ∀ b (y : RefinedOppositeJacquetModule B D S.ρ),
      φ (T.normalizedRefinedOppositeJacquet B D S.ρ (scal b) y) = (ψ b : ℂ) * φ y := by
    intro b y
    obtain ⟨s, rfl⟩ := refinedOppositeJacquetMk_surjective B D S.ρ y
    exact heig b s
  have hΛfeig : ∀ b, commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ b Λf =
      (ψ b : ℂ) • Λf := by
    intro b
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := E.surjective y
    rw [commutativeTranspose_apply, ← hE, LinearMap.smul_apply, smul_eq_mul]
    change Λ (E.symm (E _)) = (ψ b : ℂ) * Λ (E.symm (E z))
    simp only [LinearEquiv.symm_apply_apply]
    change φ (Jq (Jm _)) = (ψ b : ℂ) * φ (Jq (Jm z))
    rw [Representation.IntertwiningMap.isIntertwining _ _ Jm,
      Representation.IntertwiningMap.isIntertwining _ _ Jq]
    exact heigS b _
  have hΛf0 : Λf ≠ 0 := by
    obtain ⟨w, hw⟩ := hq v₀
    obtain ⟨o, ho⟩ := T.dualJacquetCharacterDefectRangeMap_surjective B A χ a k w
    obtain ⟨v, hv⟩ := T.splitCentreOppositeJacquetMk_surjective B A o
    intro h0
    apply hv₀
    have h1 := hΛf v
    rw [h0, LinearMap.zero_apply] at h1
    rw [← hw, ← ho, ← hv]
    exact h1.symm
  have hmem1 : Λf ∈ commutativeCharacterSpace
      (T.splitCentreDualJacquet (B.flatten D) A).ρ ψ 1 := by
    change Λf ∈ commutativeCharacterSpace
      (commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ) ψ 1
    rw [mem_commutativeCharacterSpace_one]
    exact hΛfeig
  refine ⟨fun hbot => hΛf0 ?_, ?_⟩
  · rw [hbot] at hmem1
    change Λf = 0 at hmem1
    exact hmem1
  -- The `k`-th defect power of `a` sends the lifted functional to the eigenfunctional.
  have hδ : (T.leviHalfModulus (B.flatten D)
      ((B.flatten D).blockScalarLevi F.Carrier (a ∘ B.flattenOuter D)) : ℂ) =
      T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) := by
    rw [leviHalfModulus_apply, leviHalfModulus_apply,
      T.leviModulus_blockScalarLevi_coarsen (B.flattenOuter_mono D)
        (B.size_eq_sum_flattenOuter D) a]
  have hDL : ((commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ
      (a ∘ B.flattenOuter D) - (χ a : ℂ) • 1) ^ k) L = Λf := by
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := T.splitCentreOppositeJacquetMk_surjective (B.flatten D) A y
    rw [commutativeTranspose_defect_pow_apply, T.splitCentreOppositeJacquet_defect_pow_mk,
      BlockShape.leviEmbedding_blockScalarLevi_coarsen F.Carrier (B.flattenOuter_mono D)
        (B.size_eq_sum_flattenOuter D) a, hδ, hL, hΛf,
      ← T.splitCentreOppositeJacquet_defect_pow_mk B A a (χ a : ℂ) k v]
    have h1 := T.dualJacquetCharacterDefect_pow_quotientMap B A χ a k
      (T.splitCentreOppositeJacquetMk B A v)
    exact (congrArg (fun x => lamX (refinedOppositeJacquetMk B D
      (T.dualJacquetCharacterQuotient B A χ).ρ x)) h1.symm).trans
        (hlamX (refinedOppositeJacquetMk B D _ (m (T.splitCentreOppositeJacquetMk B A v))))
  -- Pass to the generalized `ψ`-component.
  have hspan := (glDualJacquetFiniteness p F T n hn (B.flatten D) A hAirr hA).2.2
  have hΛgen : Λf ∈ generalizedCommutativeCharacterSpace
      (commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ) ψ := by
    refine (mem_generalizedCommutativeCharacterSpace _ _ _).mpr ⟨1, fun b => ?_⟩
    rw [pow_one, LinearMap.sub_apply, hΛfeig b, LinearMap.smul_apply, Module.End.one_apply,
      sub_self]
  obtain ⟨L', hL', hDL'⟩ := exists_generalized_preimage
    (commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ)
    (T.IsDualJacquetExponent (B.flatten D) A) hspan ψ (a ∘ B.flattenOuter D) (χ a : ℂ) k
    L Λf hΛgen hDL
  refine ⟨L', hL', ?_⟩
  change ((commutativeTranspose (T.splitCentreOppositeJacquet (B.flatten D) A).ρ
      (a ∘ B.flattenOuter D) - (χ a : ℂ) • 1) ^ k) L' ≠ 0
  rw [hDL']
  exact hΛf0

end PadicField.TopologicalData

end Langlands
