import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement
import Langlands.ClassFieldTheory.Global.FundamentalClassProof
import Langlands.ClassFieldTheory.Global.RelativeWeilTransferReciprocityProof
import Langlands.ClassFieldTheory.Global.RelativeWeilTransferNormProof
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.Global.AdelicFunctoriality.IdeleNormOpen
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTransport
import Langlands.LocalFactor.BrauerKernel.ArchimedeanTrivial
import Langlands.Global.Arithmetic.HarrisDatumArchimedean

/-! # Real-norm factorization of CM cyclic norm-kernel characters -/

noncomputable section

universe u uE uD

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality

namespace CMNormKernelRealFactor

/-- Complex conjugation of a CM field commutes with every field automorphism. -/
private theorem complexConj_comm {L : Type*} [Field L] [NumberField L] [IsCMField L]
    (g : L ≃+* L) (x : L) :
    g (IsCMField.complexConj L x) = IsCMField.complexConj L (g x) := by
  let φ : L →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h₁ := IsCMField.complexEmbedding_complexConj L (φ.comp (g : L →+* L)) x
  have h₂ := IsCMField.complexEmbedding_complexConj L φ (g x)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h₁
  rw [h₂]
  exact h₁

/-- The image of a real element of `E` is real in every extension field. -/
private theorem algebraMap_mem_maximalRealSubfield {E L : Type*} [Field E] [Field L] [Algebra E L]
    (x : maximalRealSubfield E) :
    algebraMap E L x ∈ maximalRealSubfield L := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  exact (mem_maximalRealSubfield_iff (x : E)).mp x.2 (φ.comp (algebraMap E L))

/-- The factorization for a cyclic extension `L / E` of CM fields in one universe, the
setting of the Library's relative Weil groups. The character of `E⁺` is the composite of the
reciprocity map of the abelian extension `L / E⁺` with a character of `Gal(L/E⁺)` that is
trivial on complex conjugation and restricts to the character of `Gal(L/E)` induced by `η`. -/
theorem exists_realFactor_sameUniverse (E L : Type u) [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] [IsCMField L] [Algebra E L] [IsGalois E L]
    [IsCyclic (L ≃ₐ[E] L)] (η : HeckeCharacter E) (hη : η.IsTrivialOnNorm L) :
    ∃ η₀ : HeckeCharacter (maximalRealSubfield E),
      η₀.HasFiniteOrder ∧ η₀.atInfinity = 1 ∧
        η = η₀.comp (ideleClassNorm (K := maximalRealSubfield E) (L := E)) := by
  classical
  -- The real subfield of `L` as an extension of the real subfield of `E`.
  let algP : Algebra (maximalRealSubfield E) (maximalRealSubfield L) :=
    (((algebraMap E L).comp (algebraMap (maximalRealSubfield E) E)).codRestrict
      (maximalRealSubfield L) (fun x => algebraMap_mem_maximalRealSubfield x)).toAlgebra
  have towP : IsScalarTower (maximalRealSubfield E) (maximalRealSubfield L) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Complex conjugations.
  let cE : E ≃ₐ[maximalRealSubfield E] E := IsCMField.complexConj E
  let cL : L ≃ₐ[maximalRealSubfield L] L := IsCMField.complexConj L
  let cF : L ≃ₐ[maximalRealSubfield E] L := cL.restrictScalars (maximalRealSubfield E)
  have hcFE (x : E) : cF (algebraMap E L x) = algebraMap E L (cE x) :=
    HarrisDatum.complexConj_algebraMap x
  have hcF2 : cF * cF = 1 := by
    ext x
    exact IsCMField.complexConj_apply_apply L x
  have hcentral (g : L ≃ₐ[maximalRealSubfield E] L) : Commute g cF := by
    ext x
    exact complexConj_comm g.toRingEquiv x
  have hcE_ne : cE ≠ 1 := IsCMField.complexConj_ne_one E
  -- Automorphisms of `E` over its real subfield.
  have hcard : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hτ (τ : E ≃ₐ[maximalRealSubfield E] E) : τ = 1 ∨ τ = cE := by
    by_cases h : τ = 1
    · exact Or.inl h
    · exact Or.inr (((Nat.card_eq_two_iff' 1).mp hcard).unique h hcE_ne)
  -- Automorphisms of `L` over `E` inside those over the real subfield of `E`.
  let j : (L ≃ₐ[E] L) →* (L ≃ₐ[maximalRealSubfield E] L) :=
    AlgEquiv.restrictScalarsHom (maximalRealSubfield E)
  have hfix (g : L ≃ₐ[maximalRealSubfield E] L)
      (hg : ∀ x : E, g (algebraMap E L x) = algebraMap E L x) : ∃ σ : L ≃ₐ[E] L, j σ = g :=
    ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, by ext x; rfl⟩
  have hcases (g : L ≃ₐ[maximalRealSubfield E] L) :
      (∃ σ : L ≃ₐ[E] L, j σ = g) ∨ (∃ σ : L ≃ₐ[E] L, j σ = g * cF) := by
    rcases hτ (g.restrictNormal E) with h | h
    · left
      apply hfix
      intro x
      rw [← AlgEquiv.restrictNormal_commutes, h]
      rfl
    · right
      apply hfix
      intro x
      rw [AlgEquiv.mul_apply, hcFE, ← AlgEquiv.restrictNormal_commutes, h]
      congr 1
      exact IsCMField.complexConj_apply_apply E x
  have hdecomp (g : L ≃ₐ[maximalRealSubfield E] L) :
      ∃ σ : L ≃ₐ[E] L, g = j σ ∨ g = j σ * cF := by
    rcases hcases g with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
    · exact ⟨σ, Or.inl hσ.symm⟩
    · refine ⟨σ, Or.inr ?_⟩
      rw [hσ, mul_assoc, hcF2, mul_one]
  have hcommE (σ τ : L ≃ₐ[E] L) : σ * τ = τ * σ :=
    (inferInstance : IsMulCommutative (L ≃ₐ[E] L)).is_comm.comm σ τ
  have hcomm (g h : L ≃ₐ[maximalRealSubfield E] L) : g * h = h * g := by
    obtain ⟨σ, hσ⟩ := hdecomp g
    obtain ⟨τ, hτ'⟩ := hdecomp h
    have hjj : Commute (j σ) (j τ) := by
      change j σ * j τ = j τ * j σ
      rw [← map_mul, ← map_mul, hcommE]
    rcases hσ with rfl | rfl <;> rcases hτ' with rfl | rfl
    · exact hjj.eq
    · exact (hjj.mul_right (hcentral (j σ))).eq
    · exact (hjj.mul_left (hcentral (j τ)).symm).eq
    · exact ((hjj.mul_right (hcentral (j σ))).mul_left
        ((hcentral (j τ)).symm.mul_right (Commute.refl cF))).eq
  -- `L` is Galois over the real subfield of `E`.
  have hGal : IsGalois (maximalRealSubfield E) L := by
    apply IsGalois.of_fixedField_eq_bot
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxE : x ∈ Set.range (algebraMap E L) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro σ
      exact hx (j σ) (Subgroup.mem_top _)
    obtain ⟨k, rfl⟩ := hxE
    have hk : cE k = k := by
      apply (algebraMap E L).injective
      rw [← hcFE]
      exact hx cF (Subgroup.mem_top _)
    rw [IsCMField.complexConj_eq_self_iff] at hk
    rw [IntermediateField.mem_bot]
    exact ⟨⟨k, hk⟩, rfl⟩
  -- Global class field theory through relative Weil groups.
  choose I hI using localRelativeClassFormation.{u}
  have hI' : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    fun p _ => ⟨(hI p).2.1, (hI p).1⟩
  obtain ⟨c, hc⟩ := fundamentalClass_exists I hI'
  have hRes : FundamentalClass.Restriction c := hc.2.1
  obtain ⟨hsurjF, hkerF⟩ :=
    RelativeWeilGroup.relativeWeilTransferReciprocity I hI' c hc (maximalRealSubfield E) L
  obtain ⟨hsurjE, -⟩ := RelativeWeilGroup.relativeWeilTransferReciprocity I hI' c hc E L
  obtain ⟨hsurjP, -⟩ :=
    RelativeWeilGroup.relativeWeilTransferReciprocity I hI' c hc (maximalRealSubfield L) L
  -- The reciprocity map of the abelian extension `L / E⁺`.
  have : IsMulCommutative (L ≃ₐ[maximalRealSubfield E] L) := ⟨⟨hcomm⟩⟩
  have hle : (RelativeWeilGroup.transfer c (maximalRealSubfield E) L).ker ≤
      (RelativeWeilGroup.projection c (maximalRealSubfield E) L).ker :=
    hkerF.le.trans (Abelianization.commutator_subset_ker _)
  let r := (RelativeWeilGroup.transfer c (maximalRealSubfield E) L).liftOfSurjective hsurjF
    ⟨RelativeWeilGroup.projection c (maximalRealSubfield E) L, hle⟩
  have hr (t : RelativeWeilGroup c (maximalRealSubfield E) L) :
      r (RelativeWeilGroup.transfer c (maximalRealSubfield E) L t) =
        RelativeWeilGroup.projection c (maximalRealSubfield E) L t :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  -- The character of `Gal(L/E)` induced by `η`.
  have hψle : (RelativeWeilGroup.projection c E L).ker ≤
      (η.toMonoidHom.comp (RelativeWeilGroup.transfer c E L)).ker := by
    intro t ht
    rw [← RelativeWeilGroup.exact] at ht
    obtain ⟨a, rfl⟩ := ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, RelativeWeilGroup.transfer_inclusion]
    exact hη a
  let ψ := (RelativeWeilGroup.projection c E L).liftOfSurjective
    (RelativeWeilGroup.projection_surjective c E L)
    ⟨η.toMonoidHom.comp (RelativeWeilGroup.transfer c E L), hψle⟩
  have hψ (t : RelativeWeilGroup c E L) :
      ψ (RelativeWeilGroup.projection c E L t) = η (RelativeWeilGroup.transfer c E L t) :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  -- Restriction identifies `Gal(L/E)` with the quotient by complex conjugation.
  let N : Subgroup (L ≃ₐ[maximalRealSubfield E] L) := Subgroup.zpowers cF
  have hN : N.Normal := ⟨fun n _ g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  let q := QuotientGroup.mk' N
  let θ : (L ≃ₐ[E] L) →* (L ≃ₐ[maximalRealSubfield E] L) ⧸ N := q.comp j
  have hqc : q cF = 1 := (QuotientGroup.eq_one_iff cF).mpr (Subgroup.mem_zpowers cF)
  have hsq : cF ^ (2 : ℤ) = 1 := by rw [zpow_two, hcF2]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hmem : j σ ∈ N := (QuotientGroup.eq_one_iff (j σ)).mp hσ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hσ1 : j σ = 1 ∨ j σ = cF := by
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · left
        rw [← hk, zpow_mul, hsq, one_zpow]
      · right
        rw [← hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
    rcases hσ1 with h1 | h1
    · ext x
      exact DFunLike.congr_fun h1 x
    · exfalso
      apply hcE_ne
      ext x
      apply (algebraMap E L).injective
      rw [← hcFE, ← h1]
      exact σ.commutes x
  have hθsurj : Function.Surjective θ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    rcases hcases g with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
    · exact ⟨σ, by change q (j σ) = q g; rw [hσ]⟩
    · refine ⟨σ, ?_⟩
      change q (j σ) = q g
      rw [hσ, map_mul, hqc, mul_one]
  let θe := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  let φ : (L ≃ₐ[maximalRealSubfield E] L) →* ℂˣ := ψ.comp (θe.symm.toMonoidHom.comp q)
  have hφj (σ : L ≃ₐ[E] L) : φ (j σ) = ψ σ := by
    change ψ (θe.symm (θe σ)) = ψ σ
    rw [MulEquiv.symm_apply_apply]
  have hφc : φ cF = 1 := by
    change ψ (θe.symm (q cF)) = 1
    rw [hqc, map_one, map_one]
  -- The real-subfield character.
  let η₀' : IdeleClassGroup (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) →* ℂˣ :=
    φ.comp r
  have hη₀' (t : RelativeWeilGroup c (maximalRealSubfield E) L) :
      η₀' (RelativeWeilGroup.transfer c (maximalRealSubfield E) L t) =
        φ (RelativeWeilGroup.projection c (maximalRealSubfield E) L t) := by
    change φ (r _) = _
    rw [hr]
  have hη₀N (a : IdeleClassGroup (𝓞 L) L) :
      η₀' (ideleClassNorm (K := maximalRealSubfield E) (L := L) a) = 1 := by
    rw [← RelativeWeilGroup.transfer_inclusion c (maximalRealSubfield E) L a, hη₀']
    have hproj : RelativeWeilGroup.projection c (maximalRealSubfield E) L
        (RelativeWeilGroup.inclusion c (maximalRealSubfield E) L a) = 1 := by
      rw [← MonoidHom.mem_ker, ← RelativeWeilGroup.exact]
      exact ⟨a, rfl⟩
    rw [hproj, map_one]
  have hcont : Continuous η₀' := by
    apply continuous_of_continuousAt_one η₀'
    have hopen : IsOpen (Set.range (ideleClassNorm (K := maximalRealSubfield E) (L := L))) := by
      rw [← Set.image_univ]
      exact isOpenMap_ideleClassNorm _ isOpen_univ
    have hmem : Set.range (ideleClassNorm (K := maximalRealSubfield E) (L := L)) ∈
        nhds (1 : IdeleClassGroup (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) :=
      hopen.mem_nhds ⟨1, map_one _⟩
    refine (continuousAt_const : ContinuousAt (fun _ => (1 : ℂˣ)) _).congr ?_
    filter_upwards [hmem] with x hx
    obtain ⟨a, rfl⟩ := hx
    exact (hη₀N a).symm
  let η₀ : HeckeCharacter (maximalRealSubfield E) :=
    { toMonoidHom := η₀'
      continuous_toFun := hcont }
  have hη₀ (x) : η₀ x = φ (r x) := rfl
  refine ⟨η₀, ?_, ?_, ?_⟩
  · -- Finite order.
    refine ⟨Nat.card (L ≃ₐ[maximalRealSubfield E] L), Nat.card_pos, ?_⟩
    apply ContinuousMonoidHom.ext
    intro x
    rw [ContinuousMonoidHom.pow_apply, hη₀, ← map_pow, pow_card_eq_one', map_one]
    rfl
  · -- Triviality on the whole archimedean factor.
    have hP (z : IdeleClassGroup (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) :
        η₀ (ideleClassNorm (K := maximalRealSubfield E) (L := maximalRealSubfield L) z) = 1 := by
      obtain ⟨t, rfl⟩ := hsurjP z
      change η₀' _ = 1
      rw [← RelativeWeilGroup.transferNormCompatibility c (maximalRealSubfield E)
        (maximalRealSubfield L) L hRes t, hη₀', RelativeWeilGroup.projection_restrictionInclusion]
      have hmem : RelativeWeilGroup.projection c (maximalRealSubfield L) L t ∈
          Subgroup.zpowers cL := by
        rw [IsCMField.zpowers_complexConj_eq_top]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      change φ (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (cL ^ k)) = 1
      rw [map_zpow, map_zpow]
      change φ cF ^ k = 1
      rw [hφc, one_zpow]
    have hcomp (v : InfinitePlace (maximalRealSubfield E)) : η₀.infiniteComponent v = 1 := by
      obtain ⟨w⟩ := exists_infinitePlace_above (L := maximalRealSubfield L) v
      have : w.1.LiesOver v := w.2
      have hw : w.1.IsUnramified (maximalRealSubfield E) :=
        LocalFactor.NonabelianBrauer.isUnramified_of_isReal (IsTotallyReal.isReal w.1)
      refine DFunLike.ext _ _ fun y => ?_
      obtain ⟨y', hy'⟩ := LocalFactor.NonabelianBrauer.exists_localUnitNorm_eq v w.1 hw y
      have h1 := hP (IdeleClassGroup.ofCompletion (𝓞 (maximalRealSubfield L))
        (maximalRealSubfield L) w.1 y')
      rw [ideleClassNorm_ofCompletion v w y', hy'] at h1
      exact h1
    apply ContinuousMonoidHom.ext
    intro x
    have hx : x = ∏ v, HarrisDatum.single v
        (Units.map (Pi.evalMonoidHom (fun v : InfinitePlace (maximalRealSubfield E) =>
          v.Completion) v) x) := by
      apply Units.ext
      rw [Units.coe_prod]
      have hs (v : InfinitePlace (maximalRealSubfield E)) :
          ((HarrisDatum.single v (Units.map (Pi.evalMonoidHom
            (fun v : InfinitePlace (maximalRealSubfield E) => v.Completion) v) x) :
              (InfiniteAdeles (maximalRealSubfield E))ˣ) : InfiniteAdeles (maximalRealSubfield E)) =
            Pi.mulSingle v ((x : InfiniteAdeles (maximalRealSubfield E)) v) := by
        funext w
        exact InfiniteAdeleRing.ofCompletion_apply v _ w
      simp only [hs]
      exact (Finset.univ_prod_mulSingle _).symm
    rw [hx, map_prod]
    refine (Finset.prod_eq_one fun v _ => ?_).trans rfl
    rw [← HarrisDatum.infiniteComponent_eq_atInfinity, hcomp v]
    rfl
  · -- Factorization through the norm from `E` to its real subfield.
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨t, rfl⟩ := hsurjE x
    change η (RelativeWeilGroup.transfer c E L t) =
      η₀' (ideleClassNorm (K := maximalRealSubfield E) (L := E)
        (RelativeWeilGroup.transfer c E L t))
    rw [← RelativeWeilGroup.transferNormCompatibility c (maximalRealSubfield E) E L hRes t,
      hη₀', RelativeWeilGroup.projection_restrictionInclusion, ← hψ]
    exact (hφj _).symm

end CMNormKernelRealFactor

open CMNormKernelRealFactor in
/-- Harris (1998), Lemma 1.6: a Hecke character of a CM field trivial on the norms from a
cyclic CM extension is the pullback along the real norm of a finite-order character of the
maximal totally real subfield that is trivial on the whole archimedean factor. -/
theorem cmNormKernelRealFactor : CMNormKernelRealFactorStatement.{uE, uD} := by
  intro E D _ _ _ _ _ _ _ _ _ η hη
  -- An isomorphic copy of `D` in the universe of `E`.
  let ι : D →ₐ[E] AlgebraicClosure E := IsAlgClosed.lift
  let f : D ≃ₐ[E] ι.fieldRange := ι.equivFieldRange
  have : Module.Finite E ι.fieldRange := Module.Finite.equiv f.toLinearEquiv
  have : NumberField ι.fieldRange := NumberField.of_module_finite E ι.fieldRange
  have : IsGalois E ι.fieldRange := IsGalois.of_algEquiv f
  have : IsCyclic (ι.fieldRange ≃ₐ[E] ι.fieldRange) :=
    isCyclic_of_surjective f.autCongr.toMonoidHom f.autCongr.surjective
  have : IsTotallyComplex ι.fieldRange := isTotallyComplex_of_algebra E ι.fieldRange
  let : Algebra (maximalRealSubfield D) ι.fieldRange :=
    ((f : D →+* ι.fieldRange).comp (algebraMap (maximalRealSubfield D) D)).toAlgebra
  have : Module.Free (maximalRealSubfield D) ι.fieldRange := Module.Free.of_divisionRing _ _
  have : Algebra.IsQuadraticExtension (maximalRealSubfield D) ι.fieldRange :=
    { finrank_eq_two' := by
        rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D) D]
        exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) f.toRingEquiv
          (by ext; rfl)).symm }
  have : IsCMField ι.fieldRange := IsCMField.ofCMExtension (maximalRealSubfield D) ι.fieldRange
  -- Norm triviality transfers along the isomorphism.
  have hη' : η.IsTrivialOnNorm ι.fieldRange := by
    intro y
    have h := ideleClassNorm_equiv (K := E) (L := D) (K' := E) (L' := ι.fieldRange)
      (RingEquiv.refl E) f.toRingEquiv (fun x => f.commutes x)
      ((ideleClassEquiv f.toRingEquiv).symm y)
    rw [ContinuousMulEquiv.apply_symm_apply, ideleClassEquiv_refl] at h
    rw [h]
    exact hη _
  exact exists_realFactor_sameUniverse E ι.fieldRange η hη'

end Langlands.Global.Harris
