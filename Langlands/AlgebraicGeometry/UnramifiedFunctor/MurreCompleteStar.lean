import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseSpec
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletePunctured

/-! # Lifting over the closed points of the punctured part of a closed-fibre chart

For Step 2a of Murre's induction (Bourbaki exp. 294). Let `B` be a quotient of a local
noetherian, finite, formally unramified `R`-algebra `L`, with kernel `I`, and let `ξ ∈ F(Spec B)`
be pro-representable on complete local rings and a monomorphism. For a local artinian ring `A`
and an `R`-algebra map `β : L → A` whose prime `P = β⁻¹(m_A)` has `dim L/P = 1` and which
identifies `A` with a localization of the image of `L`, an element of `F(Spec A)` agreeing with
`ξ` on `Spec (A/IA)` forces `β(I) = 0`. The proof applies (F7) to the one-dimensional complete
local rings `L/ker(β mod m_A^(k+1))`, by induction on `k`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section TwoPoint

variable {A : Type u} [CommRing A] [IsLocalRing A] (P : Ideal A) [P.IsPrime]

/-- A local ring whose primes are a prime `P` and the maximal ideal has dimension one. -/
lemma twoPoint_ringKrullDim (hPm : P ≠ maximalIdeal A) (hmin : ∀ Q : Ideal A, Q.IsPrime → P ≤ Q)
    (htwo : ∀ Q : Ideal A, Q.IsPrime → Q ≠ P → Q = maximalIdeal A) : ringKrullDim A = 1 := by
  apply le_antisymm
  · rw [ringKrullDim, Order.krullDim_le_one_iff]
    intro x
    by_cases hx : x.asIdeal = P
    · left
      intro y _
      change x.asIdeal ≤ y.asIdeal
      rw [hx]
      exact hmin _ y.isPrime
    · right
      intro y _
      change y.asIdeal ≤ x.asIdeal
      rw [htwo _ x.isPrime hx]
      exact le_maximalIdeal y.isPrime.ne_top
  · rw [ringKrullDim, Order.one_le_krullDim_iff]
    refine ⟨⟨P, inferInstance⟩, closedPoint A, lt_of_le_of_ne ?_ ?_⟩
    · change P ≤ maximalIdeal A
      exact le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · intro h
      exact hPm (congrArg PrimeSpectrum.asIdeal h)

/-- In a noetherian local ring whose primes are `P` and the maximal ideal, and in which the
elements outside `P` are non-zero-divisors, `P` is the only associated prime. -/
lemma twoPoint_associatedPrimes [IsNoetherianRing A] (hPm : P ≠ maximalIdeal A)
    (htwo : ∀ Q : Ideal A, Q.IsPrime → Q ≠ P → Q = maximalIdeal A)
    (hnzd : ∀ s ∉ P, ∀ a : A, s * a = 0 → a = 0) : associatedPrimes A A = {P} := by
  have hsub : associatedPrimes A A ⊆ {P} := by
    intro Q hQ
    have hQp := hQ.isPrime
    by_contra hQP
    have hQm := htwo Q hQp hQP
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hQ
    obtain ⟨-, x, hx⟩ := hQ
    obtain ⟨s, hsm, hsP⟩ : ∃ s ∈ maximalIdeal A, s ∉ P :=
      SetLike.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (Ne.symm (Ne.symm hPm)))
    have hs : s ∈ Q := hQm ▸ hsm
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hs
    have hx0 := hnzd s hsP x hs
    apply hQp.ne_top
    rw [hx, hx0, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨Q, hQ⟩ := associatedPrimes.nonempty A A
  have hQP := hsub hQ
  rw [Set.mem_singleton_iff] at hQP
  subst hQP
  exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 hQ)

omit [IsLocalRing A] in
/-- A prime contained in all primes is the generic point. -/
lemma twoPoint_isGenericPoint (hmin : ∀ Q : Ideal A, Q.IsPrime → P ≤ Q) :
    IsGenericPoint (⟨P, inferInstance⟩ : PrimeSpectrum A) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← PrimeSpectrum.le_iff_specializes]
  exact hmin _ y.isPrime

end TwoPoint

section Helpers

lemma algHomOver_towerIso' (A : Type u) [CommRing A] [Algebra R A] {T T' : Type u} [CommRing T]
    [Algebra A T] [Algebra R T] [IsScalarTower R A T] [CommRing T'] [Algebra A T']
    [Algebra R T'] [IsScalarTower R A T'] (φ : T →ₐ[A] T') :
    algHomOver (ovR R A).hom φ ≫ (towerIso A T).hom =
      (towerIso A T').hom ≫ homR (φ.restrictScalars R) := by
  ext1
  simp only [Over.comp_left, towerIso_hom_left, homR_left]
  rfl

/-- A finite algebra over a local ring which is a local ring has local structure map. -/
lemma isLocalHom_of_finite [IsLocalRing R] (S : Type u) [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsLocalHom (algebraMap R S) := by
  have hc : ((maximalIdeal S).comap (algebraMap R S)).IsMaximal :=
    Ideal.IsMaximal.under R (maximalIdeal S)
  have heq := IsLocalRing.eq_maximalIdeal hc
  refine ⟨fun r hr ↦ ?_⟩
  by_contra h
  have hr' : r ∈ (maximalIdeal S).comap (algebraMap R S) := by
    rw [heq]
    exact h
  exact (mem_maximalIdeal _).1 hr' hr

/-- `LiftsTo` for an element pulled back from `ovR`, in terms of `ovR` and `homR`. -/
lemma liftsTo_of_tower {A1 : Type u} [CommRing A1] [Algebra R A1] {I1 : Ideal A1}
    (Λ : Type u) [CommRing Λ] [Algebra A1 Λ] [Algebra R Λ] [IsScalarTower R A1 Λ]
    (ξ0 : F.obj (op (ovR R (A1 ⧸ I1)))) (η0 : F.obj (op (ovR R Λ)))
    (h : F.map (homR ((Ideal.Quotient.mkₐ A1 (I1.map (algebraMap A1 Λ))).restrictScalars R)).op
        η0 = F.map (homR ((Ideal.quotientMapₐ (I1.map (algebraMap A1 Λ)) (Algebra.ofId A1 Λ)
          (fun _ hx ↦ Ideal.mem_map_of_mem _ hx)).restrictScalars R)).op ξ0) :
    LiftsTo (f := (ovR R A1).hom) Λ (F.map (towerIso A1 (A1 ⧸ I1)).hom.op ξ0) := by
  refine ⟨F.map (towerIso A1 Λ).hom.op η0, ?_⟩
  unfold restrictQuotient
  rw [← map_comp_op_apply, algHomOver_towerIso', map_comp_op_apply, h, ← map_comp_op_apply,
    ← map_comp_op_apply, algHomOver_towerIso']

variable (F) in
/-- Pro-representability of `ξ ∈ F(Spec B)` on complete local noetherian `R`-algebras. -/
def ProRep {B : Type u} [CommRing B] [Algebra R B] (ξB : F.obj (op (ovR R B))) : Prop :=
  ∀ (A1 : Type u) [CommRing A1] [IsLocalRing A1] [IsNoetherianRing A1]
    [IsAdicComplete (maximalIdeal A1) A1] [Algebra R A1] [IsLocalHom (algebraMap R A1)]
    (η : F.obj (op (ovR R A1))) (σ : B →ₐ[R] ResidueField A1),
    F.map (homR σ).op ξB = F.map (homR (IsScalarTower.toAlgHom R A1 (ResidueField A1))).op η →
    ∃ ψ : B →ₐ[R] A1, F.map (homR ψ).op ξB = η

end Helpers

section Star

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {L : Type u} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] [Algebra R L]
  [Module.Finite R L] [Algebra.FormallyUnramified R L]
  {B : Type u} [CommRing B] [Algebra R B] (π : L →ₐ[R] B) (hπ : Function.Surjective π)
  (ξB : F.obj (op (ovR R B)))

include hπ in
/-- The inductive step of the lifting argument: (F7) applied to `L / ker β`. -/
theorem star_step (hF7 : OneDimensionalLifting F) (hmono : IsMonoElement F ξB)
    (hPR : ProRep F ξB)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A]
    (β : L →ₐ[R] A)
    (hP : (maximalIdeal A).comap β ≠ maximalIdeal L)
    (hP' : ∀ Q : Ideal L, Q.IsPrime → (maximalIdeal A).comap β < Q → Q = maximalIdeal L)
    (hgen : ∀ a : A, ∃ r s : L, IsUnit (β s) ∧ a * β s = β r)
    (hIP : RingHom.ker π ≤ (maximalIdeal A).comap β)
    (hPI : ∀ p ∈ (maximalIdeal A).comap β, ∀ i ∈ RingHom.ker π, β p * β i = 0)
    (v : F.obj (op (ovR R A))) (βb : B →ₐ[R] A ⧸ (RingHom.ker π).map β)
    (hβb : βb.comp π = (Ideal.Quotient.mkₐ R _).comp β)
    (hv : F.map (homR (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β))).op v =
      F.map (homR βb).op ξB) :
    RingHom.ker π ≤ RingHom.ker β := by
  classical
  set 𝔮 : Ideal L := RingHom.ker β with h𝔮
  set P : Ideal L := (maximalIdeal A).comap β with hPdef
  let I : Ideal L := RingHom.ker π
  let ι : (L ⧸ 𝔮) →ₐ[R] A := Ideal.kerLiftAlg β
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective β
  have hιmk : ∀ l, ι (Ideal.Quotient.mk 𝔮 l) = β l := fun l ↦ Ideal.kerLiftAlg_mk β l
  have hnt : Nontrivial (L ⧸ 𝔮) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro h
    have h1 : (1 : L) ∈ 𝔮 := h ▸ Submodule.mem_top
    rw [h𝔮, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have : IsLocalRing (L ⧸ 𝔮) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective
  have hmkloc : IsLocalHom (Ideal.Quotient.mk 𝔮) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmkm : (maximalIdeal (L ⧸ 𝔮)).comap (Ideal.Quotient.mk 𝔮) = maximalIdeal L :=
    congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk 𝔮))
  let P1 : Ideal (L ⧸ 𝔮) := (maximalIdeal A).comap ι
  have hP1 : P1.IsPrime := Ideal.IsPrime.comap _
  have hP1P : P1.comap (Ideal.Quotient.mk 𝔮) = P := by
    ext l
    simp only [P1, hPdef, Ideal.mem_comap, hιmk]
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 inferInstance
  have hP1nil : ∀ x ∈ P1, x ^ N = 0 := by
    intro x hx
    apply hι
    rw [map_pow, map_zero]
    have h1 : ι x ^ N ∈ maximalIdeal A ^ N := Ideal.pow_mem_pow (show ι x ∈ maximalIdeal A from hx) N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    exact h1
  have hmin : ∀ Q : Ideal (L ⧸ 𝔮), Q.IsPrime → P1 ≤ Q := fun Q hQ x hx ↦
    hQ.mem_of_pow_mem N (by rw [hP1nil x hx]; exact Q.zero_mem)
  have hPm : P1 ≠ maximalIdeal (L ⧸ 𝔮) := by
    intro h
    apply hP
    rw [← hP1P, h, hmkm]
  have htwo : ∀ Q : Ideal (L ⧸ 𝔮), Q.IsPrime → Q ≠ P1 → Q = maximalIdeal (L ⧸ 𝔮) := by
    intro Q hQ hQP
    have hQ' : (Q.comap (Ideal.Quotient.mk 𝔮)).IsPrime := Ideal.IsPrime.comap _
    have hlt : P < Q.comap (Ideal.Quotient.mk 𝔮) := by
      rw [← hP1P]
      refine lt_of_le_of_ne (Ideal.comap_mono (hmin Q hQ)) (fun h ↦ hQP ?_)
      exact (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h).symm
    have hm := hP' _ hQ' hlt
    apply le_antisymm (le_maximalIdeal hQ.ne_top)
    intro x hx
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hl : l ∈ maximalIdeal L := by
      rw [← hmkm]
      exact hx
    rw [← hm] at hl
    exact hl
  have hnzd : ∀ s ∉ P1, ∀ a : L ⧸ 𝔮, s * a = 0 → a = 0 := by
    intro s hs a hsa
    have hu : IsUnit (ι s) := by
      by_contra h
      exact hs ((mem_maximalIdeal _).2 h)
    apply hι
    rw [map_zero]
    have h1 := congrArg ι hsa
    rw [map_mul, map_zero] at h1
    exact hu.mul_right_eq_zero.1 h1
  have hdim := twoPoint_ringKrullDim P1 hPm hmin htwo
  have hass := twoPoint_associatedPrimes P1 hPm htwo hnzd
  have hgp := twoPoint_isGenericPoint P1 hmin
  -- completeness and the structure map
  have : Module.Finite R (L ⧸ 𝔮) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R 𝔮).toLinearMap Ideal.Quotient.mk_surjective
  have := isLocalHom_of_finite (R := R) (L ⧸ 𝔮)
  have hm1 : maximalIdeal (L ⧸ 𝔮) = (maximalIdeal R).map (algebraMap R (L ⧸ 𝔮)) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := L ⧸ 𝔮)).symm
  have : IsAdicComplete (maximalIdeal (L ⧸ 𝔮)) (L ⧸ 𝔮) := by
    rw [hm1]
    exact isAdicComplete_map_of_finite (maximalIdeal R)
  -- the nilpotent ideal `I1 = I (L / ker β)`
  let I1 : Ideal (L ⧸ 𝔮) := I.map (Ideal.Quotient.mk 𝔮)
  have hP1map : P1 = P.map (Ideal.Quotient.mk 𝔮) := by
    rw [← hP1P, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hNI : nilradical (L ⧸ 𝔮) * I1 = ⊥ := by
    rw [eq_bot_iff]
    calc nilradical (L ⧸ 𝔮) * I1 ≤ P1 * I1 := Ideal.mul_mono_left (nilradical_le_prime P1)
      _ = (P * I).map (Ideal.Quotient.mk 𝔮) := by rw [hP1map, Ideal.map_mul]
      _ = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
        exact Ideal.mul_le.2 fun p hp i hi ↦ by
          rw [h𝔮, RingHom.mem_ker, map_mul]
          exact hPI p hp i hi
  have hI1P1 : I1 ≤ P1 := by
    rw [hP1map]
    exact Ideal.map_mono hIP
  have hP1N : P1 ≤ nilradical (L ⧸ 𝔮) := fun x hx ↦ mem_nilradical.2 ⟨N, hP1nil x hx⟩
  have hInil : IsNilpotent I1 := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, ← hNI]
    exact Ideal.mul_mono_left (hI1P1.trans hP1N)⟩
  -- the element `ξ'` over `(L / ker β) / I1`
  have hker1 : RingHom.ker π.toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ R I1).comp (Ideal.Quotient.mkₐ R 𝔮)).toRingHom := by
    intro i hi
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk I1 (Ideal.Quotient.mk 𝔮 i) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hi
  let β1 : B →ₐ[R] (L ⧸ 𝔮) ⧸ I1 := AlgHom.liftOfSurjective π hπ _ hker1
  have hβ1 : β1.comp π = (Ideal.Quotient.mkₐ R I1).comp (Ideal.Quotient.mkₐ R 𝔮) :=
    AlgHom.liftOfSurjective_comp _ _ _ _
  let ξ' : F.obj (op (algebraOver (ovR R (L ⧸ 𝔮)).hom ((L ⧸ 𝔮) ⧸ I1))) :=
    F.map (towerIso (L ⧸ 𝔮) ((L ⧸ 𝔮) ⧸ I1)).hom.op (F.map (homR β1).op ξB)
  -- the localization at the generic point is `A`
  let t : PrimeSpectrum (L ⧸ 𝔮) := ⟨P1, hP1⟩
  let : Algebra (L ⧸ 𝔮) A := ι.toRingHom.toAlgebra
  have : IsScalarTower R (L ⧸ 𝔮) A :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (ι.commutes r).symm)
  have hloc : IsLocalization P1.primeCompl A := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      by_contra h
      exact hs ((mem_maximalIdeal _).2 h)
    · intro a
      obtain ⟨r, s, hs, h⟩ := hgen a
      refine ⟨⟨Ideal.Quotient.mk 𝔮 r, ⟨Ideal.Quotient.mk 𝔮 s, ?_⟩⟩, ?_⟩
      · change ι (Ideal.Quotient.mk 𝔮 s) ∉ maximalIdeal A
        rw [hιmk]
        exact fun hm ↦ (mem_maximalIdeal _).1 hm hs
      · change a * ι (Ideal.Quotient.mk 𝔮 s) = ι (Ideal.Quotient.mk 𝔮 r)
        rw [hιmk, hιmk]
        exact h
    · intro x y hxy
      exact ⟨1, by rw [hι hxy]⟩
  let eΛ : Localization.AtPrime t.asIdeal ≃ₐ[L ⧸ 𝔮] A :=
    IsLocalization.algEquiv P1.primeCompl (Localization.AtPrime t.asIdeal) A
  let e' : A →ₐ[R] Localization.AtPrime t.asIdeal := eΛ.symm.toAlgHom.restrictScalars R
  have he'ι : ∀ x, e' (ι x) = algebraMap (L ⧸ 𝔮) (Localization.AtPrime t.asIdeal) x :=
    fun x ↦ eΛ.symm.commutes x
  let J : Ideal (Localization.AtPrime t.asIdeal) :=
    I1.map (algebraMap (L ⧸ 𝔮) (Localization.AtPrime t.asIdeal))
  have hē : (RingHom.ker π).map β ≤ J.comap e' := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hιmk, he'ι]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi)
  let ē : (A ⧸ (RingHom.ker π).map β) →ₐ[R] Localization.AtPrime t.asIdeal ⧸ J :=
    Ideal.quotientMapₐ J e' hē
  let qm := Ideal.quotientMapₐ J (Algebra.ofId (L ⧸ 𝔮) (Localization.AtPrime t.asIdeal))
    (fun _ hx ↦ Ideal.mem_map_of_mem _ hx)
  have hcomp : ē.comp βb = (qm.restrictScalars R).comp β1 := by
    apply AlgHom.ext
    intro b
    obtain ⟨l, rfl⟩ := hπ b
    have h1 := AlgHom.congr_fun hβb l
    have h2 := AlgHom.congr_fun hβ1 l
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
    change Ideal.Quotient.mk J (e' (β l)) =
      Ideal.Quotient.mk J (algebraMap (L ⧸ 𝔮) _ (Ideal.Quotient.mk 𝔮 l))
    rw [← hιmk, he'ι]
  have hmkē : ((Ideal.Quotient.mkₐ (L ⧸ 𝔮) J).restrictScalars R).comp e' =
      ē.comp (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β)) := by
    apply AlgHom.ext
    intro a
    rfl
  have hlift : LiftsTo (Localization.AtPrime t.asIdeal) ξ' := by
    refine liftsTo_of_tower _ _ (F.map (homR e').op v) ?_
    rw [map_homR_map_homR, map_homR_map_homR, hmkē, ← map_homR_map_homR, hv,
      map_homR_map_homR, hcomp]
  -- (F7)
  obtain ⟨ζ, hζ⟩ := hF7 (L ⧸ 𝔮) hdim ⟨P1, hass⟩ t hgp I1 hInil hNI (ovR R (L ⧸ 𝔮)).hom ξ' hlift
  have hζ' : F.map (homR (Ideal.Quotient.mkₐ R I1)).op ζ = F.map (homR β1).op ξB := by
    apply map_towerIso_injective (L ⧸ 𝔮) ((L ⧸ 𝔮) ⧸ I1)
    rw [← map_comp_op_apply, ← algebraOverBase_eq]
    exact hζ
  -- pro-representability
  have hI1m : I1 ≤ maximalIdeal (L ⧸ 𝔮) := hI1P1.trans (le_maximalIdeal hP1.ne_top)
  let r : ((L ⧸ 𝔮) ⧸ I1) →ₐ[R] ResidueField (L ⧸ 𝔮) :=
    Ideal.Quotient.liftₐ I1 (IsScalarTower.toAlgHom R (L ⧸ 𝔮) (ResidueField (L ⧸ 𝔮)))
      (fun a ha ↦ by
        change residue _ a = 0
        exact (residue_eq_zero_iff a).2 (hI1m ha))
  have hr : r.comp (Ideal.Quotient.mkₐ R I1) =
      IsScalarTower.toAlgHom R (L ⧸ 𝔮) (ResidueField (L ⧸ 𝔮)) := by
    apply AlgHom.ext
    intro a
    rfl
  obtain ⟨ψ, hψ⟩ := hPR (L ⧸ 𝔮) ζ (r.comp β1) (by
    rw [← map_homR_map_homR, ← hζ', map_homR_map_homR, hr])
  -- the monomorphism property and formal unramifiedness
  have hmk : (Ideal.Quotient.mkₐ R I1).comp ψ = β1 := by
    apply ArtinianBase.homR_injective
    apply hmono
    rw [← map_homR_map_homR, hψ, hζ']
  have hfu : ψ.comp π = Ideal.Quotient.mkₐ R 𝔮 := by
    apply Algebra.FormallyUnramified.lift_unique I1 hInil
    rw [← AlgHom.comp_assoc, hmk, hβ1]
  intro i hi
  have h1 := AlgHom.congr_fun hfu i
  rw [AlgHom.comp_apply, RingHom.mem_ker.1 hi, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm

include hπ in
/-- The lifting argument: an element of `F(Spec A)` agreeing with `ξ` on `Spec (A/IA)` forces
`β(I) = 0`. By induction on `k`, `β(I) ⊆ m_A^k`, applying `star_step` to `A/m_A^(k+1)`. -/
theorem star (hF7 : OneDimensionalLifting F) (hmono : IsMonoElement F ξB) (hPR : ProRep F ξB)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A]
    (β : L →ₐ[R] A)
    (hP : (maximalIdeal A).comap β ≠ maximalIdeal L)
    (hP' : ∀ Q : Ideal L, Q.IsPrime → (maximalIdeal A).comap β < Q → Q = maximalIdeal L)
    (hgen : ∀ a : A, ∃ r s : L, IsUnit (β s) ∧ a * β s = β r)
    (hIP : RingHom.ker π ≤ (maximalIdeal A).comap β)
    (v : F.obj (op (ovR R A))) (βb : B →ₐ[R] A ⧸ (RingHom.ker π).map β)
    (hβb : βb.comp π = (Ideal.Quotient.mkₐ R _).comp β)
    (hv : F.map (homR (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β))).op v =
      F.map (homR βb).op ξB) :
    ∀ i ∈ RingHom.ker π, β i = 0 := by
  have key : ∀ k : ℕ, (RingHom.ker π).map β ≤ maximalIdeal A ^ k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    | succ k ih =>
      have hMne : maximalIdeal A ^ (k + 1) ≠ ⊤ :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self k.succ_ne_zero)
      have : Nontrivial (A ⧸ maximalIdeal A ^ (k + 1)) := Ideal.Quotient.nontrivial_iff.2 hMne
      have : IsLocalRing (A ⧸ maximalIdeal A ^ (k + 1)) :=
        IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      have hmkloc : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (k + 1))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have hmkm : (maximalIdeal (A ⧸ maximalIdeal A ^ (k + 1))).comap
          (Ideal.Quotient.mk (maximalIdeal A ^ (k + 1))) = maximalIdeal A :=
        congrArg PrimeSpectrum.asIdeal
          (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (maximalIdeal A ^ (k + 1))))
      let β' : L →ₐ[R] A ⧸ maximalIdeal A ^ (k + 1) :=
        (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))).comp β
      have hPeq : (maximalIdeal (A ⧸ maximalIdeal A ^ (k + 1))).comap β' =
          (maximalIdeal A).comap β := by
        change ((maximalIdeal _).comap (Ideal.Quotient.mk (maximalIdeal A ^ (k + 1)))).comap β = _
        rw [hmkm]
      have hle : (RingHom.ker π).map β ≤
          ((RingHom.ker π).map β').comap (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro i hi
        exact Ideal.mem_map_of_mem β' hi
      let βb' : B →ₐ[R] (A ⧸ maximalIdeal A ^ (k + 1)) ⧸ (RingHom.ker π).map β' :=
        (Ideal.quotientMapₐ _ (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))) hle).comp βb
      have hgen' : ∀ a : A ⧸ maximalIdeal A ^ (k + 1), ∃ r s : L, IsUnit (β' s) ∧
          a * β' s = β' r := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨r, s, hs, h⟩ := hgen a
        refine ⟨r, s, hs.map (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))), ?_⟩
        change Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ (β s) = Ideal.Quotient.mk _ (β r)
        rw [← map_mul, h]
      have hIP' : RingHom.ker π ≤ (maximalIdeal (A ⧸ maximalIdeal A ^ (k + 1))).comap β' := by
        rw [hPeq]
        exact hIP
      have hPI' : ∀ p ∈ (maximalIdeal (A ⧸ maximalIdeal A ^ (k + 1))).comap β',
          ∀ i ∈ RingHom.ker π, β' p * β' i = 0 := by
        intro p hp i hi
        rw [hPeq] at hp
        change Ideal.Quotient.mk _ (β p) * Ideal.Quotient.mk _ (β i) = 0
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
        exact Ideal.mul_mem_mul hp (ih (Ideal.mem_map_of_mem β hi))
      have hβb' : βb'.comp π = (Ideal.Quotient.mkₐ R _).comp β' := by
        apply AlgHom.ext
        intro l
        have h1 := AlgHom.congr_fun hβb l
        simp only [AlgHom.comp_apply] at h1
        simp only [βb', AlgHom.comp_apply, h1]
        rfl
      have hv' : F.map (homR (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β'))).op
          (F.map (homR (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1)))).op v) =
          F.map (homR βb').op ξB := by
        have hc : (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β')).comp
            (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))) =
            (Ideal.quotientMapₐ _ (Ideal.Quotient.mkₐ R (maximalIdeal A ^ (k + 1))) hle).comp
              (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β)) :=
          AlgHom.ext fun _ ↦ rfl
        rw [map_homR_map_homR, hc, ← map_homR_map_homR, hv, map_homR_map_homR]
      have h := star_step π hπ ξB hF7 hmono hPR β' (by rw [hPeq]; exact hP)
        (by rw [hPeq]; exact hP') hgen' hIP' hPI' _ βb' hβb' hv'
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      have h1 := h hi
      rw [RingHom.mem_ker] at h1
      change Ideal.Quotient.mk _ (β i) = 0 at h1
      show β i ∈ maximalIdeal A ^ (k + 1)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 inferInstance
  intro i hi
  have h1 := key N (Ideal.mem_map_of_mem β hi)
  rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
  exact h1

end Star

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
