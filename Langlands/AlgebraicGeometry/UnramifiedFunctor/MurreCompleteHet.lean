import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteStar
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteEtaleLevel

/-! # Infinitesimal étaleness of the closed-fibre charts away from the closed point

For Step 2a of Murre's induction (Bourbaki exp. 294). Let `B = L/I` with `L` local
noetherian, finite étale over the complete local noetherian ring `R`, and let `ξ ∈ F(Spec B)` be
pro-representable on complete local rings and a monomorphism. If `F` is represented over the
punctured spectrum of `R`, then `ξ` is infinitesimally étale at every non-closed point of
`Spec B`: at the points `w` with `dim L/P_w = 1` by the lifting argument of
`MurreCompleteStar` and the Library's criterion in terms of levels, and at the other
non-closed points by generization. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section ChartIso

variable {L : Type u} [CommRing L] [Algebra R L] {B : Type u} [CommRing B] [Algebra R B]
  (π : L →ₐ[R] B) (hπ : Function.Surjective π)

/-- The isomorphism `Spec (L/I) ⟶ Spec B` over `Spec R`, for `I = ker π`. -/
def chartHom : chart R L (RingHom.ker π) ⟶ ovR R B :=
  (towerIso L (L ⧸ RingHom.ker π)).hom ≫
    homR (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

/-- Its inverse. -/
def chartInv : ovR R B ⟶ chart R L (RingHom.ker π) :=
  homR (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom ≫
    (towerIso L (L ⧸ RingHom.ker π)).inv

lemma chartInv_chartHom : chartInv π hπ ≫ chartHom π hπ = 𝟙 _ := by
  simp only [chartInv, chartHom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← homR_comp, show (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom.comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom = AlgHom.id R B from
    AlgHom.ext fun b ↦ (Ideal.quotientKerAlgEquivOfSurjective hπ).apply_symm_apply b, ArtinianBase.homR_id]

lemma chartHom_chartInv : chartHom π hπ ≫ chartInv π hπ = 𝟙 _ := by
  simp only [chartInv, chartHom, Category.assoc]
  rw [← Category.assoc (homR _) (homR _), ← homR_comp,
    show (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom.comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).toAlgHom = AlgHom.id R _ from
    AlgHom.ext fun x ↦ (Ideal.quotientKerAlgEquivOfSurjective hπ).symm_apply_apply x, ArtinianBase.homR_id,
    Category.id_comp, Iso.hom_inv_id]

instance : IsIso (chartInv π hπ) :=
  ⟨⟨chartHom π hπ, chartInv_chartHom π hπ, chartHom_chartInv π hπ⟩⟩

instance : IsOpenImmersion (chartInv π hπ).left :=
  have : IsIso (chartInv π hπ).left :=
    inferInstanceAs (IsIso ((Over.forget (Spec R)).map (chartInv π hπ)))
  inferInstance

end ChartIso

section Kill

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {L : Type u} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] [Algebra R L]
  [Module.Finite R L] [Algebra.FormallyUnramified R L]
  {B : Type u} [CommRing B] [Algebra R B] (π : L →ₐ[R] B) (hπ : Function.Surjective π)
  (ξB : F.obj (op (ovR R B)))

include hπ in
/-- The lifting condition at a point `w` of `Spec (L/I)` with `dim L/P_w = 1`, for the
surjections `O_w → A`. -/
theorem killAt_chart (hF5 : NilpotentInjective F) (hF7 : OneDimensionalLifting F)
    (hmono : IsMonoElement F ξB) (hPR : ProRep F ξB)
    (w : Spec (CommRingCat.of (L ⧸ RingHom.ker π)))
    (hw1 : primeOf (RingHom.ker π) w ≠ maximalIdeal L)
    (hw2 : ∀ Q : Ideal L, Q.IsPrime → primeOf (RingHom.ker π) w < Q → Q = maximalIdeal L)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (δ' : Ow (RingHom.ker π) w →+* A) (hδ' : Function.Surjective δ') :
    KillAt (F.map (chartHom π hπ).op ξB) w A
      (δ'.comp (algebraMap L (Ow (RingHom.ker π) w))) := by
  intro f hf J hJ u₀ hc hw v hv
  subst hf
  let β0 : L →+* A := δ'.comp (algebraMap L (Ow (RingHom.ker π) w))
  let : Algebra R A := (β0.comp (algebraMap R L)).toAlgebra
  let β : L →ₐ[R] A := { β0 with commutes' := fun _ ↦ rfl }
  have hβ : ∀ l, β l = β0 l := fun _ ↦ rfl
  -- the prime of `β`
  have hδloc : IsLocalHom δ' := IsLocalHom.of_surjective δ' hδ'
  have hPeq : (maximalIdeal A).comap β = primeOf (RingHom.ker π) w := by
    have h1 : (maximalIdeal A).comap δ' = maximalIdeal (Ow (RingHom.ker π) w) :=
      congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint δ')
    have h2 := Localization.AtPrime.under_maximalIdeal (I := primeOf (RingHom.ker π) w)
    change ((maximalIdeal A).comap δ').comap (algebraMap L _) = _
    rw [h1]
    exact h2
  have hgen : ∀ a : A, ∃ r s : L, IsUnit (β s) ∧ a * β s = β r := by
    intro a
    obtain ⟨x, rfl⟩ := hδ' a
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (primeOf (RingHom.ker π) w).primeCompl x
    refine ⟨r, s, (IsLocalization.map_units (Ow (RingHom.ker π) w) s).map δ', ?_⟩
    rw [hβ, hβ]
    change δ' _ * δ' (algebraMap L _ s) = δ' (algebraMap L _ r)
    rw [← map_mul, IsLocalization.mk'_spec]
  have hIP : RingHom.ker π ≤ (maximalIdeal A).comap β := by
    rw [hPeq]
    exact le_primeOf w
  -- the map `γ₀ : L/I → A/J`
  have : IsLocalRing (A ⧸ J) := Charts.isLocalRing_quotient hJ
  obtain ⟨γ₀, hγ₀⟩ := exists_specMap_ofHom u₀.left
  have h1 : (Ideal.Quotient.mk J).comp β0 = γ₀.comp (Ideal.Quotient.mk (RingHom.ker π)) := by
    rw [← specMap_ofHom_inj, ← hc, ← hγ₀, specMap_ofHom_comp]
  let γₐ : (L ⧸ RingHom.ker π) →ₐ[R] A ⧸ J :=
    { γ₀ with
      commutes' := fun r ↦ by
        change γ₀ (Ideal.Quotient.mk _ (algebraMap R L r)) = Ideal.Quotient.mk J (β0 _)
        rw [← RingHom.comp_apply, ← h1]
        rfl }
  have hIJ : (RingHom.ker π).map β ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    change ((Ideal.Quotient.mk J).comp β0) i = 0
    rw [h1, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]
  -- the induced map `B → A / IA`
  have hker : RingHom.ker π.toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ R ((RingHom.ker π).map β)).comp β).toRingHom := by
    intro i hi
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (β i) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hi
  let βb : B →ₐ[R] A ⧸ (RingHom.ker π).map β := AlgHom.liftOfSurjective π hπ _ hker
  have hβb : βb.comp π = (Ideal.Quotient.mkₐ R _).comp β :=
    AlgHom.liftOfSurjective_comp _ _ _ _
  -- `v` agrees with `ξ` on `Spec (A/J)`
  let q := Ideal.quotientKerAlgEquivOfSurjective hπ
  have hu : u₀ ≫ chartHom π hπ = (towerIso A (A ⧸ J)).hom ≫ homR (γₐ.comp q.symm.toAlgHom) := by
    ext1
    simp only [chartHom, Over.comp_left, homR_left, towerIso_hom_left, Category.id_comp]
    rw [← hγ₀, specMap_ofHom_comp]
    rfl
  have hv2 : F.map (homR (γₐ.comp q.symm.toAlgHom)).op ξB =
      F.map (homR (Ideal.Quotient.mkₐ R J)).op v := by
    apply map_towerIso_injective A (A ⧸ J)
    rw [← map_comp_op_apply, ← hu, ← map_comp_op_apply, ← algebraOverBase_eq, map_comp_op_apply]
    exact hv
  -- (F5) on `A / IA`
  have hIβne : (RingHom.ker π).map β ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_isNilpotent hJ) hIJ
  have : Nontrivial (A ⧸ (RingHom.ker π).map β) := Ideal.Quotient.nontrivial_iff.2 hIβne
  have : IsLocalRing (A ⧸ (RingHom.ker π).map β) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let J'' : Ideal (A ⧸ (RingHom.ker π).map β) := J.map (Ideal.Quotient.mk _)
  have hJ'' : IsNilpotent J'' := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    rw [Ideal.zero_eq_bot] at hn ⊢
    rw [← Ideal.map_pow, hn, Ideal.map_bot]
  let κ : (A ⧸ J) →ₐ[R] (A ⧸ (RingHom.ker π).map β) ⧸ J'' :=
    Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ R J'').comp (Ideal.Quotient.mkₐ R _))
      (fun a ha ↦ by
        change Ideal.Quotient.mk J'' (Ideal.Quotient.mk _ a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hκ1 : (Ideal.Quotient.mkₐ R J'').comp (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β)) =
      κ.comp (Ideal.Quotient.mkₐ R J) := AlgHom.ext fun _ ↦ rfl
  have hκ2 : (Ideal.Quotient.mkₐ R J'').comp βb = κ.comp (γₐ.comp q.symm.toAlgHom) := by
    apply AlgHom.ext
    intro b
    obtain ⟨l, rfl⟩ := hπ b
    have e1 := AlgHom.congr_fun hβb l
    simp only [AlgHom.comp_apply] at e1 ⊢
    have e2 : (q.symm.toAlgHom : B →ₐ[R] L ⧸ RingHom.ker π) (π l) = Ideal.Quotient.mk _ l :=
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply hπ l
    rw [e1, e2]
    change κ (Ideal.Quotient.mk J (β0 l)) = κ (γ₀ (Ideal.Quotient.mk _ l))
    rw [← RingHom.comp_apply, h1]
    rfl
  have hv' : F.map (homR (Ideal.Quotient.mkₐ R ((RingHom.ker π).map β))).op v =
      F.map (homR βb).op ξB := by
    apply hF5 (A ⧸ (RingHom.ker π).map β) J'' hJ'' (ovR R (A ⧸ (RingHom.ker π).map β)).hom
    rw [algebraOverBase_eq, map_comp_op_apply, map_comp_op_apply]
    congr 1
    rw [map_homR_map_homR, map_homR_map_homR, hκ1, hκ2, ← map_homR_map_homR,
      ← map_homR_map_homR (T := B), hv2]
  exact star π hπ ξB hF7 hmono hPR β (hPeq ▸ hw1) (hPeq ▸ hw2) hgen hIP v βb hβb hv'

end Kill

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
