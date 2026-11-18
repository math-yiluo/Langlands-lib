import Langlands.AlgebraicGeometry.DvrStableNormalization.NormalLift
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Langlands.CommutativeAlgebra.RegularLocalFactorialProof

/-! # Normal stalks of flat DVR schemes with smooth generic and reduced special fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The generic fibre of a scheme over `Spec R`, as a scheme. -/
abbrev genericFibre (Z : Over (Spec (CommRingCat.of R))) : Scheme.{u} :=
  pullback Z.hom (Spec.algebraMap R (FractionRing R))

/-- Stalks at points of a smooth generic fibre are integrally closed domains. -/
theorem stalk_normal_of_generic (P : Over (Spec (CommRingCat.of R)))
    [Smooth (pullback.snd P.hom (Spec.algebraMap R (FractionRing R)))]
    (z : genericFibre P) :
    IsDomain (P.left.presheaf.stalk (genericι P z)) ∧
      IsIntegrallyClosed (P.left.presheaf.stalk (genericι P z)) := by
  have hiso : IsIso ((genericι P).stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 z
  let e := (asIso ((genericι P).stalkMap z)).commRingCatIsoToRingEquiv
  have hreg : IsRegularLocalRing
      ((pullback P.hom (Spec.algebraMap R (FractionRing R))).presheaf.stalk z) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
      (f := pullback.snd P.hom (Spec.algebraMap R (FractionRing R))) z
  have hdom := IsRegularLocalRing.isDomain
    ((pullback P.hom (Spec.algebraMap R (FractionRing R))).presheaf.stalk z)
  have hufd := Langlands.CommutativeAlgebra.regularLocalFactorial _ hreg
  have hic : IsIntegrallyClosed
      ((pullback P.hom (Spec.algebraMap R (FractionRing R))).presheaf.stalk z) := inferInstance
  exact ⟨e.toMulEquiv.isDomain, hic.of_equiv e.symm⟩

/-- Normal stalks from the affine criterion: flatness, reduced quotients by the uniformizer on
affine opens, and smooth generic fibre. -/
theorem hasNormalStalks_of_reduced_quotient (P : Over (Spec (CommRingCat.of R))) [Flat P.hom]
    [LocallyOfFiniteType P.hom]
    [Smooth (pullback.snd P.hom (Spec.algebraMap R (FractionRing R)))] {ϖ : R}
    (hϖ : Irreducible ϖ)
    (hsf : ∀ U : P.left.affineOpens, IsReduced (Γ(P.left, U.1) ⧸ Ideal.span {resSec P ϖ U.1})) :
    HasNormalStalks P.left := by
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    P.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hNoeth : IsNoetherianRing Γ(P.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hπ := resSec_mem_nonZeroDivisors P hϖ hU
  have hgen : ∀ (q : Ideal Γ(P.left, U)) [q.IsPrime], resSec P ϖ U ∉ q →
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
    intro q _ hq
    let y : PrimeSpectrum Γ(P.left, U) := ⟨q, inferInstance⟩
    have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
    have hyb : hU.fromSpec y ∈ P.left.basicOpen (pullSec P ϖ) := by
      have h1 : y ∈ hU.fromSpec ⁻¹ᵁ P.left.basicOpen (resSec P ϖ U) := by
        rw [hU.fromSpec_preimage_basicOpen]; exact hq
      have h2 : P.left.basicOpen (resSec P ϖ U) ≤ P.left.basicOpen (pullSec P ϖ) := by
        rw [Scheme.basicOpen_res]; exact inf_le_right
      exact h2 h1
    rw [← opensRange_genericι P hϖ] at hyb
    obtain ⟨z, hz⟩ := hyb
    obtain ⟨h1, h2⟩ := stalk_normal_of_generic P z
    rw [hz] at h1 h2
    let alg := TopCat.Presheaf.algebra_section_stalk P.left.presheaf ⟨hU.fromSpec y, hy⟩
    have hloc : IsLocalization.AtPrime (P.left.presheaf.stalk (hU.fromSpec y)) q :=
      hU.isLocalization_stalk' y hy
    let e : Localization.AtPrime q ≃ₐ[Γ(P.left, U)] P.left.presheaf.stalk (hU.fromSpec y) :=
      IsLocalization.algEquiv q.primeCompl _ _
    exact ⟨e.toMulEquiv.isDomain, h2.of_equiv e.symm.toRingEquiv⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let alg := TopCat.Presheaf.algebra_section_stalk P.left.presheaf ⟨x, hxU⟩
  obtain ⟨h1, h2⟩ :=
    Langlands.CommutativeAlgebra.FlatDvrNormality.isDomain_and_isIntegrallyClosed_localization
      hπ (hsf ⟨U, hU⟩) hgen p.asIdeal
  have hloc : IsLocalization.AtPrime (P.left.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime p.asIdeal ≃ₐ[Γ(P.left, U)] P.left.presheaf.stalk x :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  exact ⟨e.symm.toMulEquiv.isDomain, h2.of_equiv e.toRingEquiv⟩

/-- If `D` is a reduced pushout of `C ← A → K` and `π ∈ C` comes from an element of `A` killed
in `K`, and the quotient `C → C / π C` extends to a cocone, then `C / π C` is reduced. -/
lemma isReduced_quotient_of_isPushout {A C K D : CommRingCat.{u}} {a : A ⟶ C} {b : A ⟶ K}
    {c : C ⟶ D} {d : K ⟶ D} (hPO : IsPushout a b c d) (hD : IsReduced D) {s : A}
    (hbs : b s = 0) (d' : K ⟶ CommRingCat.of (C ⧸ Ideal.span {a s}))
    (hcomm : a ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a s})) = b ≫ d') :
    IsReduced (C ⧸ Ideal.span {a s}) := by
  let δ := hPO.desc (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a s}))) d' hcomm
  have hcδ : c ≫ δ = CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a s})) := hPO.inl_desc _ _ _
  have hcπ : c (a s) = 0 := by
    have := congrArg (fun h => h s) hPO.w
    simp only [CommRingCat.comp_apply] at this
    rw [this, hbs, map_zero]
  refine ⟨fun x hx => ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hn
  have hcz : IsNilpotent (c z) := ⟨n, by rw [← map_pow, ← hw, map_mul, hcπ, mul_zero]⟩
  have hcz0 : c z = 0 := hcz.eq_zero
  have := congrArg (fun h => h z) hcδ
  change δ (c z) = Ideal.Quotient.mk _ z at this
  rw [hcz0, map_zero] at this
  exact this.symm

/-- Geometric reducedness of the special fibre makes `Γ(U) / π Γ(U)` reduced for every affine
open `U`. -/
theorem isReduced_quotient_of_geometricallyReduced (P : Over (Spec (CommRingCat.of R)))
    [GeometricallyReduced P.hom] {ϖ : R} (hϖ : Irreducible ϖ) (U : P.left.affineOpens) :
    IsReduced (Γ(P.left, U.1) ⧸ Ideal.span {resSec P ϖ U.1}) := by
  have hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  let : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  let ι : Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ})) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ})))
  have hred : IsReduced (pullback P.hom ι) :=
    GeometricallyReduced.geometrically_isReduced (f := P.hom) ι (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have H := IsPullback.of_hasPullback P.hom ι
  have hPO := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U.1)
    le_top le_top rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _)
      (isAffineOpen_top _) U.2)
  let eR := Scheme.ΓSpecIso (CommRingCat.of R)
  let eK := Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {ϖ}))
  let a := P.hom.appLE ⊤ U.1 le_top
  have hπ : resSec P ϖ U.1 = a (eR.inv ϖ) := rfl
  have hb' : ι.appLE ⊤ ⊤ le_top = ι.appTop := (Scheme.Hom.app_eq_appLE ι).symm
  have hb : ∀ x, (ι.appLE ⊤ ⊤ le_top) x = ι.appTop x := fun x =>
    congrArg (fun h => h x) hb'
  have hnat : ∀ r : R, eK.hom (ι.appTop (eR.inv r)) = Ideal.Quotient.mk _ r := by
    intro r
    have := congrArg (fun h => h (eR.inv r)) (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    change eK.hom (ι.appTop (eR.inv r)) = Ideal.Quotient.mk _ (eR.hom (eR.inv r)) at this
    rw [this]
    congr 1
    exact eR.inv_hom_id_apply r
  have hbs : (ι.appLE ⊤ ⊤ le_top) (eR.inv ϖ) = 0 := by
    rw [hb]
    apply eK.commRingCatIsoToRingEquiv.injective
    change eK.hom _ = eK.hom 0
    rw [hnat, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self ϖ
  have hlift : ∀ r ∈ Ideal.span {ϖ},
      (Ideal.Quotient.mk (Ideal.span {a (eR.inv ϖ)})) (a (eR.inv r)) = 0 := by
    intro r hr
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let κlift : (R ⧸ Ideal.span {ϖ}) →+* Γ(P.left, U.1) ⧸ Ideal.span {a (eR.inv ϖ)} :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (a.hom.comp eR.inv.hom)) hlift
  let d' := eK.hom ≫ CommRingCat.ofHom κlift
  have hcomm : a ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a (eR.inv ϖ)})) =
      ι.appLE ⊤ ⊤ le_top ≫ d' := by
    ext x
    obtain ⟨r, rfl⟩ : ∃ r, eR.inv r = x := ⟨eR.hom x, by simp [eR]⟩
    change Ideal.Quotient.mk _ (a (eR.inv r)) = κlift (eK.hom ((ι.appLE ⊤ ⊤ le_top) (eR.inv r)))
    rw [hb, hnat]
    rfl
  rw [hπ]
  exact isReduced_quotient_of_isPushout hPO inferInstance hbs d' hcomm

/-- A flat, locally finite-type scheme over a DVR with smooth generic fibre and geometrically
reduced fibres has normal stalks. -/
theorem hasNormalStalks_of_flat_of_geometricallyReduced (P : Over (Spec (CommRingCat.of R)))
    [Flat P.hom] [LocallyOfFiniteType P.hom] [GeometricallyReduced P.hom]
    [Smooth (pullback.snd P.hom (Spec.algebraMap R (FractionRing R)))] :
    HasNormalStalks P.left := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact hasNormalStalks_of_reduced_quotient P hϖ
    (isReduced_quotient_of_geometricallyReduced P hϖ)

end Langlands.AlgebraicGeometry.DvrStableNormalization
