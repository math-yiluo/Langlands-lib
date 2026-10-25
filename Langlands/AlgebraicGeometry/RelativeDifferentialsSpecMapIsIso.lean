import Langlands.AlgebraicGeometry.RelativeDifferentialsSpecMapIsIsoStatement
import Mathlib.RingTheory.Etale.Kaehler

/-! # Invertibility of the canonical differential comparison on spectra: proof -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme

namespace SpecDifferentials

section Algebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (P : Submonoid A)

/-- The comparison `Ω[A/R]_P ≃ Ω[A_P/R]`, made linear over the localization. -/
def localizedKaehlerEquiv :
    Ω[Localization P⁄R] →ₗ[Localization P] LocalizedModule P Ω[A⁄R] :=
  LinearMap.extendScalarsOfIsLocalization P (Localization P)
    (IsLocalizedModule.iso P (KaehlerDifferential.map R R A (Localization P))).symm.toLinearMap

/-- The derivation of a localization into the localized module of differentials. -/
def localizedDerivation : Derivation R (Localization P) (LocalizedModule P Ω[A⁄R]) :=
  (localizedKaehlerEquiv R A P).compDer (KaehlerDifferential.D R (Localization P))

lemma localizedDerivation_algebraMap (a : A) :
    localizedDerivation R A P (algebraMap A (Localization P) a) =
      LocalizedModule.mk (KaehlerDifferential.D R A a) 1 := by
  change (IsLocalizedModule.iso P (KaehlerDifferential.map R R A (Localization P))).symm
    (KaehlerDifferential.D R (Localization P) (algebraMap A (Localization P) a)) = _
  rw [← KaehlerDifferential.map_D R R A (Localization P), IsLocalizedModule.iso_symm_apply]

/-- The quotient rule for the localized derivation. -/
lemma localizedDerivation_mk (a : A) (g : P) :
    localizedDerivation R A P (Localization.mk a g) =
      LocalizedModule.mk ((g : A) • KaehlerDifferential.D R A a -
        a • KaehlerDifferential.D R A (g : A)) (g * g) := by
  have h1 : Localization.mk a g * algebraMap A (Localization P) g =
      algebraMap A (Localization P) a := by
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ a g
  have h2 := congrArg (localizedDerivation R A P) h1
  rw [Derivation.leibniz, localizedDerivation_algebraMap, localizedDerivation_algebraMap] at h2
  have h3 : Localization.mk 1 g * algebraMap A (Localization P) g = 1 := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_spec, map_one]
  calc localizedDerivation R A P (Localization.mk a g)
      = (Localization.mk 1 g * algebraMap A (Localization P) g) •
          localizedDerivation R A P (Localization.mk a g) := by rw [h3, one_smul]
    _ = Localization.mk 1 g • (LocalizedModule.mk (KaehlerDifferential.D R A a) 1 -
          Localization.mk a g • LocalizedModule.mk (KaehlerDifferential.D R A (g : A)) 1) := by
        rw [mul_smul, ← h2, add_sub_cancel_left]
    _ = _ := by
        rw [smul_sub, LocalizedModule.mk_smul_mk, LocalizedModule.mk_smul_mk,
          LocalizedModule.mk_smul_mk, sub_eq_add_neg, ← LocalizedModule.mk_neg,
          LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, mul_one,
          smul_sub, smul_add, smul_neg, smul_smul]
        module

end Algebra

section Sheaf

variable (R A : CommRingCat.{u}) [Algebra R A]

local notation "φ" => (CommRingCat.ofHom (algebraMap R A))

/-- The localized derivation at a point of the spectrum. -/
def pointDerivation (x : PrimeSpectrum A) :
    LocalizedModule x.asIdeal.primeCompl A →
      LocalizedModule x.asIdeal.primeCompl (KaehlerDifferential R A) :=
  fun s => localizedDerivation R A x.asIdeal.primeCompl s

lemma pointDerivation_mk (x : PrimeSpectrum A) (a : A) (g : x.asIdeal.primeCompl) :
    pointDerivation R A x (LocalizedModule.mk a g) =
      LocalizedModule.mk ((g : A) • KaehlerDifferential.D R A a -
        a • KaehlerDifferential.D R A (g : A)) (g * g) :=
  localizedDerivation_mk R A _ a g

lemma pointDerivation_zero (x : PrimeSpectrum A) : pointDerivation R A x 0 = 0 :=
  map_zero (localizedDerivation R A x.asIdeal.primeCompl)

lemma pointDerivation_add (x : PrimeSpectrum A) (s t : LocalizedModule x.asIdeal.primeCompl A) :
    pointDerivation R A x (s + t) = pointDerivation R A x s + pointDerivation R A x t :=
  map_add (localizedDerivation R A x.asIdeal.primeCompl) s t

lemma pointDerivation_mul (x : PrimeSpectrum A) (s t : LocalizedModule x.asIdeal.primeCompl A) :
    pointDerivation R A x (s * t) =
      s • pointDerivation R A x t + t • pointDerivation R A x s :=
  (localizedDerivation R A x.asIdeal.primeCompl).leibniz s t

/-- The pointwise derivation on sections of the structure sheaf of `Spec A`. -/
def tildeDerivationApp (U : (Spec A).Opens) :
    Γ(Spec A, U) →+ Γ(tilde (ModuleCat.of A (KaehlerDifferential R A)), U) where
  toFun s := ⟨fun x => pointDerivation R A x.1 (s.1 x), fun x => by
    obtain ⟨V, m, i, r, t, w⟩ := s.2 x
    refine ⟨V, m, i, t • KaehlerDifferential.D R A r - r • KaehlerDifferential.D R A t,
      t * t, fun y => ?_⟩
    obtain ⟨ht, hy⟩ := w y
    have hy' : s.1 (i y) = LocalizedModule.mk r ⟨t, ht⟩ := hy
    refine ⟨y.1.asIdeal.primeCompl.mul_mem ht ht, ?_⟩
    change pointDerivation R A (i y).1 (s.1 (i y)) = _
    rw [hy', pointDerivation_mk]
    rfl⟩
  map_zero' := Subtype.ext <| funext fun x => pointDerivation_zero R A x.1
  map_add' a b := Subtype.ext <| funext fun x => pointDerivation_add R A x.1 (a.1 x) (b.1 x)

/-- The relative derivation of the structure sheaf of `Spec A` into the sheaf associated
with the algebraic Kähler differentials. -/
def tildeDerivation :
    RelativeDerivation (Spec.map φ) (tilde (ModuleCat.of A (KaehlerDifferential R A))) where
  d {U} := tildeDerivationApp R A U.unop
  d_mul {U} a b := Subtype.ext <| funext fun x => pointDerivation_mul R A x.1 (a.1 x) (b.1 x)
  d_map f s := rfl
  d_app {U} a := by
    apply Subtype.ext
    funext x
    change pointDerivation R A x.1 (StructureSheaf.Localizations.comapFun
      (CommRingCat.ofHom (algebraMap R A)).hom.toSemilinearMap x.1
        (a.1 ⟨PrimeSpectrum.comap (algebraMap R A) x.1, x.2⟩)) = 0
    induction a.1 ⟨PrimeSpectrum.comap (algebraMap R A) x.1, x.2⟩ using
      LocalizedModule.induction_on with
    | h r t =>
      rw [StructureSheaf.Localizations.comapFun_mk, pointDerivation_mk]
      simp [Derivation.map_algebraMap]

/-- On global functions, the derivation into `tilde Ω` is the algebraic universal derivation. -/
lemma tildeDerivation_app_top (a : A) :
    (tildeDerivation R A).app ⊤ ((Scheme.ΓSpecIso A).inv a) =
      tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) ⊤ (KaehlerDifferential.D R A a) := by
  apply Subtype.ext
  funext x
  change pointDerivation R A x.1 (LocalizedModule.mk a 1) =
    LocalizedModule.mk (KaehlerDifferential.D R A a) 1
  rw [pointDerivation_mk]
  simp

/-- A relative derivation on `Spec A` is determined by its values on global functions. -/
lemma relativeDerivation_ext {M : (Spec A).Modules} (d d' : RelativeDerivation (Spec.map φ) M)
    (h : ∀ a : A, d.app ⊤ ((Scheme.ΓSpecIso A).inv a) = d'.app ⊤ ((Scheme.ΓSpecIso A).inv a)) :
    d = d' := by
  have hres : ∀ (W : (Spec A).Opens) (a : A),
      d.app W ((Spec A).presheaf.map W.leTop.op ((Scheme.ΓSpecIso A).inv a)) =
        d'.app W ((Spec A).presheaf.map W.leTop.op ((Scheme.ΓSpecIso A).inv a)) := by
    intro W a
    exact (d.app_restrict W.leTop _).trans
      ((congrArg _ (h a)).trans (d'.app_restrict W.leTop _).symm)
  have hconst : ∀ f g : A,
      d.app (PrimeSpectrum.basicOpen g)
          (StructureSheaf.const f g (PrimeSpectrum.basicOpen g) le_rfl :
            Γ(Spec A, PrimeSpectrum.basicOpen g)) =
        d'.app (PrimeSpectrum.basicOpen g)
          (StructureSheaf.const f g (PrimeSpectrum.basicOpen g) le_rfl :
            Γ(Spec A, PrimeSpectrum.basicOpen g)) := by
    intro f g
    set W : (Spec A).Opens := PrimeSpectrum.basicOpen g
    set c : Γ(Spec A, W) := StructureSheaf.const f g (PrimeSpectrum.basicOpen g) le_rfl
    have key : c * (Spec A).presheaf.map W.leTop.op ((Scheme.ΓSpecIso A).inv g) =
        (Spec A).presheaf.map W.leTop.op ((Scheme.ΓSpecIso A).inv f) := by
      apply Subtype.ext
      funext x
      change LocalizedModule.mk f ⟨g, x.2⟩ * LocalizedModule.mk g 1 = LocalizedModule.mk f 1
      rw [LocalizedModule.mk_mul_mk, LocalizedModule.mk_eq]
      exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩
    have e := congrArg (d.app W) key
    have e' := congrArg (d'.app W) key
    rw [RelativeDerivation.app_mul] at e e'
    rw [hres W g, hres W f, ← e'] at e
    have e2 := add_left_cancel e
    exact Scheme.Modules.isSMulRegular_of_le_basicOpen (M := M) (U := W) le_rfl e2
  ext U s
  change d.app U.unop s = d'.app U.unop s
  choose g hxg hgU f hf using fun x : U.unop =>
    StructureSheaf.exists_const (R := A) (M := A) U.unop s x.1 x.2
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M.presheaf, M.isSheaf⟩)
    (fun x : U.unop => (PrimeSpectrum.basicOpen (g x) : (Spec A).Opens)) U.unop
    (fun x => homOfLE (hgU x)) ?_ _ _ fun x => ?_
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxg ⟨y, hy⟩⟩
  · have := hconst (f x) (g x)
    rw [hf x] at this
    exact (d.app_restrict (homOfLE (hgU x)) s).symm.trans
      (this.trans (d'.app_restrict (homOfLE (hgU x)) s))

/-- The inverse comparison, induced by the derivation into `tilde Ω`. -/
def specMapInv :
    relativeDifferentials (Spec.map φ) ⟶ tilde (ModuleCat.of A (KaehlerDifferential R A)) :=
  relativeDifferentialsDesc (Spec.map φ) (tildeDerivation R A)

lemma specMapInv_app_D (a : A) :
    (specMapInv R A).app ⊤
      ((relativeDifferentialsDerivation (Spec.map φ)).app ⊤ ((Scheme.ΓSpecIso A).inv a)) =
      tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) ⊤ (KaehlerDifferential.D R A a) := by
  rw [← RelativeDerivation.postcomp_app, specMapInv, relativeDifferentialsDesc_fac,
    tildeDerivation_app_top]

lemma specMap_comp_specMapInv :
    relativeDifferentialsSpecMap R A ≫ specMapInv R A = 𝟙 _ := by
  apply (tilde.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, relativeDifferentialsSpecMap_adjoint]
  erw [Adjunction.homEquiv_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
  intro a
  have h := relativeDifferentialsSpecMap_adjoint_D R A a
  rw [relativeDifferentialsSpecMap_adjoint] at h
  change (specMapInv R A).app ⊤ (relativeDifferentialsSpecLinearMap R A
    (KaehlerDifferential.D R A a)) =
      tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) ⊤ (KaehlerDifferential.D R A a)
  rw [h]
  exact specMapInv_app_D R A a

lemma specMapInv_comp_specMap :
    specMapInv R A ≫ relativeDifferentialsSpecMap R A = 𝟙 _ := by
  apply relativeDifferentials_hom_ext (Spec.map φ)
  rw [RelativeDerivation.postcomp_comp, specMapInv, relativeDifferentialsDesc_fac,
    RelativeDerivation.postcomp_id]
  apply relativeDerivation_ext
  intro a
  rw [RelativeDerivation.postcomp_app, tildeDerivation_app_top,
    relativeDifferentialsSpecMap_app_toOpen_D]
  erw [show (⊤ : (Spec A).Opens).leTop.op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

end Sheaf

end SpecDifferentials

open SpecDifferentials in
/-- The canonical comparison `tilde Ω[A/R] ⟶ Ω_{Spec A/Spec R}` is an isomorphism. -/
theorem relativeDifferentialsSpecMapIsIso : RelativeDifferentialsSpecMapIsIsoStatement.{u} :=
  fun R A _ => ⟨⟨specMapInv R A, specMap_comp_specMapInv R A, specMapInv_comp_specMap R A⟩⟩

end Langlands.Scheme
