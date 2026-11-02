import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Picard.RelativeGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Localization.Ideal

/-! # Scheme-theoretic support of finitely generated quasi-coherent modules -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

/-- Localization commutes with the annihilator of a finite module. -/
theorem map_annihilator_of_isLocalizedModule
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (S : Submonoid R) [IsLocalization S A]
    (l : M →ₗ[R] N) [IsLocalizedModule S l] [Module.Finite R M] :
    (Module.annihilator R M).map (algebraMap R A) = Module.annihilator A N := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap R A r ∈ Module.annihilator A N
    rw [Module.mem_annihilator]
    intro y
    rw [IsScalarTower.algebraMap_smul A (R := R)]
    obtain ⟨⟨m, s⟩, hy⟩ := IsLocalizedModule.surj S l y
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units l s)).1
    change (s : R) • (r • y) = (s : R) • (0 : N)
    rw [smul_zero, smul_comm, ← Submonoid.smul_def, hy, ← l.map_smul,
      Module.mem_annihilator.mp hr, l.map_zero]
  · rw [← IsLocalization.under_le_under_iff S A]
    intro r hr
    change algebraMap R A r ∈ (Module.annihilator R M).map (algebraMap R A)
    obtain ⟨s, hs⟩ := ‹Module.Finite R M›
    have hz (m : s) : l (r • m.val) = l 0 := by
      rw [l.map_smul, ← IsScalarTower.algebraMap_smul A (R := R),
        Module.mem_annihilator.mp hr, l.map_zero]
    choose c hc using fun m : s => IsLocalizedModule.exists_of_eq (S := S) (hz m)
    refine (IsLocalization.algebraMap_mem_map_algebraMap_iff S A _ _).mpr ?_
    refine ⟨s.attach.prod (fun m => (c m : R)),
      S.prod_mem (fun m _ => (c m).property), ?_⟩
    rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun m => (c m : R))
      (Finset.mem_attach s m)
    rw [mul_smul, hk, mul_comm (c m : R), mul_smul]
    simpa only [Submonoid.smul_def, smul_zero] using
      congrArg (fun z : M => k • z) (hc m)

variable {X Y : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

/-- The quasi-coherent annihilator, specified on every affine open. -/
def annihilatorIdealSheaf (hM : HasFiniteAffineSections M) : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(M, U.1)
  map_ideal_basicOpen U f := by
    let : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    let : Module Γ(X, U.1) Γ(M, X.basicOpen f) :=
      Module.compHom Γ(M, X.basicOpen f)
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    let : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    change (Module.annihilator Γ(X, U.1) Γ(M, U.1)).map
      (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
        Module.annihilator Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)
    have := hM U
    have := U.2.isLocalization_basicOpen f
    have := AffineSections.isLocalizedModule_basicRestriction M f U.2
    exact map_annihilator_of_isLocalizedModule (Submonoid.powers f)
      (AffineSections.basicRestriction M f)

@[simp]
lemma annihilatorIdealSheaf_ideal (hM : HasFiniteAffineSections M) (U : X.affineOpens) :
    (annihilatorIdealSheaf M hM).ideal U =
      Module.annihilator Γ(X, U.1) Γ(M, U.1) := rfl

/-- The closed subscheme locally cut out by the annihilator of the module. -/
def schemeTheoreticSupport (hM : HasFiniteAffineSections M) : Scheme.{u} :=
  (annihilatorIdealSheaf M hM).subscheme

/-- The closed immersion of the scheme-theoretic support into the ambient scheme. -/
def schemeTheoreticSupportι (hM : HasFiniteAffineSections M) :
    schemeTheoreticSupport M hM ⟶ X :=
  (annihilatorIdealSheaf M hM).subschemeι

instance (hM : HasFiniteAffineSections M) :
    IsClosedImmersion (schemeTheoreticSupportι M hM) :=
  inferInstanceAs (IsClosedImmersion (annihilatorIdealSheaf M hM).subschemeι)

@[simp]
lemma ker_schemeTheoreticSupportι (hM : HasFiniteAffineSections M) :
    (schemeTheoreticSupportι M hM).ker = annihilatorIdealSheaf M hM :=
  (annihilatorIdealSheaf M hM).ker_subschemeι

@[simp]
lemma ker_schemeTheoreticSupportι_app (hM : HasFiniteAffineSections M)
    (U : X.affineOpens) :
    RingHom.ker ((schemeTheoreticSupportι M hM).app U.1).hom =
      Module.annihilator Γ(X, U.1) Γ(M, U.1) :=
  (annihilatorIdealSheaf M hM).ker_subschemeι_app U

/-- The affine rings of the support are precisely the annihilator quotients. -/
def schemeTheoreticSupportObjIso (hM : HasFiniteAffineSections M) (U : X.affineOpens) :
    Γ(schemeTheoreticSupport M hM, schemeTheoreticSupportι M hM ⁻¹ᵁ U.1) ≅
      CommRingCat.of (Γ(X, U.1) ⧸ Module.annihilator Γ(X, U.1) Γ(M, U.1)) :=
  (annihilatorIdealSheaf M hM).subschemeObjIso U

lemma range_schemeTheoreticSupportι (hM : HasFiniteAffineSections M) :
    Set.range (schemeTheoreticSupportι M hM) = (annihilatorIdealSheaf M hM).support :=
  (annihilatorIdealSheaf M hM).range_subschemeι

lemma isClosed_range_schemeTheoreticSupportι (hM : HasFiniteAffineSections M) :
    IsClosed (Set.range (schemeTheoreticSupportι M hM)) := by
  rw [range_schemeTheoreticSupportι]
  exact (annihilatorIdealSheaf M hM).support.isClosed

/-- The affine annihilator characterization of Stacks Lemma 29.5.4(1). -/
def IsSchemeTheoreticSupport {Z : Scheme.{u}} (ι : Z ⟶ X) : Prop :=
  IsClosedImmersion ι ∧ ∀ U : X.affineOpens,
    RingHom.ker (ι.app U.1).hom = Module.annihilator Γ(X, U.1) Γ(M, U.1)

lemma isSchemeTheoreticSupport_schemeTheoreticSupportι (hM : HasFiniteAffineSections M) :
    IsSchemeTheoreticSupport M (schemeTheoreticSupportι M hM) :=
  ⟨inferInstance, ker_schemeTheoreticSupportι_app M hM⟩

lemma isSchemeTheoreticSupport_iff_ker_eq (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι] :
    IsSchemeTheoreticSupport M ι ↔ ι.ker = annihilatorIdealSheaf M hM := by
  constructor
  · intro h
    ext U
    rw [Scheme.Hom.ker_apply, h.2 U, annihilatorIdealSheaf_ideal]
  · intro h
    refine ⟨inferInstance, fun U => ?_⟩
    rw [← Scheme.Hom.ker_apply, h, annihilatorIdealSheaf_ideal]

/-- Any closed subscheme satisfying the source's affine characterization
is canonically isomorphic over `X` to the constructed support. -/
def schemeTheoreticSupportIso (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) (hι : IsSchemeTheoreticSupport M ι) :
    Z ≅ schemeTheoreticSupport M hM := by
  letI := hι.1
  have hker : (schemeTheoreticSupportι M hM).ker = ι.ker :=
    (ker_schemeTheoreticSupportι M hM).trans
      ((isSchemeTheoreticSupport_iff_ker_eq M hM ι).mp hι).symm
  let g := IsClosedImmersion.lift (schemeTheoreticSupportι M hM) ι hker.le
  haveI : IsIso g := IsClosedImmersion.isIso_lift _ _ hker
  exact asIso g

@[reassoc (attr := simp)]
lemma schemeTheoreticSupportIso_hom_ι (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) (hι : IsSchemeTheoreticSupport M ι) :
    (schemeTheoreticSupportIso M hM ι hι).hom ≫ schemeTheoreticSupportι M hM = ι :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma schemeTheoreticSupportIso_inv_ι (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) (hι : IsSchemeTheoreticSupport M ι) :
    (schemeTheoreticSupportIso M hM ι hι).inv ≫ ι = schemeTheoreticSupportι M hM := by
  rw [Iso.inv_comp_eq]
  exact (schemeTheoreticSupportIso_hom_ι M hM ι hι).symm

/-- The annihilator is the largest ideal sheaf acting by zero on affine sections. -/
lemma le_annihilatorIdealSheaf_iff (hM : HasFiniteAffineSections M) (I : X.IdealSheafData) :
    I ≤ annihilatorIdealSheaf M hM ↔
      ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ I.ideal U →
        ∀ m : Γ(M, U.1), r • m = 0 := by
  simp only [Scheme.IdealSheafData.le_def, annihilatorIdealSheaf_ideal,
    SetLike.le_def, Module.mem_annihilator]

/-- The support factors through every closed subscheme whose defining ideal
annihilates the module on affine sections. -/
def schemeTheoreticSupportLift (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    (hι : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ ι.ker.ideal U →
      ∀ m : Γ(M, U.1), r • m = 0) : schemeTheoreticSupport M hM ⟶ Z :=
  IsClosedImmersion.lift ι (schemeTheoreticSupportι M hM)
    (by rw [ker_schemeTheoreticSupportι]; exact (le_annihilatorIdealSheaf_iff M hM _).mpr hι)

@[reassoc (attr := simp)]
lemma schemeTheoreticSupportLift_ι (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    (hι : ∀ (U : X.affineOpens) (r : Γ(X, U.1)), r ∈ ι.ker.ideal U →
      ∀ m : Γ(M, U.1), r • m = 0) :
    schemeTheoreticSupportLift M hM ι hι ≫ ι = schemeTheoreticSupportι M hM :=
  IsClosedImmersion.lift_fac _ _ _

/-- Properness of the actual annihilator subscheme over the base. -/
def HasProperSupport (f : X ⟶ Y) (hM : HasFiniteAffineSections M) : Prop :=
  IsProper (schemeTheoreticSupportι M hM ≫ f)

lemma hasProperSupport_of_isProper (f : X ⟶ Y) [IsProper f]
    (hM : HasFiniteAffineSections M) : HasProperSupport M f hM := by
  dsimp [HasProperSupport]
  infer_instance

/-- Properness is independent of the choice of closed subscheme realizing the
source's affine annihilator characterization. -/
lemma hasProperSupport_iff (f : X ⟶ Y) (hM : HasFiniteAffineSections M)
    {Z : Scheme.{u}} (ι : Z ⟶ X) (hι : IsSchemeTheoreticSupport M ι) :
    HasProperSupport M f hM ↔ IsProper (ι ≫ f) := by
  constructor
  · intro h
    let : IsProper (schemeTheoreticSupportι M hM ≫ f) := h
    rw [← schemeTheoreticSupportIso_hom_ι M hM ι hι, Category.assoc]
    infer_instance
  · intro h
    let := h
    dsimp [HasProperSupport]
    rw [← schemeTheoreticSupportIso_inv_ι M hM ι hι, Category.assoc]
    infer_instance

/-- The constructed proper-support predicate is equivalent to existence of a
proper closed subscheme with the source's affine annihilator characterization. -/
lemma hasProperSupport_iff_exists (f : X ⟶ Y) (hM : HasFiniteAffineSections M) :
    HasProperSupport M f hM ↔ ∃ (Z : Scheme.{u}) (ι : Z ⟶ X),
      IsSchemeTheoreticSupport M ι ∧ IsProper (ι ≫ f) := by
  constructor
  · intro h
    exact ⟨schemeTheoreticSupport M hM, schemeTheoreticSupportι M hM,
      isSchemeTheoreticSupport_schemeTheoreticSupportι M hM, h⟩
  · rintro ⟨Z, ι, hι, hp⟩
    exact (hasProperSupport_iff M f hM ι hι).mpr hp

/-- Every finite quasi-coherent module on every test-scheme base change of a
proper ambient scheme has proper scheme-theoretic support over that test scheme. -/
lemma hasProperSupport_relativeSpace {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (T : Over S) (M : ((Picard.relativeSpace f).obj T).Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) :
    HasProperSupport M ((Picard.relativeProjection f).app T) hM := by
  have : IsProper ((Picard.relativeProjection f).app T) :=
    inferInstanceAs (IsProper (pullback.fst T.hom f))
  exact hasProperSupport_of_isProper M _ hM

end Langlands.AlgebraicGeometry.Modules
