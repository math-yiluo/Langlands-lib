import Langlands.GroupScheme.Dilatation.ChartPresentation
import Mathlib.RingTheory.Localization.Algebra

/-! # Localization of dilatation algebras -/

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dilatation

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {A : Type v} [CommRing A] [Algebra R A]

/-- Extending the centre along a map of flat affine coordinate algebras induces a
map of affine dilatation algebras. -/
def blowupBaseMap {A' : Type*} [CommRing A'] [Algebra R A'] [Module.Flat R A']
    {r : R} (hr : r ≠ 0) (I : Ideal A) (f : A →ₐ[R] A') :
    blowupAlgebra r I →ₐ[R] blowupAlgebra r (I.map f.toRingHom) := by
  let J := I.map f.toRingHom
  refine liftBlowup hr I ((blowupMap r J).comp f) ?_
  intro a ha
  exact maps_centre_to_span J (AlgHom.id R (blowupAlgebra r J)) (f a)
    (Ideal.mem_map_of_mem f.toRingHom ha)

@[simp] theorem blowupBaseMap_algebraMap {A' : Type*} [CommRing A'] [Algebra R A'] [Module.Flat R A']
    {r : R} (hr : r ≠ 0) (I : Ideal A) (f : A →ₐ[R] A') (a : A) :
    blowupBaseMap hr I f (algebraMap A (blowupAlgebra r I) a) =
      algebraMap A' (blowupAlgebra r (I.map f.toRingHom)) (f a) :=
  DFunLike.congr_fun (liftBlowup_comp hr I ((blowupMap r (I.map f.toRingHom)).comp f)
    (fun a ha => maps_centre_to_span (I.map f.toRingHom)
      (AlgHom.id R (blowupAlgebra r (I.map f.toRingHom))) (f a)
      (Ideal.mem_map_of_mem f.toRingHom ha))) a

variable [Module.Flat R A]

private instance flat_localization_trans (M : Submonoid A) : Module.Flat R (Localization M) := by
  let : Module.Flat A (Localization M) := IsLocalization.flat (Localization M) M
  exact Module.Flat.trans R A _

section

variable {r : R} (hr : r ≠ 0) (I : Ideal A) (M : Submonoid A)

private abbrev blowupRing (r : R) (I : Ideal A) : Type v := blowupAlgebra r I

local notation "A'" => Localization M
local notation "I'" => I.map (algebraMap A A')
local notation "B₀" => blowupRing r I
local notation "B₁" => blowupRing r I'
local notation "N" => Algebra.algebraMapSubmonoid B₀ M
local notation "L" => Localization N

private abbrev localBaseMap : B₀ →ₐ[R] B₁ :=
  blowupBaseMap hr I (IsScalarTower.toAlgHom R A A')

private theorem localBaseMap_unit (b : N) : IsUnit (localBaseMap hr I M b) := by
  obtain ⟨a, ha, h⟩ := b.property
  rw [← h]
  change IsUnit (blowupBaseMap hr I (IsScalarTower.toAlgHom R A A') (algebraMap A B₀ a))
  rw [blowupBaseMap_algebraMap]
  exact (IsLocalization.map_units A' (⟨a, ha⟩ : M)).map (algebraMap A' B₁)

private def toLocalBlowup : L →ₐ[R] B₁ :=
  IsLocalization.liftAlgHom (localBaseMap_unit hr I M)

private theorem toLocalBlowup_algebraMap (b : B₀) :
    toLocalBlowup hr I M (algebraMap B₀ L b) = localBaseMap hr I M b :=
  IsLocalization.lift_eq (localBaseMap_unit hr I M) b

omit [IsDedekindDomain R] [Module.Flat R A] in
private theorem localScalarTower : IsScalarTower R A' L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply A A' L,
      IsScalarTower.algebraMap_apply A B₀ L, ← IsScalarTower.algebraMap_apply R A B₀,
      ← IsScalarTower.algebraMap_apply R B₀ L]

private def toLocalCoordinates : A' →ₐ[R] L :=
  letI := localScalarTower (r := r) I M
  IsScalarTower.toAlgHom R A' L

omit [IsDedekindDomain R] [Module.Flat R A] in
private theorem toLocalCoordinates_algebraMap (a : A) :
    toLocalCoordinates (r := r) I M (algebraMap A A' a) =
      algebraMap B₀ L (algebraMap A B₀ a) := by
  change algebraMap A' L (algebraMap A A' a) = _
  rw [← IsScalarTower.algebraMap_apply A A' L, IsScalarTower.algebraMap_apply A B₀ L]

omit [IsDedekindDomain R] [Module.Flat R A] in
private theorem toLocalCoordinates_mem (x : A') (hx : x ∈ I') :
    toLocalCoordinates (r := r) I M x ∈ Ideal.span {algebraMap R L r} := by
  let q := toLocalCoordinates (r := r) I M
  have hle : I' ≤ (Ideal.span {algebraMap R L r}).comap q.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change q (algebraMap A A' a) ∈ Ideal.span {algebraMap R L r}
    rw [toLocalCoordinates_algebraMap]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (maps_centre_to_span I (AlgHom.id R B₀) a ha)
    refine Ideal.mem_span_singleton.mpr ⟨algebraMap B₀ L b, ?_⟩
    change algebraMap A B₀ a = algebraMap R B₀ r * b at hb
    rw [hb, map_mul, ← IsScalarTower.algebraMap_apply R B₀ L]
  exact hle hx

private theorem flat_localBlowup : Module.Flat R L :=
  letI : Module.Flat B₀ L := IsLocalization.flat L N
  Module.Flat.trans R B₀ L

include hr in
private theorem exists_fromLocalBlowup :
    ∃ f : B₁ →ₐ[R] L, f.comp (blowupMap r I') = toLocalCoordinates (r := r) I M := by
  let : Module.Flat R L := flat_localBlowup (r := r) I M
  let q : A' →ₐ[R] L := toLocalCoordinates (r := r) I M
  have hq (x : A') (hx : x ∈ I') : q x ∈ Ideal.span {algebraMap R L r} :=
    toLocalCoordinates_mem (r := r) I M x hx
  exact ((existsUnique_liftBlowup_iff (A := A') (B := L) hr I' q).mpr hq).exists

private def fromLocalBlowup : B₁ →ₐ[R] L :=
  (exists_fromLocalBlowup hr I M).choose

private theorem fromLocalBlowup_algebraMap (x : A') :
    fromLocalBlowup hr I M (algebraMap A' B₁ x) = toLocalCoordinates (r := r) I M x :=
  AlgHom.congr_fun (exists_fromLocalBlowup hr I M).choose_spec x

private theorem fromLocalBlowup_comp_baseMap :
    (fromLocalBlowup hr I M).comp (localBaseMap hr I M) = IsScalarTower.toAlgHom R B₀ L := by
  let : Module.Flat R L := flat_localBlowup (r := r) I M
  apply blowupMap_ext (B := L) hr I
  apply AlgHom.ext
  intro a
  change fromLocalBlowup hr I M (blowupBaseMap hr I (IsScalarTower.toAlgHom R A A')
    (algebraMap A B₀ a)) = algebraMap B₀ L (algebraMap A B₀ a)
  exact (congrArg (fromLocalBlowup hr I M)
    (blowupBaseMap_algebraMap hr I (IsScalarTower.toAlgHom R A A') a)).trans
    ((fromLocalBlowup_algebraMap hr I M (algebraMap A A' a)).trans
      (toLocalCoordinates_algebraMap (r := r) I M a))

private theorem toLocalBlowup_comp_from :
    (toLocalBlowup hr I M).comp (fromLocalBlowup hr I M) = AlgHom.id R B₁ := by
  apply blowupMap_ext hr I'
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext M
  apply RingHom.ext
  intro a
  change toLocalBlowup hr I M (fromLocalBlowup hr I M (algebraMap A' B₁ (algebraMap A A' a))) =
    algebraMap A' B₁ (algebraMap A A' a)
  rw [fromLocalBlowup_algebraMap, toLocalCoordinates_algebraMap, toLocalBlowup_algebraMap]
  exact blowupBaseMap_algebraMap hr I (IsScalarTower.toAlgHom R A A') a

private theorem fromLocalBlowup_comp_to :
    (fromLocalBlowup hr I M).comp (toLocalBlowup hr I M) = AlgHom.id R L := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext N
  apply RingHom.ext
  intro b
  change fromLocalBlowup hr I M (toLocalBlowup hr I M (algebraMap B₀ L b)) = algebraMap B₀ L b
  rw [toLocalBlowup_algebraMap]
  exact DFunLike.congr_fun (fromLocalBlowup_comp_baseMap hr I M) b

/-- Localizing the affine dilatation algebra in elements from the original ring
agrees with dilating the localized original ring along the extended ideal. -/
def blowupLocalizationEquiv : L ≃ₐ[R] B₁ :=
  AlgEquiv.ofAlgHom (toLocalBlowup hr I M) (fromLocalBlowup hr I M)
    (toLocalBlowup_comp_from hr I M) (fromLocalBlowup_comp_to hr I M)

@[simp] theorem blowupLocalizationEquiv_algebraMap (b : B₀) :
    blowupLocalizationEquiv hr I M (algebraMap B₀ L b) =
      blowupBaseMap hr I (IsScalarTower.toAlgHom R A A') b :=
  toLocalBlowup_algebraMap hr I M b

local notation "Q₀" => (A ⧸ I)
local notation "Q₁" => (A' ⧸ I')
local notation "C₀" => blowupResidue r I
local notation "C₁" => blowupResidue r I'
local notation "J₀" => Ideal.span {algebraMap R B₀ r}
local notation "J₁" => Ideal.span {algebraMap R B₁ r}

/-- Reduction of the localization map to the special fibre. -/
def localizedResidueMap : C₀ →+* C₁ :=
  Ideal.quotientMap J₁ (localBaseMap hr I M).toRingHom (by
    apply Ideal.span_le.mpr
    rintro _ rfl
    change localBaseMap hr I M (algebraMap R B₀ r) ∈ J₁
    rw [AlgHom.commutes]
    exact Ideal.subset_span (Set.mem_singleton _))

/-- The localized special fibre is an algebra over the unlocalized special fibre. -/
@[instance_reducible]
def localizedResidueAlgebra : Algebra C₀ C₁ :=
  @RingHom.toAlgebra C₀ C₁ _ _ (localizedResidueMap hr I M)

private theorem localizedResidueMap_mk (b : B₀) :
    localizedResidueMap hr I M (Ideal.Quotient.mk J₀ b) =
      Ideal.Quotient.mk J₁ (localBaseMap hr I M b) := rfl

omit [IsDedekindDomain R] [Module.Flat R A] in
private theorem residueSubmonoid_eq :
    Algebra.algebraMapSubmonoid C₀ N =
      Algebra.algebraMapSubmonoid C₀ (Algebra.algebraMapSubmonoid Q₀ M) := by
  ext z
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨Ideal.Quotient.mk I a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨algebraMap A B₀ a, ⟨a, ha, rfl⟩, rfl⟩

private theorem isLocalization_localizedResidue_of_equiv
    (L₀ : Type v) [CommRing L₀] [Algebra B₀ L₀] [IsLocalization N L₀]
    [Algebra R L₀] [IsScalarTower R B₀ L₀]
    (e : L₀ ≃ₐ[R] B₁) (he : ∀ b : B₀, e (algebraMap B₀ L₀ b) = localBaseMap hr I M b) :
    @IsLocalization C₀ _
      (Algebra.algebraMapSubmonoid C₀ (Algebra.algebraMapSubmonoid Q₀ M)) C₁ _
      (localizedResidueAlgebra hr I M) := by
  let : Algebra C₀ C₁ := localizedResidueAlgebra hr I M
  let J := Ideal.map (algebraMap B₀ L₀) J₀
  have hJ : J₁ = J.map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
    change J₁ = Ideal.span {e (algebraMap B₀ L₀ (algebraMap R B₀ r))}
    rw [← IsScalarTower.algebraMap_apply R B₀ L₀, e.commutes]
  let E : (L₀ ⧸ J) ≃ₐ[C₀] C₁ := AlgEquiv.ofRingEquiv
      (f := Ideal.quotientEquiv J J₁ e.toRingEquiv hJ) (by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.quotientEquiv J J₁ e.toRingEquiv hJ
        (Ideal.Quotient.mk J (algebraMap B₀ L₀ b)) =
      localizedResidueMap hr I M (Ideal.Quotient.mk J₀ b)
    rw [Ideal.quotientEquiv_mk, localizedResidueMap_mk]
    exact congrArg (Ideal.Quotient.mk J₁) (he b))
  rw [← residueSubmonoid_eq (r := r) I M]
  exact IsLocalization.isLocalization_of_algEquiv _ E

/-- Reducing a localized dilatation is localization of the reduced algebra in
the corresponding elements of the centre. -/
theorem isLocalization_localizedResidue :
    @IsLocalization C₀ _
      (Algebra.algebraMapSubmonoid C₀ (Algebra.algebraMapSubmonoid Q₀ M)) C₁ _
      (localizedResidueAlgebra hr I M) :=
  isLocalization_localizedResidue_of_equiv hr I M L (blowupLocalizationEquiv hr I M)
    (blowupLocalizationEquiv_algebraMap hr I M)

@[instance_reducible]
private def centreLocalizedResidueAlgebra : Algebra Q₀ C₁ :=
  @RingHom.toAlgebra Q₀ C₁ _ _ ((algebraMap Q₁ C₁).comp (algebraMap Q₀ Q₁))

/-- On the special fibre, localizing the original ring base changes the
dilatation along localization of the centre. -/
def blowupResidueLocalizationEquiv :
    Q₁ ⊗[Q₀] C₀ ≃ₐ[Q₁] C₁ := by
  letI := localizedResidueAlgebra hr I M
  letI := centreLocalizedResidueAlgebra (r := r) I M
  let : IsScalarTower Q₀ Q₁ C₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Q₀ C₀ C₁ := IsScalarTower.of_algebraMap_eq fun z => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change algebraMap Q₁ C₁ (Ideal.Quotient.mk I' (algebraMap A A' a)) =
      localizedResidueMap hr I M (algebraMap Q₀ C₀ (Ideal.Quotient.mk I a))
    rw [algebraMap_blowupResidue_mk, algebraMap_blowupResidue_mk, localizedResidueMap_mk]
    exact (congrArg (Ideal.Quotient.mk J₁)
      (blowupBaseMap_algebraMap hr I (IsScalarTower.toAlgHom R A A') a)).symm
  let : @IsLocalization C₀ _ (Algebra.algebraMapSubmonoid C₀ (Algebra.algebraMapSubmonoid Q₀ M)) C₁ _ _ :=
    isLocalization_localizedResidue hr I M
  let : Algebra.IsPushout Q₀ C₀ Q₁ C₁ :=
    Algebra.isPushout_of_isLocalization (Algebra.algebraMapSubmonoid Q₀ M) Q₁ C₀ C₁
  let : Algebra.IsPushout Q₀ Q₁ C₀ C₁ := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv Q₀ Q₁ C₀ C₁

end

end Langlands.GroupScheme.Dilatation
