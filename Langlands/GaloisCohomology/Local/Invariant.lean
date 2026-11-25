import Langlands.Algebra.BrauerComparison.SeparableRestriction
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.Cohomology.Profinite.ClassFormation.Basic
import Langlands.GaloisCohomology.Field.Brauer
import Langlands.GaloisCohomology.Field.Hilbert90

/-!
# The invariant of a local field on `H²(Gal(Ksep/K), Ksepˣ)`

For a nonarchimedean local field `K` and a separable closure `Ksep`, the invariant
`H²(Gal(Ksep/K), Ksepˣ) ≃ ℚ/ℤ` in the cochain model of `Langlands.ProfiniteCohomology` is the
Library's `localBrauerInvariant K` read through `Br(K) ≅ H²` (`brauerEquiv`). Restriction to a
finite extension multiplies it by the degree (from the Library's
`localBrauerInvariant_scalarExtension`).

Open subgroups of `Gal(Ksep/K)` are identified with the Galois groups over their fixed fields
(`galFixedFieldEquivOpen`, `openCohomologyIso`); the fixed fields carry the Library's spectral
local-field structure (`Langlands.LocalField.FiniteExtension`), which gives the invariant on
`H²(U, Ksepˣ)` for every open subgroup `U` (`openInvariant`) and its restriction law
(`openInvariant_resOfLE`).
-/

noncomputable section

namespace Langlands.GaloisCohomology

open CategoryTheory IntermediateField Langlands.ProfiniteCohomology ClassFieldTheory.Local

universe u

section OpenSubgroup

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep]

/-- The fixed field of an intermediate field of a separable closure has that closure as its
separable closure. -/
instance isSepClosure_intermediateField [IsSepClosure K Ksep] (E : IntermediateField K Ksep) :
    IsSepClosure E Ksep :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ksep⟩

variable [IsGalois K Ksep]

theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    (fixedField (U : Subgroup Gal(Ksep/K))).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨(U : Subgroup Gal(Ksep/K)), U.isClosed⟩

instance finiteDimensional_fixedField_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    FiniteDimensional K (fixedField (U : Subgroup Gal(Ksep/K))) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)

instance isGalois_fixedField_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
  IsGalois.tower_top_of_isGalois K _ Ksep

/-- The index of an open subgroup is the degree of its fixed field. -/
theorem index_openSubgroup (U : OpenSubgroup Gal(Ksep/K)) :
    (U : Subgroup Gal(Ksep/K)).index =
      Module.finrank K (fixedField (U : Subgroup Gal(Ksep/K))) := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField_openSubgroup]

omit [IsGalois K Ksep] in
theorem fixedField_le_fixedField {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    fixedField (U : Subgroup Gal(Ksep/K)) ≤ fixedField (V : Subgroup Gal(Ksep/K)) :=
  fun _ hx => (mem_fixedField_iff _ _).2 fun σ hσ => (mem_fixedField_iff _ _).1 hx σ (h hσ)

/-- The relative index of open subgroups `V ≤ U` is the degree of the extension of their fixed
fields. -/
theorem relIndex_eq_finrank {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (V : Subgroup Gal(Ksep/K)).relIndex U =
      Module.finrank (fixedField (U : Subgroup Gal(Ksep/K)))
        (fixedField (V : Subgroup Gal(Ksep/K))) := by
  let _ := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower K (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := Subgroup.relIndex_mul_index (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)
  rw [index_openSubgroup, index_openSubgroup, ← Module.finrank_mul_finrank K
    (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))), mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

/-- The Galois group over the fixed field of an open subgroup `U`, mapped into `U`. -/
def galFixedFieldToOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →* (U : Subgroup Gal(Ksep/K)) :=
  (AlgEquiv.restrictScalarsHom K).codRestrict (U : Subgroup Gal(Ksep/K)) fun σ =>
    (fixingSubgroup_fixedField_openSubgroup U).le
      ((mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩)

@[simp]
theorem coe_galFixedFieldToOpen_apply (U : OpenSubgroup Gal(Ksep/K))
    (σ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) (x : Ksep) :
    ((galFixedFieldToOpen U σ : Gal(Ksep/K)) : Ksep → Ksep) x = σ x :=
  rfl

theorem continuous_galFixedFieldToOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldToOpen U) :=
  (BrauerComparison.krullRestrictScalars K (fixedField (U : Subgroup Gal(Ksep/K))) Ksep).continuous.subtype_mk _

theorem galFixedFieldToOpen_bijective (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Bijective (galFixedFieldToOpen U) := by
  refine ⟨fun σ τ h => AlgEquiv.ext fun x => ?_, fun τ => ?_⟩
  · exact congrArg (fun ρ : (U : Subgroup Gal(Ksep/K)) => (ρ : Gal(Ksep/K)) x) h
  · have hτ : (τ : Gal(Ksep/K)) ∈ (fixedField (U : Subgroup Gal(Ksep/K))).fixingSubgroup :=
      (fixingSubgroup_fixedField_openSubgroup U).ge τ.2
    exact ⟨fixingSubgroupEquiv _ ⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩

/-- An open subgroup `U` of `Gal(Ksep/K)` is the Galois group of `Ksep` over its fixed field. -/
def galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) ≃* (U : Subgroup Gal(Ksep/K)) :=
  MulEquiv.ofBijective (galFixedFieldToOpen U) (galFixedFieldToOpen_bijective U)

theorem galFixedFieldEquivOpen_toMonoidHom (U : OpenSubgroup Gal(Ksep/K)) :
    (galFixedFieldEquivOpen U).toMonoidHom = galFixedFieldToOpen U :=
  rfl

theorem continuous_galFixedFieldEquivOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldEquivOpen U).toMonoidHom :=
  continuous_galFixedFieldToOpen U

theorem continuous_galFixedFieldEquivOpen_symm (U : OpenSubgroup Gal(Ksep/K)) :
    Continuous (galFixedFieldEquivOpen U).symm.toMonoidHom :=
  (Continuous.homeoOfEquivCompactToT2 (f := (galFixedFieldEquivOpen U).toEquiv)
    (continuous_galFixedFieldToOpen U)).symm.continuous

/-- `galFixedFieldEquivOpen` as a continuous homomorphism. -/
abbrev galFixedFieldHomOpen (U : OpenSubgroup Gal(Ksep/K)) :
    Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))) →ₜ* (U : Subgroup Gal(Ksep/K)) :=
  ⟨(galFixedFieldEquivOpen U).toMonoidHom, continuous_galFixedFieldEquivOpen U⟩

/-- The identity of `Ksepˣ`, from the units module of `K` restricted to `U` to the units module of
the fixed field of `U`. -/
def unitsModuleOpenHom (U : OpenSubgroup Gal(Ksep/K)) :
    Rep.res (galFixedFieldEquivOpen U).toMonoidHom
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) ⟶
      unitsModule (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ksepˣ) (B := Additive Ksepˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

theorem unitsModuleOpenHom_bijective (U : OpenSubgroup Gal(Ksep/K)) :
    Function.Bijective (unitsModuleOpenHom U).hom :=
  Function.bijective_id

/-- `Hⁿ(U, Ksepˣ) ≅ Hⁿ(Gal(Ksep/Ksep^U), Ksepˣ)` for an open subgroup `U`. -/
def openCohomologyIso (U : OpenSubgroup Gal(Ksep/K)) (n : ℕ) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) n ≅
      cohomology (unitsModule (fixedField (U : Subgroup Gal(Ksep/K))) Ksep) n :=
  haveI := isIso_map_of_mulEquiv (galFixedFieldEquivOpen U)
    (continuous_galFixedFieldEquivOpen U) (continuous_galFixedFieldEquivOpen_symm U)
    (unitsModuleOpenHom U) (unitsModuleOpenHom_bijective U) n
  asIso (map (galFixedFieldHomOpen U) (unitsModuleOpenHom U) n)

theorem openCohomologyIso_hom (U : OpenSubgroup Gal(Ksep/K)) (n : ℕ) :
    (openCohomologyIso U n).hom = map (galFixedFieldHomOpen U) (unitsModuleOpenHom U) n :=
  rfl

/-- Hilbert 90 for the open subgroups of `Gal(Ksep/K)`. -/
theorem isZero_cohomology_one_res_unitsModule (U : OpenSubgroup Gal(Ksep/K)) :
    Limits.IsZero (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) 1) :=
  (isZero_cohomology_one_unitsModule (K := fixedField (U : Subgroup Gal(Ksep/K))) (L := Ksep)).of_iso
    (openCohomologyIso U 1)

end OpenSubgroup

section Restriction

variable (E F L : Type u) [Field E] [Field F] [Field L] [Algebra E F] [Algebra E L] [Algebra F L]
  [IsScalarTower E F L] [IsGalois E L] [IsGalois F L]

/-- Restriction `Hⁿ(Gal(L/E), Lˣ) → Hⁿ(Gal(L/F), Lˣ)` along an extension `F/E` inside `L`, as the
map of the Library's continuous restriction `continuousUnitRestriction E F L L` in the cochain
model. -/
def unitsRestriction (n : ℕ) : cohomology (unitsModule E L) n ⟶ cohomology (unitsModule F L) n :=
  map (BrauerComparison.krullRestriction E F L L)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients E F L L)) n

omit [IsGalois E L] [IsGalois F L] in
theorem krullRestriction_self_apply [Normal E L] [Algebra.IsAlgebraic F L] (σ : Gal(L/F)) (x : L) :
    BrauerComparison.krullRestriction E F L L σ x = σ x := by
  have h := AlgEquiv.restrictNormal_commutes (σ.restrictScalars E) L x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

theorem unitsModuleContinuousEquiv_unitsRestriction (n : ℕ) (x : cohomology (unitsModule E L) n) :
    unitsModuleContinuousEquiv F L n ((unitsRestriction E F L n).hom x) =
      BrauerComparison.continuousUnitRestriction E F L L n (unitsModuleContinuousEquiv E L n x) :=
  congrArg (fun f => f.hom x) (isoContinuousCohomology_naturality
    (BrauerComparison.krullRestriction E F L L)
    (BrauerComparison.continuousUnitRestrictionCoefficients E F L L) n)

variable [IsSepClosure E L] [IsSepClosure F L]

/-- Restriction corresponds to scalar extension of Brauer classes. -/
theorem unitsRestriction_brauerEquiv (a : BrauerGroup.{u, u} E) :
    (unitsRestriction E F L 2).hom (brauerEquiv E L a) =
      brauerEquiv F L (Brauer.scalarExtension F a) := by
  apply (unitsModuleContinuousEquiv F L 2).injective
  rw [unitsModuleContinuousEquiv_unitsRestriction, unitsModuleContinuousEquiv_brauerEquiv,
    unitsModuleContinuousEquiv_brauerEquiv,
    BrauerComparison.brauerContinuousEquiv_scalarExtension E F L L]

end Restriction

namespace Local

section Invariant

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The invariant `H²(Gal(Ksep/K), Ksepˣ) ≃ ℚ/ℤ` of a nonarchimedean local field: the Library's
`localBrauerInvariant K` read through `Br(K) ≅ H²(Gal(Ksep/K), Ksepˣ)`. -/
def invariant : cohomology (unitsModule K Ksep) 2 ≃+ RationalModIntegers :=
  (brauerEquiv K Ksep).symm.trans (localBrauerInvariant K)

@[simp]
theorem invariant_brauerEquiv (x : BrauerGroup.{u, u} K) :
    invariant K Ksep (brauerEquiv K Ksep x) = localBrauerInvariant K x := by
  simp [invariant]

theorem invariant_symm_apply (q : RationalModIntegers) :
    (invariant K Ksep).symm q = brauerEquiv K Ksep ((localBrauerInvariant K).symm q) :=
  rfl

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Algebra L Ksep] [IsScalarTower K L Ksep] [IsSepClosure L Ksep]

/-- Restriction to a finite extension `L` multiplies the invariant by `[L : K]`. -/
theorem invariant_unitsRestriction (hcont : Continuous (algebraMap K L))
    (x : cohomology (unitsModule K Ksep) 2) :
    invariant L Ksep ((unitsRestriction K L Ksep 2).hom x) =
      Module.finrank K L • invariant K Ksep x := by
  obtain ⟨a, rfl⟩ := (brauerEquiv K Ksep).surjective x
  rw [unitsRestriction_brauerEquiv, invariant_brauerEquiv, invariant_brauerEquiv,
    localBrauerInvariant_scalarExtension K L hcont]

end Invariant

section Spectral

/-! The Library's spectral local-field structure on a finite extension, and the facts about it
that the restriction law on open subgroups needs. -/

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] LocalGalois.localNormedField LocalGalois.localNormedField_complete

/-- A `K`-algebra map between finite extensions of `K` is continuous for their spectral norms. -/
theorem continuous_spectral_algHom (X Y : Type u) [Field X] [Algebra K X] [FiniteDimensional K X]
    [Field Y] [Algebra K Y] [FiniteDimensional K Y] (f : X →ₐ[K] Y) :
    letI := LocalField.FiniteExtension.normedField K X
    letI := LocalField.FiniteExtension.normedField K Y
    Continuous f := by
  let := LocalField.FiniteExtension.normedField K X
  let := LocalField.FiniteExtension.normedField K Y
  let := LocalField.FiniteExtension.normedAlgebra K X
  let := LocalField.FiniteExtension.normedAlgebra K Y
  exact f.toLinearMap.continuous_of_finiteDimensional

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The base field is a valuative extension of itself. -/
theorem valuativeExtension_self : ValuativeExtension K K :=
  ⟨fun _ _ => Iff.rfl⟩

/-- A `K`-algebra map between finite extensions of `K` respects their spectral valuations. -/
theorem valuativeExtension_spectral_algHom (X Y : Type u) [Field X] [Algebra K X]
    [FiniteDimensional K X] [Field Y] [Algebra K Y] [FiniteDimensional K Y] (f : X →ₐ[K] Y) :
    letI := LocalField.FiniteExtension.valuativeRel K X
    letI := LocalField.FiniteExtension.valuativeRel K Y
    letI := f.toRingHom.toAlgebra
    ValuativeExtension X Y := by
  let := valuativeExtension_self K
  exact spectralFiniteEmbedding_valuativeExtension K K X Y f

end Spectral

section Open

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type u} [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The invariant on `H²(U, Ksepˣ)` for an open subgroup `U` of `Gal(Ksep/K)`: the invariant of the
fixed field of `U` (a finite extension of `K`, with the Library's spectral local-field structure),
through `openCohomologyIso`. -/
def openInvariant (U : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) 2 ≃+
      RationalModIntegers :=
  let := LocalField.FiniteExtension.normedField K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.valuativeRel K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.isLocalField K (fixedField (U : Subgroup Gal(Ksep/K)))
  (openCohomologyIso U 2).toLinearEquiv.toAddEquiv.trans
    (invariant (fixedField (U : Subgroup Gal(Ksep/K))) Ksep)

theorem openInvariant_apply (U : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) 2) :
    letI := LocalField.FiniteExtension.normedField K (fixedField (U : Subgroup Gal(Ksep/K)))
    letI := LocalField.FiniteExtension.valuativeRel K (fixedField (U : Subgroup Gal(Ksep/K)))
    letI := LocalField.FiniteExtension.isLocalField K (fixedField (U : Subgroup Gal(Ksep/K)))
    openInvariant K U x =
      invariant (fixedField (U : Subgroup Gal(Ksep/K))) Ksep ((openCohomologyIso U 2).hom.hom x) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Restriction between open subgroups is restriction between their fixed fields. -/
theorem resOfLE_comp_openCohomologyIso {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) (n : ℕ) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    haveI : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K)))
        (fixedField (V : Subgroup Gal(Ksep/K))) Ksep := IsScalarTower.of_algebraMap_eq' rfl
    resOfLE (unitsModule K Ksep) (show (V : Subgroup Gal(Ksep/K)) ≤ U from h) n ≫
        (openCohomologyIso V n).hom =
      (openCohomologyIso U n).hom ≫
        unitsRestriction (fixedField (U : Subgroup Gal(Ksep/K)))
          (fixedField (V : Subgroup Gal(Ksep/K))) Ksep n := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) Ksep := IsScalarTower.of_algebraMap_eq' rfl
  rw [openCohomologyIso_hom, openCohomologyIso_hom, resOfLE, unitsRestriction]
  refine (map_comp _ _ _ _ n).symm.trans (Eq.trans ?_ (map_comp _ _ _ _ n))
  apply ProfiniteCohomology.map_congr
  · exact ContinuousMonoidHom.ext fun σ => Subtype.ext (AlgEquiv.ext fun x =>
      (krullRestriction_self_apply _ _ Ksep σ x).symm)
  · intro a
    exact Units.ext rfl

/-- The restriction law of the invariants of open subgroups:
`inv_V (res x) = [U : V] • inv_U x`. -/
theorem openInvariant_resOfLE (U V : OpenSubgroup Gal(Ksep/K)) (h : V ≤ U)
    (x : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) 2) :
    openInvariant K V
        ((resOfLE (unitsModule K Ksep) (show (V : Subgroup Gal(Ksep/K)) ≤ U from h) 2).hom x) =
      (V : Subgroup Gal(Ksep/K)).relIndex U • openInvariant K U x := by
  set EU := fixedField (U : Subgroup Gal(Ksep/K))
  set EV := fixedField (V : Subgroup Gal(Ksep/K))
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower EU EV Ksep := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K EU EV := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional EU EV := Module.Finite.of_restrictScalars_finite K _ _
  have hsq := congrArg (fun φ => φ.hom x) (resOfLE_comp_openCohomologyIso K h 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
  let := LocalField.FiniteExtension.normedField K EU
  let := LocalField.FiniteExtension.valuativeRel K EU
  let := LocalField.FiniteExtension.isLocalField K EU
  let := LocalField.FiniteExtension.normedField K EV
  let := LocalField.FiniteExtension.valuativeRel K EV
  let := LocalField.FiniteExtension.isLocalField K EV
  have : ValuativeExtension EU EV :=
    valuativeExtension_spectral_algHom K EU EV (IntermediateField.inclusion (fixedField_le_fixedField h))
  have hcont : Continuous (algebraMap EU EV) :=
    continuous_spectral_algHom K EU EV (IntermediateField.inclusion (fixedField_le_fixedField h))
  rw [openInvariant_apply, openInvariant_apply, hsq, invariant_unitsRestriction EU Ksep EV hcont,
    relIndex_eq_finrank h]

end Open

end Local

end Langlands.GaloisCohomology
