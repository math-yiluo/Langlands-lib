import Langlands.GaloisCohomology.CyclotomicKilling.FiniteModuleStatement
import Langlands.GaloisCohomology.Global.BrauerSequence.Proof
import Langlands.GaloisCohomology.Global.Units.ComplexRestriction
import Langlands.GaloisCohomology.Local.Dimension

/-!
# Cyclotomic restriction of finite primary cohomology classes

Prime-torsion Brauer classes and the Kummer sequence give a cohomological dimension
bound for the fixing group of the corresponding prime-power cyclotomic tower.
Degree-two classes with finite primary coefficients then vanish after restriction
to a finite layer.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open IntermediateField
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension Topology

universe u

noncomputable section

section Brauer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- A Brauer class killed by a prime `ℓ` restricts to zero over a finite subfield of some
`K(μ_{ℓ ^ r})`. -/
private theorem exists_brauerRestriction_eq_zero_cyclotomic {ℓ : ℕ} (hℓ : ℓ.Prime)
    (x : cohomology (unitsModule K Ω) 2) (hx : ℓ • x = 0) :
    ∃ (r : ℕ) (E : IntermediateField K Ω) (_ : FiniteDimensional K E),
      E ≤ cyclotomicLayer K Ω (ℓ ^ r) ∧ brauerRestriction E x = 0 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  let T := (brauerLocalization_finite_support ι x).toFinset
  obtain ⟨k, hk⟩ := Langlands.Global.CyclotomicSplitting.exists_pow_dvd_localDegree K ℓ 1 T
  let X := Langlands.Global.CyclotomicSplitting.xiField K ℓ k
  let g : Langlands.Global.CyclotomicSplitting.Layer K ℓ k →ₐ[K] Ω := IsSepClosed.lift
  let E : IntermediateField K Ω := X.map g
  let φ : X ≃ₐ[K] E := IntermediateField.equivMap X g
  have hE : FiniteDimensional K E := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have := NumberField.of_module_finite K E
  refine ⟨k + 3, E, hE, ?_, brauerRestriction_eq_zero_of_isComplex ι E ?_ x ℓ hx ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact fieldRange_le_cyclotomicLayer (ℓ ^ (k + 3)) g ⟨y, rfl⟩
  · intro w
    rw [← InfinitePlace.not_isReal_iff_isComplex, ← InfinitePlace.isReal_comap_iff φ.toRingEquiv,
      InfinitePlace.not_isReal_iff_isComplex]
    exact Langlands.Global.CyclotomicSplitting.isComplex_xiField K ℓ k _
  · intro v hv w _
    have hT : v ∈ T := by simpa [T] using hv
    simpa only [localDegree, pow_one] using localDegreesDvd_of_algEquiv φ hk v hT w

end Brauer

section Restriction

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

private theorem fixingSubgroup_restrictScalars_le (U : OpenSubgroup Gal(Ω/K))
    (E : IntermediateField (fixedField (U : Subgroup Gal(Ω/K))) Ω) :
    (E.restrictScalars K).fixingSubgroup ≤ (U : Subgroup Gal(Ω/K)) := by
  have h : fixedField (U : Subgroup Gal(Ω/K)) ≤ E.restrictScalars K :=
    fun x hx => E.algebraMap_mem ⟨x, hx⟩
  exact (fixingSubgroup_antitone h).trans (fixingSubgroup_fixedField_openSubgroup U).le

/-- A zero Brauer restriction gives a zero restriction on the corresponding subgroups. -/
private theorem resOfLE_eq_zero_of_brauerRestriction_eq_zero [NumberField K]
    (U : OpenSubgroup Gal(Ω/K))
    (E : IntermediateField (fixedField (U : Subgroup Gal(Ω/K))) Ω)
    (x : cohomology (Rep.res (U : Subgroup Gal(Ω/K)).subtype (unitsModule K Ω)) 2)
    (hx : letI := NumberField.of_module_finite K (fixedField (U : Subgroup Gal(Ω/K)))
      brauerRestriction E ((openCohomologyIso U 2).hom.hom x) = 0) :
    (resOfLE (unitsModule K Ω) (fixingSubgroup_restrictScalars_le U E) 2).hom x = 0 := by
  let F := fixedField (U : Subgroup Gal(Ω/K))
  let V := (E.restrictScalars K).fixingSubgroup
  have : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq' rfl
  let e : Gal(Ω/E) ≃* V := (E.restrictScalars K).fixingSubgroupEquiv.symm
  have he : Continuous e.toMonoidHom :=
    (BrauerComparison.krullRestrictScalars K E Ω).continuous.subtype_mk _
  have he' : Continuous e.symm.toMonoidHom :=
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  let ψ : Gal(Ω/E) →ₜ* V := ⟨e.toMonoidHom, he⟩
  let f : Rep.res (ψ : Gal(Ω/E) →* V) (Rep.res V.subtype (unitsModule K Ω)) ⟶
      unitsModule E Ω :=
    Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ωˣ) (B := Additive Ωˣ) (AddMonoidHom.id _),
      fun σ => by ext a; rfl⟩
  have hf : Function.Bijective f.hom := Function.bijective_id
  have : IsIso (map ψ f 2) := isIso_map_of_mulEquiv e he he' f hf 2
  have hcomp :
      resOfLE (unitsModule K Ω) (fixingSubgroup_restrictScalars_le U E) 2 ≫ map ψ f 2 =
        (openCohomologyIso U 2).hom ≫ unitsRestriction F E Ω 2 := by
    rw [resOfLE, openCohomologyIso_hom, unitsRestriction]
    refine (map_comp _ _ _ _ 2).symm.trans (Eq.trans ?_ (map_comp _ _ _ _ 2))
    exact map_congr _ _ (ContinuousMonoidHom.ext fun σ => Subtype.ext (AlgEquiv.ext fun x =>
      (krullRestriction_self_apply _ _ Ω σ x).symm)) (fun _ => Units.ext rfl) 2
  apply (ModuleCat.mono_iff_injective (map ψ f 2)).1 inferInstance
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, map_zero] using
    (congrArg (fun f => f.hom x) hcomp).trans hx

end Restriction

section Kummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

set_option maxHeartbeats 600000 in
/-- A closed subgroup that fixes every layer of the `ℓ`-power tower has zero
degree-two cohomology with coefficients in `μ_ℓ`. -/
private theorem subsingleton_cohomology_two_rootsOfUnity_of_le_layers {ℓ : ℕ} (hℓ : ℓ.Prime)
    {P : Subgroup Gal(Ω/K)} (hP : IsClosed (P : Set Gal(Ω/K)))
    (hfix : ∀ r : ℕ, P ≤ (cyclotomicLayer K Ω (ℓ ^ r)).fixingSubgroup) :
    Subsingleton (cohomology (Rep.res P.subtype (rootsOfUnityModule K Ω ℓ)) 2) := by
  let R := rootsOfUnityModule K Ω ℓ
  let B := unitsModule K Ω
  suffices hz : ∀ z : cohomology (Rep.res P.subtype R) 2, z = 0 from
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro z
  obtain ⟨W, hW, hPW, y, hy⟩ := exists_resOfLE_eq R hP 2 z
  let U : OpenSubgroup Gal(Ω/K) := ⟨W, hW⟩
  let F := fixedField (U : Subgroup Gal(Ω/K))
  let S := kummerSequenceRes (K := K) (Ksep := Ω) ℓ (U : Subgroup Gal(Ω/K))
  let x := (coeffMap S.f 2).hom y
  have hx : ℓ • x = 0 := by
    change ℓ • (coeffMap S.f 2).hom y = 0
    rw [← cohomologyMap_kummerSequenceRes_g_apply]
    exact cohomologyMap_g_cohomologyMap_f_apply (S := S) 2 y
  have : FiniteDimensional K F := finiteDimensional_fixedField_openSubgroup U
  let : NumberField F := NumberField.of_module_finite K F
  let xF := (openCohomologyIso U 2).hom.hom x
  have hxF : ℓ • xF = 0 := by
    change ℓ • (openCohomologyIso U 2).hom.hom x = 0
    rw [← map_nsmul, hx, map_zero]
  obtain ⟨r, E, hE, hEle, hsplit⟩ := exists_brauerRestriction_eq_zero_cyclotomic hℓ xF hxF
  let V := (E.restrictScalars K).fixingSubgroup
  have hVU : V ≤ (U : Subgroup Gal(Ω/K)) := fixingSubgroup_restrictScalars_le U E
  have hPV : P ≤ V := by
    refine (le_inf (show P ≤ F.fixingSubgroup from
      (show P ≤ (U : Subgroup Gal(Ω/K)) from hPW).trans
        (fixingSubgroup_fixedField_openSubgroup U).ge) (hfix r)).trans ?_
    rw [← fixingSubgroup_sup]
    apply IntermediateField.fixingSubgroup_antitone
    exact (show E.restrictScalars K ≤ (cyclotomicLayer F Ω (ℓ ^ r)).restrictScalars K
      from hEle).trans (le_of_eq (restrictScalars_adjoin_eq_sup K F _))
  have hzero : (resOfLE B hVU 2).hom x = 0 :=
    resOfLE_eq_zero_of_brauerRestriction_eq_zero U E x hsplit
  have : FiniteDimensional K (E.restrictScalars K) := FiniteDimensional.trans K F E
  let Vopen : OpenSubgroup Gal(Ω/K) :=
    ⟨V, (E.restrictScalars K).fixingSubgroup_isOpen⟩
  let S' := kummerSequenceRes (K := K) (Ksep := Ω) ℓ V
  have hS' : S'.ShortExact := kummerSequenceRes_shortExact ℓ V (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hinj := cohomologyMap_f_injective_of_subsingleton hS' 1
    (Local.subsingleton_cohomology_one_res_unitsModule K Ω Vopen)
  have hcomm :
      resOfLE R hVU 2 ≫ coeffMap S'.f 2 = coeffMap S.f 2 ≫ resOfLE B hVU 2 := by
    rw [resOfLE, resOfLE, coeffMap_eq, coeffMap_eq]
    refine (map_comp _ _ _ _ 2).symm.trans (Eq.trans ?_ (map_comp _ _ _ _ 2))
    exact map_congr _ _ (by ext; rfl) (fun _ => rfl) 2
  have hyV : (resOfLE R hVU 2).hom y = 0 := by
    apply (injective_iff_map_eq_zero _).1 hinj
    exact (congrArg (fun f => f.hom y) hcomm).trans hzero
  rw [← hy]
  have hcomp := congrArg (fun f => f.hom y) (resOfLE_comp R hVU hPV 2)
  rw [← hcomp, ModuleCat.comp_apply, hyV, map_zero]

end Kummer

section Dimension

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- A closed subgroup fixing the `ℓ`-power cyclotomic tower has `ℓ`-cohomological dimension
at most one. -/
private theorem cd_le_one_of_le_layers {ℓ : ℕ} (hℓ : ℓ.Prime)
    {H : Subgroup Gal(Ω/K)} (hH : IsClosed (H : Set Gal(Ω/K)))
    (hfix : ∀ r : ℕ, H ≤ (cyclotomicLayer K Ω (ℓ ^ r)).fixingSubgroup) :
    cd ℓ H ≤ 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH.isCompact
  obtain ⟨P, hP⟩ := exists_isProSylow (G := H) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cd_eq_of_isProSylow hℓ hP]
  change cd ℓ P ≤ ((1 : ℕ) : ℕ∞)
  rw [cd_le_iff_of_isProPGroup hℓ hP.2.1 1]
  let Q := P.map H.subtype
  have hQ : IsClosed (Q : Set Gal(Ω/K)) := (hP.1.isCompact.image continuous_subtype_val).isClosed
  have hQfix (r : ℕ) : Q ≤ (cyclotomicLayer K Ω (ℓ ^ r)).fixingSubgroup := by
    rintro _ ⟨σ, _, rfl⟩
    exact hfix r σ.2
  have hμ := subsingleton_cohomology_two_rootsOfUnity_of_le_layers hℓ hQ hQfix
  let e : P ≃* Q := P.equivMapOfInjective H.subtype Subtype.val_injective
  have he : Continuous e.toMonoidHom :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e.symm.toMonoidHom :=
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  obtain ⟨f⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ω hℓ (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  let eμ : Additive (rootsOfUnity ℓ Ω) ≃+ ULift.{u} (ZMod ℓ) :=
    f.symm.trans AddEquiv.ulift.symm
  let R := Rep.res Q.subtype (rootsOfUnityModule K Ω ℓ)
  let B := Rep.trivial (ULift.{u} ℤ) P (ULift.{u} (ZMod ℓ))
  let g : Rep.res e.toMonoidHom R ⟶ B :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm eμ.toAddMonoidHom, fun σ =>
      LinearMap.ext fun x => by
        change eμ (R.ρ (e σ) x) = eμ x
        apply congrArg eμ
        refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
        apply (mem_fixingSubgroup_iff _ _).1 (hQfix 1 (e σ).2)
        apply subset_adjoin
        let y : Additive (rootsOfUnity ℓ Ω) := x
        change ((y.toMul : Ωˣ) : Ω) ^ (ℓ ^ 1) = 1
        rw [pow_one]
        exact (mem_rootsOfUnity' ℓ _).1 y.toMul.2⟩
  have hg : Function.Bijective g.hom := eμ.bijective
  let ψ : P →ₜ* Q := ⟨e.toMonoidHom, he⟩
  have : IsIso (map ψ g 2) := isIso_map_of_mulEquiv e he he' g hg 2
  exact ((ModuleCat.epi_iff_surjective (map ψ g 2)).1 inferInstance).subsingleton

end Dimension

set_option maxHeartbeats 600000 in
/-- Finite `ℓ`-primary degree-two classes restrict to zero at a finite stage of the
`ℓ`-power cyclotomic tower. -/
theorem numberFieldFiniteModuleCyclotomicKilling :
    NumberFieldFiniteModuleCyclotomicKillingStatement.{u} := by
  intro K _ _ Ω _ _ _ A _ _ ℓ a hℓ hA β
  classical
  let L (r : ℕ) := (cyclotomicLayer K Ω (ℓ ^ r)).fixingSubgroup
  let H : Subgroup Gal(Ω/K) := ⨅ r : ℕ, L r
  have hclosed (r : ℕ) : IsClosed (L r : Set Gal(Ω/K)) := InfiniteGalois.fixingSubgroup_isClosed _
  have hcoe : (H : Set Gal(Ω/K)) = ⋂ r : ℕ, (L r : Set Gal(Ω/K)) := by
    ext σ
    simp [H]
  have hH : IsClosed (H : Set Gal(Ω/K)) := hcoe ▸ isClosed_iInter hclosed
  have hcd := cd_le_one_of_le_layers hℓ hH (fun r => iInf_le L r)
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH.isCompact
  have : Subsingleton (cohomology (Rep.res H.subtype A) 2) :=
    (cd_le_iff_forall_primary hℓ 1).1 hcd _ (fun x => ⟨a, hA x⟩) 2 (by decide)
  obtain ⟨U, hU, hHU, hβ⟩ := exists_res_eq_zero A hH 1 β (Subsingleton.elim _ _)
  have hdir : Directed (· ⊇ ·) (fun r => (L r : Set Gal(Ω/K))) := by
    intro i j
    exact ⟨max i j,
      IntermediateField.fixingSubgroup_antitone (cyclotomicLayer_mono (pow_dvd_pow ℓ (le_max_left i j))),
      IntermediateField.fixingSubgroup_antitone (cyclotomicLayer_mono (pow_dvd_pow ℓ (le_max_right i j)))⟩
  have hnhds : (U : Set Gal(Ω/K)) ∈ 𝓝ˢ (⋂ r : ℕ, (L r : Set Gal(Ω/K))) :=
    mem_nhdsSet_iff_exists.2 ⟨U, hU, hcoe ▸ hHU, fun _ hx => hx⟩
  obtain ⟨r, hr⟩ := exists_subset_nhds_of_isCompact' hdir (fun i => (hclosed i).isCompact) hclosed hnhds
  refine ⟨r, fun E ⟨ζ, hζ, hprim⟩ => ?_⟩
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  have hEL : cyclotomicLayer K Ω (ℓ ^ r) ≤ E := by
    apply adjoin_le_iff.2
    intro x hx
    obtain ⟨i, _, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx
    exact E.toSubalgebra.pow_mem hζ i
  have hEU : E.fixingSubgroup ≤ U := (IntermediateField.fixingSubgroup_antitone hEL).trans hr
  have hcomp : res A U 2 ≫ resOfLE A hEU 2 = res A E.fixingSubgroup 2 := by
    rw [res_eq A U, res_eq A E.fixingSubgroup, resOfLE]
    exact (map_comp _ _ _ _ 2).symm.trans (map_congr _ _ (by ext; rfl) (fun _ => rfl) 2)
  rw [← hcomp, ModuleCat.comp_apply, hβ, map_zero]

end

end Langlands.GaloisCohomology
