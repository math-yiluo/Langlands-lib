/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality

/-! # Encoding continuous internal modules as sectionwise module sheaves

Source: Stacks Project, Modules on Sites, and Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
/-- The section ring reconstructed from a ring sheaf is the original ring sheaf.
The identity on sections preserves multiplication by Sheaf.μ_comp_map_mul.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def reconstructedRingIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)) ≅ R := by
  let J := Scheme.ProEt.topology X
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  apply (fullyFaithfulSheafToPresheaf J RingCat.{u + 1}).preimageIso
  refine NatIso.ofComponents (fun Z ↦ ?_) (fun f ↦ ?_)
  · refine RingEquiv.toRingCatIso
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_mul' := ?_ }
    intro a b
    change (((sheafToPresheaf J Ab.{u + 1}).monObjObj A).mul.app Z).hom
      (a ⊗ₜ[ℤ] b) = (show R.obj.obj Z from a) * (show R.obj.obj Z from b)
    have hm := congrArg (fun m : MonObj A.obj ↦ m.mul) hmon
    rw [hm]
    rfl
  · ext a
    rfl

/-- The ring map on reconstructed section rings induced by an internal algebra map.
It is obtained by forgetting sheaves and evaluating the commutative monoid functor.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def sectionRingMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S := by
  let J := Scheme.ProEt.topology X
  let f : CommMon.mk R ⟶ CommMon.mk S := CommMon.homMk (Mon.ofHom φ)
  exact ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf J Ab.{u + 1}).mapCommMon.map f))
    InternalAbelianSheafModule.commMonToRing⟩

set_option backward.isDefEq.respectTransparency false in
/-- Encoding internal modules commutes with restriction of scalars.
The underlying isomorphism is identity; linearity is mapModComapIso.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def sectionModuleComapIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    Mod.comap φ ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R).functor ≅
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) S).functor ⋙
        SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sectionRingMap X φ)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      apply ConcreteCategory.hom_ext
      intro m
      have h := Mod.act_hom
        (((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapModComapIso φ).app M).hom
      exact (ConcreteCategory.congr_hom (congr_app h Z) (r ⊗ₜ[ℤ] m)).symm
    · intro Z W f
      ext
      rfl
  · intro M N f
    ext Z m
    rfl

/-- The regular internal module encodes as the unit sectionwise module.
The isomorphism is the identity on sections and their scalar actions.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def sectionModuleRegularIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj (Mod.regular R) ≅
      SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) R)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  · intro Z W f
    ext
    rfl

/-- The given metric on a finite extension is its spectral-norm metric.
This is NormedAlgebra.norm_eq_spectralNorm applied to differences.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
lemma spectralMetric_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [hE : NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    (spectralNorm.normedField ℚ_[ℓ] E).toMetricSpace = hE.toMetricSpace := by
  apply MetricSpace.ext
  apply Dist.ext
  funext a b
  rw [(spectralNorm.normedField ℚ_[ℓ] E).dist_eq, hE.dist_eq]
  exact (NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (-a + b)).symm

/-- The spectral and given-norm continuous field sheaves agree.
Their metrics agree, hence their topologies and continuous function rings agree.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
lemma lisseFieldSheaf_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [hE : NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    lisseFieldSheaf ℓ E X = latticeCoefficientSheaf X E := by
  have ht := congrArg
    (fun m : MetricSpace E ↦ m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (spectralMetric_eq ℓ E)
  unfold lisseFieldSheaf
  congr 1
  exact proof_irrel_heq _ _

/-- The two integral coefficient subrings agree.
Both membership conditions are exactly spectral norm at most one.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
lemma continuousIntegers_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    continuousIntegers ℓ E = Padic.coefficientExtensionIntegers ℓ E := by
  ext x
  rw [Padic.mem_coefficientExtensionIntegers]
  change ‖x‖₊ ≤ 1 ↔ spectralNorm ℚ_[ℓ] E x ≤ 1
  rw [← NNReal.coe_le_coe]
  change ‖x‖ ≤ 1 ↔ spectralNorm ℚ_[ℓ] E x ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ]]

/-- The spectral and given-norm integral coefficient sheaves agree.
Use equality of their subrings and of the induced subspace topologies.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
lemma lisseIntegerSheaf_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [hE : NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    lisseIntegerSheaf ℓ E X = latticeCoefficientSheaf X (continuousIntegers ℓ E) := by
  have ht := congrArg
    (fun m : MetricSpace E ↦ m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (spectralMetric_eq ℓ E)
  unfold lisseIntegerSheaf
  rw [continuousIntegers_eq ℓ E]
  congr 1
  · exact congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
      (Subtype.val (p := fun x ↦ x ∈ Padic.coefficientExtensionIntegers ℓ E)) t) ht
  · exact proof_irrel_heq _ _

/-- Transport module sheaves through an isomorphism of coefficient sheaves.
Use the identity-site pushforward equivalence and the two inverse ring maps.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def ringModuleEquivalenceOfIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S := by
  let eqv : X.ProEt ≌ X.ProEt :=
    ⟨𝟭 _, 𝟭 _, Iso.refl _, Iso.refl _, fun _ ↦ Category.id_comp _⟩
  letI : eqv.functor.IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  letI : eqv.inverse.IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  exact SheafOfModules.pushforwardPushforwardEquivalence eqv e.hom e.inv
    (by ext V : 2
        exact (R.obj.map_id V).trans
          (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) e.inv_hom_id) V).symm)
    (by ext V : 2
        exact (congrArg (fun f ↦ e.hom.hom.app V ≫ e.inv.hom.app V ≫ f)
          (S.obj.map_id V)).trans ((Category.comp_id _).trans
            (congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) e.hom_inv_id) V)))

/-- Coefficient transport identifies the unit module sheaves.
On each object this is restrictScalarsIsoOfEquiv for the given ring isomorphism.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def ringModuleUnitIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R) :
    (ringModuleEquivalenceOfIso X e).functor.obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let eV := ((sheafToPresheaf (Scheme.ProEt.topology X) RingCat).mapIso e).app V
    exact ModuleCat.restrictScalarsIsoOfEquiv eV.ringCatIsoToRingEquiv
  · intro V W f
    ext s
    change e.inv.hom.app W (R.obj.map f s) = S.obj.map f (e.inv.hom.app V s)
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) s

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A coefficient isomorphism preserves the finite free sectionwise modules.
Source: Stacks Project, Modules on Sites, Tag 03DO.
(auxiliary; not a blueprint node) -/
noncomputable def ringModuleFreeIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R)
    (n : ℕ) :
    (ringModuleEquivalenceOfIso X e).functor.obj
        (SheafOfModules.free (R := R) (ULift.{u + 1} (Fin n))) ≅
      SheafOfModules.free (R := S) (ULift.{u + 1} (Fin n)) := by
  let F := (ringModuleEquivalenceOfIso X e).functor
  exact (SheafOfModules.mapFreeIso F _ (ringModuleUnitIso X e).symm).symm

/-- The explicit encoding of continuous internal modules as module sheaves.
Restrict along the inverse chartComparison, encode the sectionwise action, then
transport along reconstructedRingIso. Each step is an actual equivalence.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousRingModuleEquivalence (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T) X) ≌
      SheafOfModules.{u + 1} (continuousMapRingSheaf X T) := by
  let J := Scheme.ProEt.topology X
  let R := continuousMapRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ by
      exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let φ := chartComparison X T
  exact (Mod.comapEquivalenceOfIsIso (inv φ)).trans
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A).trans
      (ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm))
/-- The continuous module encoding identifies the regular module with the unit.
Compose regularIsoOfIsIso, sectionModuleRegularIso and ringModuleUnitIso.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousRingRegularIso (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    (continuousRingModuleEquivalence X T).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) X)) ≅
      SheafOfModules.unit (continuousMapRingSheaf X T) := by
  let J := Scheme.ProEt.topology X
  let R := continuousMapRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let F := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J A
  let G := ringModuleEquivalenceOfIso X (reconstructedRingIso X R).symm
  exact G.functor.mapIso (F.functor.mapIso
    (Mod.regularIsoOfIsIso (chartComparison X T)) ≪≫ sectionModuleRegularIso X A) ≪≫
      ringModuleUnitIso X (reconstructedRingIso X R).symm

/-- The continuous module encoding identifies finite biproducts with finite free sheaves.
Map the biproduct through the equivalence, use continuousRingRegularIso and
reindex the corresponding coproduct along Equiv.ulift.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousRingFreeIso (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (n : ℕ) :
    (continuousRingModuleEquivalence X T).functor.obj
        (⨁ fun _ : Fin n ↦ Mod.regular
          (condensedRingObj (Profinite.continuousMapRingObj T) X)) ≅
      SheafOfModules.free (R := continuousMapRingSheaf X T) (ULift.{u + 1} (Fin n)) := by
  let F := (continuousRingModuleEquivalence X T).functor
  letI : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) F :=
    preservesBiproduct_of_preservesCoproduct F
  exact F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ continuousRingRegularIso X T) ≪≫
    biproduct.isoCoproduct _ ≪≫
      (Sigma.reindex Equiv.ulift (fun _ : Fin n ↦
        SheafOfModules.unit (continuousMapRingSheaf X T))).symm

/-- The explicit encoding for rational coefficients in the lattice theorem.
Compose continuousRingModuleEquivalence with the spectral coefficient equality.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousFieldModuleEquivalence (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X) ≌
      ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf ℓ E X)) := by
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  letI : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  exact (continuousRingModuleEquivalence X E).trans (ringModuleEquivalenceOfIso X
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (eqToIso (lisseFieldSheaf_eq ℓ E X))))

/-- The explicit encoding for integral coefficients in the lattice theorem.
Compose continuousRingModuleEquivalence with the integral coefficient equality.
Source: Stacks Project, Modules on Sites, sheaves of modules (Tag 00YV);
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def continuousIntegerModuleEquivalence (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X) ≌
      ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf ℓ E X)) := by
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  letI : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  exact (continuousRingModuleEquivalence X (continuousIntegers ℓ E)).trans
    (ringModuleEquivalenceOfIso X ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (eqToIso (lisseIntegerSheaf_eq ℓ E X))))

set_option backward.isDefEq.respectTransparency false in
/-- The explicit continuous module encoding commutes with restriction of scalars.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 00YV;
Bhatt--Scholze Section 6.8.
(auxiliary; not a blueprint node)

Proof. Coefficient naturality conjugates the condensed scalar map by the two
canonical chart comparisons to the sectionwise scalar map. Apply comapComp and
sectionModuleComapIso. The reconstructed-ring comparisons are identity on sections,
so their restrictions commute by an identity linear map. Compose the resulting
isomorphisms. This proves a property of the already constructed encodings. -/
theorem continuousRing_comap_compatibility (X : Scheme.{u}) (T S : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [TotallyDisconnectedSpace S]
    (φ : T →+* S) (hφ : Continuous φ) :
    Nonempty (Mod.comap ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ))) ⋙
      (continuousRingModuleEquivalence X T).functor ≅
    (continuousRingModuleEquivalence X S).functor ⋙
      SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ)) := by
  refine ⟨?_⟩
  let J := Scheme.ProEt.topology X
  let RT := continuousMapRingSheaf X T
  let RS := continuousMapRingSheaf X S
  let AT := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RT
  let AS := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj RS
  letI : IsCommMonObj AT := Sheaf.isCommMonObj_sheafCompose_obj J RT
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  letI : IsCommMonObj AS := Sheaf.isCommMonObj_sheafCompose_obj J RS
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, S)) inferInstance a b)
  let α := (upperStarFromPoint X).map
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ))
  let β := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X φ hφ)
  have hc : inv (chartComparison X T) ≫ α = β ≫ inv (chartComparison X S) := by
    apply (cancel_epi (chartComparison X T)).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← chartComparison_naturality X T S φ hφ]
    simp
    rfl
  let e₀ : Mod.comap α ⋙ Mod.comap (inv (chartComparison X T)) ≅
      Mod.comap (inv (chartComparison X S)) ⋙ Mod.comap β :=
    (Mod.comapComp _ _).symm ≪≫ Mod.comapCongr hc ≪≫ Mod.comapComp _ _
  let FT := (InternalAbelianSheafModule.sectionModuleEquivalence J AT).functor
  let FS := (InternalAbelianSheafModule.sectionModuleEquivalence J AS).functor
  let GT := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RT).symm).functor
  let GS := (ringModuleEquivalenceOfIso X (reconstructedRingIso X RS).symm).functor
  let e₁ := sectionModuleComapIso X β
  let e₂ : SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (sectionRingMap X β)) ⋙ GT ≅
      GS ⋙ SheafOfModules.restrictScalars (continuousMapRingSheafMap X φ hφ) := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
      · refine ModuleCat.isoMk (Iso.refl _) ?_
        intro r
        ext m
        rfl
      · intro Z W f
        ext
        rfl
    · intro M N f
      ext Z m
      rfl
  refine NatIso.ofComponents (fun M ↦
    (FT ⋙ GT).mapIso (e₀.app M) ≪≫
      GT.mapIso (e₁.app ((Mod.comap (inv (chartComparison X S))).obj M)) ≪≫
      e₂.app (FS.obj ((Mod.comap (inv (chartComparison X S))).obj M))) ?_
  intro M N f
  ext Z m
  rfl

private lemma cast_square {C : Type*} [Category C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst hA
  subst hB
  cases h
  simp
set_option backward.isDefEq.respectTransparency false in
/-- The integral-to-field scalar map commutes with the spectral coefficient identifications.
Source: Bhatt--Scholze Section 6.8, with NormedAlgebra.norm_eq_spectralNorm.
(auxiliary; not a blueprint node)

Proof. The given and spectral metrics agree, and the two integral subrings agree.
The inclusions of either subring into the field are the same subtype inclusion.
Postcomposition on continuous functions therefore gives heterogeneously equal maps.
Transport through the coefficient equalities to obtain the stated commuting square. -/
lemma lisseScalar_square (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    (lisseIntegerToField ℓ E X) ≫ eqToHom (lisseFieldSheaf_eq ℓ E X) =
      eqToHom (lisseIntegerSheaf_eq ℓ E X) ≫
        (show latticeCoefficientSheaf X (continuousIntegers ℓ E) ⟶
          latticeCoefficientSheaf X E from
          ⟨{ app := fun U ↦ CommRingCat.ofHom
                ((continuousMapRingPresheafMap X (continuousIntegers ℓ E).subtype
                  continuous_subtype_val).app U).hom
             naturality := fun _ _ _ ↦ rfl }⟩) := by
  have ht := congrArg
    (fun m : MetricSpace E ↦ m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (spectralMetric_eq ℓ E)
  have hi := continuousIntegers_eq ℓ E
  apply cast_square (lisseIntegerSheaf_eq ℓ E X) (lisseFieldSheaf_eq ℓ E X)
  unfold lisseIntegerToField
  congr! 12
  all_goals first
    | exact lisseIntegerSheaf_eq ℓ E X
    | exact lisseFieldSheaf_eq ℓ E X
    | (rename_i U V hUV
       cases hUV
       dsimp only [continuousMapRingPresheafMap]
       congr! 16
       all_goals first
         | exact hi.symm
)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] condensedPushforwardHom

/-- The canonical continuous chart commutes with weakly etale inverse image.
Source: Bhatt--Scholze Section 6.8; the adjoint form of
continuousChart_scheme_naturality. Transpose by the inverse-image adjunction.
The localization comparison transposes to its unit; on sections this is exactly
precomposition with the pullback projection. Apply scheme naturality.
(auxiliary; not a blueprint node) -/
lemma continuousChart_pullback (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] :
    (upperStar Ab.{u + 1} f).map (chartComparison X E) ≫
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).hom.app
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X E)) =
      condensedPullbackHom (Profinite.continuousMapRingObj E) f ≫ chartComparison Y E := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  apply (adj.homEquiv _ _).injective
  have hl := adj.homEquiv_naturality_left (chartComparison X E)
    ((upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).hom.app
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X E)))
  erw [hl]
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app adj
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f inferInstance)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X E))
  erw [hu]
  erw [adj.homEquiv_naturality_right]
  change chartComparison X E ≫ _ =
    (adj.unit.app _ ≫ (lowerStar Ab.{u + 1} f).map
      (condensedPullbackHom (Profinite.continuousMapRingObj E) f)) ≫
        (lowerStar Ab.{u + 1} f).map (chartComparison Y E)
  rw [← Adjunction.unitAlgHom, unitAlgHom_comp_map_condensedPullbackHom]
  rw [CondensedRing.continuousChart_scheme_naturality]
  congr 1
  ext U : 3
  apply ConcreteCategory.hom_ext
  intro s
  erw [CondensedRing.continuousFunctionPushforward_app f E U.unop s]
  rfl

end AlgebraicGeometry.ProEtale
