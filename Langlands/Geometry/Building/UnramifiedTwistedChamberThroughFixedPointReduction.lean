import Langlands.Geometry.Building.UnramifiedTwistedGeneratorChamberStatement
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointStatement
import Langlands.Geometry.Building.UnramifiedTwistedBuildingAction
import Langlands.Geometry.Building.KPApartmentGaloisTransport
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof

/-! # Reduction of twisted-stable chambers to one topological generator -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The single-generator chamber statement implies the chamber statement for all of
`Aut(K/F)`. -/
def UnramifiedTwistedChamberThroughFixedPointReductionStatement : Prop :=
  UnramifiedTwistedGeneratorChamberStatement.{u} →
    UnramifiedTwistedChamberThroughFixedPointStatement.{u}

namespace TwistedGeneratorReduction

section General

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Finitely many rational points of a scalar extension of a group of finite type are fixed by
the fixing subgroup of a finite intermediate field. -/
theorem exists_finite_fixing_rationalPoints [Algebra.IsAlgebraic k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {J : Type u} [Finite J]
    (g : J → rationalPoints (baseChanged k K G)) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ i, rationalConjugate k K G σ (g i) = g i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨E, hE, hfix⟩ := IdentityComponent.exists_finite_fixing_algHoms k K
    (fun i => GaloisPoint.coordinates k G K (baseChangeCoeffEquiv k K G (g i)))
  refine ⟨E, hE, fun σ hσ i => ?_⟩
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate]
  apply (GaloisPoint.coordinates k G K).injective
  ext a
  rw [GaloisPoint.coordinates_conjugate]
  exact DFunLike.congr_fun (hfix σ hσ i) a

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

omit [IsAffineHom G.X.hom] in
/-- Points of a scalar extension of a monomorphism are detected after pushforward. -/
theorem map_injective [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left] :
    Function.Injective
      (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) := by
  have : Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom :=
    Over.mono_of_mono_left _
  intro x y hxy
  exact (cancel_mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom).mp hxy

omit [IsAffineHom G.X.hom] in
/-- A torus point whose pushforward is fixed is fixed. -/
theorem rationalConjugate_eq_of_map
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
    (σ : K ≃ₐ[k] K) (s : rationalPoints (baseChanged k K T.toGrp))
    (hs : rationalConjugate k K G σ
        (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map i) s) =
      rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map i) s) :
    rationalConjugate k K T.toGrp σ s = s := by
  apply map_injective k K i
  rw [← rationalConjugate_map]
  exact hs

omit [IsAffineHom G.X.hom] in
/-- If `σ` fixes the cocharacter point `ν(b)` with `b` a fixed non-torsion unit, then `σ χ - χ`
pairs trivially with `ν`. -/
theorem latticePairing_galois_sub_eq_zero (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (b : Kˣ) (hbfix : Units.map σ.toMonoidHom b = b) (hb : ∀ n : ℤ, b ^ n = 1 → n = 0)
    (hq : rationalConjugate k K T.toGrp σ (CocharacterUniformizer.cocharacterPoints K
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ν b) =
      CocharacterUniformizer.cocharacterPoints K
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ν b) :
    latticePairing _ (characterLattice.galoisRepresentation k K T σ χ - χ) ν = 0 := by
  have h := rationalCharacterEval_galois k K T σ χ (CocharacterUniformizer.cocharacterPoints K
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ν b)
  rw [hq, CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    CocharacterUniformizer.rationalCharacterEval_cocharacterPoints, map_zpow, hbfix] at h
  rw [map_sub, LinearMap.sub_apply]
  apply hb
  rw [zpow_sub, h, mul_inv_cancel]

/-- **The Galois action on characters is locally constant.** Let `T → G` be a homomorphism
over `k` to a group of finite type, with monomorphic scalar extension, and suppose that `T_K`
is split. If `b ∈ Kˣ` is fixed by every coefficient automorphism and is not a root of unity,
then the fixing subgroup of some finite intermediate field acts trivially on `X^*(T_K)`. -/
theorem exists_finite_fixing_characters [Algebra.IsAlgebraic k K] [LocallyOfFiniteType G.X.hom]
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (b : Kˣ) (hbfix : ∀ σ : K ≃ₐ[k] K, Units.map σ.toMonoidHom b = b)
    (hb : ∀ n : ℤ, b ^ n = 1 → n = 0) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup,
        ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T),
          characterLattice.galoisRepresentation k K T σ χ = χ := by
  classical
  obtain ⟨s, hs⟩ := hT.finite_cocharacterLattice.fg_top
  obtain ⟨E, hE, hfix⟩ := exists_finite_fixing_rationalPoints k K (G := G)
    (fun ν : s => rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (CocharacterUniformizer.cocharacterPoints K
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ν.1 b))
  refine ⟨E, hE, fun σ hσ χ => ?_⟩
  have hzero : latticePairing _ (characterLattice.galoisRepresentation k K T σ χ - χ) = 0 :=
    LinearMap.ext_on hs (fun ν hν => by
      rw [latticePairing_galois_sub_eq_zero k K σ χ ν b (hbfix σ) hb
        (rationalConjugate_eq_of_map k K i σ _ (hfix σ hσ ⟨ν, hν⟩)), LinearMap.zero_apply])
  rw [← sub_eq_zero]
  apply hT.isPerfPair_latticePairing.separatingLeft
  intro ν
  rw [hzero, LinearMap.zero_apply]

/-- If the inverse of `σ` fixes every relative root, then `σ` acts trivially on the reduced
translation space. -/
theorem galoisTranslationAction_eq_self (σ : K ≃ₐ[k] K)
    (hσ : ∀ χ ∈ relativeRoots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i),
      characterLattice.galoisRepresentation k K T σ⁻¹ χ = χ)
    (v : TranslationSpace (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) :
    galoisTranslationAction k K i σ v = v := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  rw [galoisTranslationAction_mk, Submodule.Quotient.eq, mem_rootAnnihilator]
  intro a ha
  rw [map_sub, eval_galoisCocharacterAction_right, hσ a ha, sub_self]

/-- A coefficient automorphism with trivial translation part and a fixed point acts trivially
on a stable apartment. -/
theorem galoisAction_eq_self
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left] {ω : Kˣ → ℝ}
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)
    (hD : KPApartmentData.GaloisStable k K i D) (σ : K ≃ₐ[k] K) (x₁ : D.Apartment)
    (hx₁ : KPApartmentData.galoisAction k K i D hD σ x₁ = x₁)
    (ht : ∀ v, galoisTranslationAction k K i σ v = v) (z : D.Apartment) :
    KPApartmentData.galoisAction k K i D hD σ z = z := by
  rw [← vsub_vadd z x₁, KPApartmentData.galoisAction_vadd, ht, hx₁]

end General

section Stabilizer

variable {Γ X : Type*} [Group Γ]

/-- The elements of `Γ` whose permutations map `Y` onto itself. -/
def setStabilizer (τ : Γ →* Equiv.Perm X) (Y : Set X) : Subgroup Γ where
  carrier := {σ | ⇑(τ σ) '' Y = Y}
  one_mem' := by
    change ⇑(τ 1) '' Y = Y
    rw [map_one, Equiv.Perm.coe_one, Set.image_id]
  mul_mem' {a b} ha hb := by
    change ⇑(τ a) '' Y = Y at ha
    change ⇑(τ b) '' Y = Y at hb
    change ⇑(τ (a * b)) '' Y = Y
    rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp, hb, ha]
  inv_mem' {a} ha := by
    change ⇑(τ a) '' Y = Y at ha
    change ⇑(τ a⁻¹) '' Y = Y
    conv_lhs => rw [← ha]
    rw [map_inv, Equiv.Perm.inv_def, Equiv.symm_image_image]

theorem mem_setStabilizer (τ : Γ →* Equiv.Perm X) (Y : Set X) (σ : Γ) :
    σ ∈ setStabilizer τ Y ↔ ⇑(τ σ) '' Y = Y := Iff.rfl

end Stabilizer

section Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance extendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))

/-- The twisted action of an automorphism fixing the cocycle value, the translating element
and the apartment point fixes the translated point. -/
theorem twisted_smul_apartmentMap (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (w : B.Apartment)
    (hcσ : c σ = 1) (hgσ : rationalConjugate F (inertiaFixedField F) G σ g = g)
    (hw : A.apartment σ w = w) :
    c σ • A.action σ (g • B.apartmentMap w) = g • B.apartmentMap w := by
  rw [MaximalUnramified.SemilinearApartmentData.action_smul,
    MaximalUnramified.SemilinearApartmentData.action_apartmentMap, hcσ, one_smul, hgσ, hw]

variable (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))

include hc in
/-- **Density step.** If a set is stable under the twisted action of `φ` and fixed pointwise by
the twisted action of the fixing subgroup of `E`, and the powers of `φ` meet every coset of that
subgroup, then the set is stable under the twisted action of every automorphism. -/
theorem twisted_image_eq_of_generator (E : IntermediateField F (inertiaFixedField F))
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hgen : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∃ n : ℤ, σ⁻¹ * φ ^ n ∈ E.fixingSubgroup)
    (Y : Set B.ReducedBuilding) (hYφ : (fun z => c φ • A.action φ z) '' Y = Y)
    (hfix : ∀ σ ∈ E.fixingSubgroup, ∀ z ∈ Y, c σ • A.action σ z = z)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (fun z => c σ • A.action σ z) '' Y = Y := by
  let τ := A.twistedAction c hc
  have hτ : ∀ ρ, ⇑(τ ρ) = fun z => c ρ • A.action ρ z := fun ρ =>
    funext fun z => MaximalUnramified.SemilinearApartmentData.twistedAction_apply A c hc ρ z
  let H := setStabilizer τ Y
  have hφ : φ ∈ H := by
    rw [mem_setStabilizer, hτ]
    exact hYφ
  have hE : ∀ ρ ∈ E.fixingSubgroup, ρ ∈ H := by
    intro ρ hρ
    rw [mem_setStabilizer, hτ, Set.image_congr (hfix ρ hρ), Set.image_id']
  obtain ⟨n, hn⟩ := hgen σ
  have hσ : σ = φ ^ n * (σ⁻¹ * φ ^ n)⁻¹ := by group
  have hmem : σ ∈ H := by
    rw [hσ]
    exact H.mul_mem (H.zpow_mem hφ n) (H.inv_mem (hE _ hn))
  rw [← hτ]
  exact hmem

include hc in
/-- **Density step for a translated subset of the apartment.** If `Y = g · S` with `S` a subset
of the apartment, `Y` is stable under the twisted action of `φ`, and the fixing subgroup of `E`
fixes `c`, `g` and the apartment pointwise, then `Y` is stable under every twisted action. -/
theorem twisted_image_eq_of_presentation (E : IntermediateField F (inertiaFixedField F))
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hgen : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∃ n : ℤ, σ⁻¹ * φ ^ n ∈ E.fixingSubgroup)
    (Y : Set B.ReducedBuilding) (hYφ : (fun z => c φ • A.action φ z) '' Y = Y)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (S : Set B.Apartment)
    (hYeq : Y = (fun z => g • B.apartmentMap z) '' S)
    (hcE : ∀ σ ∈ E.fixingSubgroup, c σ = 1)
    (hgE : ∀ σ ∈ E.fixingSubgroup, rationalConjugate F (inertiaFixedField F) G σ g = g)
    (hAE : ∀ σ ∈ E.fixingSubgroup, ∀ w, A.apartment σ w = w)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (fun z => c σ • A.action σ z) '' Y = Y := by
  refine twisted_image_eq_of_generator A c hc E φ hgen Y hYφ ?_ σ
  intro ρ hρ z hz
  rw [hYeq] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact twisted_smul_apartmentMap A c ρ g w (hcE ρ hρ) (hgE ρ hρ) (hAE ρ hρ w)

/-- A translate of the facet of a point on no affine root hyperplane is a chamber. -/
theorem isChamber_of_presentation
    {G' : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G'.X.hom]
    (B' : MaximalUnramified.BuildingData F G') (g : rationalPoints G') (x₀ : B'.Apartment)
    (hx₀ : ∀ ψ ∈ B'.affineRoots, ψ x₀ ≠ 0) (Y : Set B'.ReducedBuilding)
    (hYeq : Y = (fun z => g • B'.apartmentMap z) '' AffineRootSystem.facet B'.affineRoots x₀) :
    B'.IsChamber Y :=
  ⟨g, _, ⟨x₀, hx₀, rfl⟩, hYeq⟩

/-- The mapped base uniformizer is fixed by every automorphism of `K/F`. -/
theorem baseUniformizerUnit_fixed (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    Units.map σ.toMonoidHom (MaximalUnramified.baseUniformizerUnit F) =
      MaximalUnramified.baseUniformizerUnit F := by
  apply Units.ext
  exact σ.commutes _

/-- The mapped base uniformizer is not a root of unity. -/
theorem baseUniformizerUnit_zpow_eq_one (n : ℤ)
    (hn : MaximalUnramified.baseUniformizerUnit F ^ n = 1) : n = 0 := by
  have h := congrArg (fun t => (IntegerValuation.orderUnits (MaximalUnramified.valuation F)
    t).toAdd) hn
  simp only [map_zpow, toAdd_zpow, MaximalUnramified.orderUnits_baseUniformizerUnit,
    map_one, toAdd_one, smul_eq_mul, mul_one] at h
  exact h

end Building

end TwistedGeneratorReduction

namespace TwistedGeneratorReduction

section Descent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)

/-- An automorphism whose inverse fixes every character, in the presence of a point of the
apartment fixed by it, acts trivially on the apartment of `semilinearData`. -/
theorem semilinearData_apartment_eq_self (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hσ : ∀ χ : characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T),
      characterLattice.galoisRepresentation F (inertiaFixedField F) T σ⁻¹ χ = χ)
    (x₁ : D.Apartment)
    (hx₁ : RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x₁.val = x₁.val)
    (w : D.Apartment) :
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ w = w :=
  galoisAction_eq_self F (inertiaFixedField F) iT D hD σ x₁
    (KPApartmentData.Apartment.ext hx₁)
    (galoisTranslationAction_eq_self F (inertiaFixedField F) iT σ (fun χ _ => hσ χ)) w

set_option maxHeartbeats 1600000 in
/-- **Core of the reduction.** If `Y = g · S` with `S` a subset of the apartment and `Y` is
stable under the twisted action of a dense `φ`, then `Y` is stable under the twisted action of
every automorphism of `K/F`, provided the apartment has a point fixed by every automorphism. -/
theorem twisted_image_eq_of_generator_data [LocallyOfFiniteType G.X.hom]
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (hcE : ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1)
    (hfixed : ∃ x : D.Apartment, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hφgen : ∀ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E →
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        ∃ n : ℤ, σ⁻¹ * φ ^ n ∈ E.fixingSubgroup)
    (Y : Set (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).ReducedBuilding)
    (hYφ : (fun z => c φ •
      (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).action φ z) '' Y = Y)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (S : Set (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).Apartment)
    (hYeq : Y = (fun z => g •
      (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).apartmentMap z) '' S)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    (fun z => c σ •
      (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).action σ z) '' Y = Y := by
  obtain ⟨Ec, hEc, hcfix⟩ := hcE
  obtain ⟨Eχ, hEχ, hχ⟩ := exists_finite_fixing_characters F (inertiaFixedField F) iT
    hiT.isSplitSubtorus.1 (MaximalUnramified.baseUniformizerUnit F)
    baseUniformizerUnit_fixed baseUniformizerUnit_zpow_eq_one
  obtain ⟨Eg, hEg, hgfix⟩ := exists_finite_fixing_rationalPoints F (inertiaFixedField F)
    (G := G) (fun _ : PUnit.{u + 1} => g)
  obtain ⟨x₁, hx₁⟩ := hfixed
  have hE : FiniteDimensional F (Ec ⊔ Eχ ⊔ Eg : IntermediateField F (inertiaFixedField F)) :=
    IntermediateField.finiteDimensional_sup _ _
  exact twisted_image_eq_of_presentation
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD) c hc (Ec ⊔ Eχ ⊔ Eg) φ
    (hφgen _ hE) Y hYφ g S hYeq
    (fun ρ hρ => hcfix ρ
      (IntermediateField.fixingSubgroup_le (le_sup_left.trans le_sup_left) hρ))
    (fun ρ hρ => hgfix ρ (IntermediateField.fixingSubgroup_le le_sup_right hρ) PUnit.unit)
    (fun ρ hρ => semilinearData_apartment_eq_self iT hGK hiT C h6 hD ρ
      (hχ ρ⁻¹ (Eχ.fixingSubgroup.inv_mem
        (IntermediateField.fixingSubgroup_le (le_sup_right.trans le_sup_left) hρ)))
      x₁ (hx₁ ρ)) σ

end Descent

end TwistedGeneratorReduction

open TwistedGeneratorReduction in
set_option maxHeartbeats 1600000 in
/-- **Reduction to one topological generator.** A chamber through the twisted-fixed point that
is stable under the twisted action of a dense generator `φ` is stable under the twisted action
of all of `Aut(K/F)`: the fixing subgroup of a suitable finite subextension fixes it pointwise. -/
theorem unramifiedTwistedChamberThroughFixedPoint_of_generator :
    UnramifiedTwistedChamberThroughFixedPointReductionStatement.{u} := by
  intro hR F _ _ _ _ G hG T iT
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let _ := mono_of_isMaximalSplitTorus hiT
  let _ : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hcE y hy
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨φ, hφgen, Y, hYφ, g, x₀, x, hx₀, hYeq, hxcl, hgx⟩ :=
    hR F G hG T iT hiT D C h6 hD c hc hcE y hy
  exact ⟨Y, isChamber_of_presentation _ g x₀ hx₀ Y hYeq,
    twisted_image_eq_of_generator_data iT _ hiT C h6 hD c hc hcE
      (unramifiedGaloisFixedApartment F G hG T iT hiT D hD) φ hφgen Y hYφ g _ hYeq,
    g, x₀, x, hx₀, hYeq, hxcl, hgx⟩

/-- The conditional reduction holds at arbitrary universe. -/
theorem unramifiedTwistedChamberThroughFixedPointReduction :
    UnramifiedTwistedChamberThroughFixedPointReductionStatement.{u} :=
  unramifiedTwistedChamberThroughFixedPoint_of_generator

end Langlands.Geometry.Building
