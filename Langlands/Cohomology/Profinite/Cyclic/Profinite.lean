import Langlands.Cohomology.Profinite.Cup.Connecting
import Langlands.Cohomology.Profinite.Cyclic.Cup
import Langlands.Cohomology.Profinite.LowDegree

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory GroupCoh

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] {p q n : ℕ}

noncomputable def cupRightProf (h : p + q = n) (b : cohomology B q) :
    cohomology A p ⟶ cohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cup h).flip b)

theorem cupRightProf_apply (h : p + q = n) (b : cohomology B q) (a : cohomology A p) :
    (cupRightProf h b).hom a = cup h a b :=
  rfl

end Generic

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

noncomputable def charClassProf (χ : Additive G →ₜ+ QZ) : cohomology (Rep.trivial ℤ G ℤ) 2 :=
  (δ (ratSES_shortExact G) 1 2 rfl).hom ((cohomologyOneRatModIntIso G).inv.hom χ)

noncomputable def cupCharClassProf (A : Rep ℤ G) [IsSmoothRep A] (χ : Additive G →ₜ+ QZ) :=
  (zeroIso A).inv ≫ cupRightProf (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2) (charClassProf χ) ≫
    coeffMap (A := A ⊗ Rep.trivial ℤ G ℤ) (B := A) (ρ_ A).hom 2

theorem cupCharClassProf_zero (A : Rep ℤ G) [IsSmoothRep A] (a : A.ρ.invariants) :
    (cupCharClassProf A 0).hom a = 0 := by
  have h0 : charClassProf (0 : Additive G →ₜ+ QZ) = 0 := by
    unfold charClassProf
    rw [map_zero]
    exact map_zero _
  rw [cupCharClassProf, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, cupRightProf_apply, h0, map_zero, map_zero]

end Profinite

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory GroupCoh

universe u

def charAdd {G : Type u} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    Additive G →+ AddCircle (1 : ℚ) :=
  QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom

section Profinite

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem charAdd_apply (χ : Additive G →ₜ+ QZ) (x : Additive G) :
    charAdd χ x = QZ.toAddCircle (χ x) :=
  rfl

omit [IsTopologicalGroup G] in
theorem isLocallyConstant_charAdd (χ : Additive G →ₜ+ QZ) :
    IsLocallyConstant fun g : G => charAdd χ (Additive.ofMul g) := by
  have hc : Continuous fun g : G => χ (Additive.ofMul g) :=
    χ.continuous_toFun.comp continuous_ofMul
  have h := IsLocallyConstant.comp_continuous
    (IsLocallyConstant.of_discrete (X := QZ) (fun x : QZ => QZ.toAddCircle x)) hc
  exact h

theorem exists_cocycle_zeroIso_inv {k : Type u} [CommRing k] (A : Rep k G) [IsSmoothRep A]
    (a : A.ρ.invariants) :
    ∃ z : cocycles A 0, cohomologyπ A 0 z = (zeroIso A).inv.hom a ∧
      cochainOf A (cocycleι A 0 z) = fun _ => (a : A) := by
  refine ⟨(cocyclesIso₀ A).inv.hom a, rfl, ?_⟩
  have hf : (cocyclesIso₀ A).hom ≫ ModuleCat.ofHom (invariantsToCochains₀ A) =
      (cochains A).iCycles 0 := by
    dsimp only [cocyclesIso₀, Limits.KernelFork.mapIsoOfIsLimit]
    exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)
  have e := ConcreteCategory.congr_hom hf ((cocyclesIso₀ A).inv a)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at e
  exact (congrArg (cochainOf A) e).symm

end Profinite

section ProfiniteInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Cocycles


theorem exists_cocycle_charH1 (χ : Additive G →ₜ+ QZ) :
    ∃ z : cocycles (Rep.trivial ℤ G (AddCircle (1 : ℚ))) 1,
      cohomologyπ _ 1 z = (cohomologyOneRatModIntIso G).inv.hom χ ∧
      ∀ v : Fin 1 → G, cochainOf _ (cocycleι _ 1 z) v = charAdd χ (Additive.ofMul (v 0)) := by
  obtain ⟨z, hz⟩ := cohomologyπ_surjective _ 1 ((cohomologyOneRatModIntIso G).inv.hom χ)
  refine ⟨z, hz, fun v => ?_⟩
  have h1 : (cohomologyOneRatModIntIso G).hom.hom (cohomologyπ _ 1 z) = χ := by
    rw [hz]
    exact congrArg (fun f => f.hom χ) (cohomologyOneRatModIntIso G).inv_hom_id
  simp only [cohomologyOneRatModIntIso, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
    at h1
  change (locallyConstantHomQZEquiv G) ((cohomologyOneIsoOfIsTrivial G (AddCircle (1 : ℚ))).hom.hom
    (cohomologyπ _ 1 z)) = χ at h1
  have h4 := DFunLike.congr_fun h1 (Additive.ofMul (v 0))
  rw [locallyConstantHomQZEquiv_apply] at h4
  have h2 := cohomologyOneIsoOfIsTrivial_hom_cohomologyπ G (AddCircle (1 : ℚ)) z (v 0)
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have h5 := congrArg QZ.toAddCircle h4
  rw [AddEquiv.apply_symm_apply] at h5
  rw [charAdd_apply, ← h5]
  conv_lhs => rw [hv]
  exact h2.symm

theorem exists_cocycle_charClassProf (χ : Additive G →ₜ+ QZ) :
    ∃ x : cocycles (Rep.trivial ℤ G ℤ) 2, cohomologyπ _ 2 x = charClassProf χ ∧
      ∀ v : Fin 2 → G, cochainOf _ (cocycleι _ 2 x) v = charCocycle (charAdd χ) (v 0, v 1) := by
  obtain ⟨z, hz, hzv⟩ := exists_cocycle_charH1 χ
  let y : (Fin 1 → G) → ℚ := fun v => reprIco (charAdd χ (Additive.ofMul (v 0)))
  have hy : IsLocallyConstant y :=
    (((isLocallyConstant_charAdd χ).comp_continuous (continuous_apply 0)).comp reprIco)
  let x₂ := mkCochain (ratSES G).X₂ y hy
  have hx₂ : (coeffCochainsMap (ratSES G).g).f 1 x₂ = cocycleι (ratSES G).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    exact (coe_reprIco _).trans (hzv v).symm
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d (ratSES_shortExact G) 2 z x₂ hx₂
  refine ⟨x₁, ?_, fun v => ?_⟩
  · rw [charClassProf, ← hz]
    exact (δ_cohomologyπ_of_lift (ratSES_shortExact G) rfl z x₂ hx₂ x₁ hx₁).symm
  · have e := congrArg (fun c => cochainOf _ c v) hx₁
    simp only [cochainOf_cochainsMap_f] at e
    erw [cochainOf_d, d_one_trivial_apply] at e
    have hc := charCocycle_cast (charAdd χ) (v 0) (v 1)
    apply Int.cast_injective (α := ℚ)
    refine e.trans ?_
    rw [hc]
    change reprIco (charAdd χ (Additive.ofMul (v 1))) - reprIco (charAdd χ (Additive.ofMul (v 0 * v 1)))
      + reprIco (charAdd χ (Additive.ofMul (v 0))) = _
    ring

theorem exists_cocycle_cupCharClassProf (A : Rep ℤ G) [IsSmoothRep A] (χ : Additive G →ₜ+ QZ)
    (a : A.ρ.invariants) :
    ∃ w : cocycles A 2, cohomologyπ A 2 w = (cupCharClassProf A χ).hom a ∧
      ∀ v : Fin 2 → G, cochainOf A (cocycleι A 2 w) v = charCocycle (charAdd χ) (v 0, v 1) • (a : A) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv A a
  obtain ⟨x, hx, hxc⟩ := exists_cocycle_charClassProf χ
  let φ : A ⊗ Rep.trivial ℤ G ℤ ⟶ A := (ρ_ A).hom
  refine ⟨HomologicalComplex.cyclesMap (coeffCochainsMap φ) 2 (cupCocycles (zero_add 2) z0 x), ?_, ?_⟩
  · change _ = (coeffMap φ 2).hom (cup (zero_add 2) ((zeroIso A).inv.hom a) (charClassProf χ))
    rw [← hz0, ← hx, cup_cohomologyπ]
    exact (ConcreteCategory.congr_hom (cohomologyπ_coeffMap φ 2) _).symm
  · intro v
    have e := congrArg (fun ψ => cochainOf A (ψ.hom (cupCocycles (zero_add 2) z0 x)))
      (HomologicalComplex.cyclesMap_i (coeffCochainsMap φ) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    change cochainOf A (((cochains A).iCycles 2).hom _) v = _
    rw [e, cochainOf_cochainsMap_f]
    change φ.hom (cochainOf _ (cocycleι _ 2 (cupCocycles (zero_add 2) z0 x)) v) = _
    rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cupCochain_apply, hz0c]
    erw [hxc, rightUnitor_hom_tmul]
    exact int_smul_eq_zsmul _ _ _

theorem cupCharClassProf_eq_inflation [CompactSpace G] (A : Rep ℤ G) [IsSmoothRep A]
    (χ : Additive G →ₜ+ QZ) (U : OpenNormalSubgroup G)
    (ψ : Additive (G ⧸ (U : Subgroup G)) →+ AddCircle (1 : ℚ))
    (hψ : charAdd χ = charComp (U : Subgroup G) ψ) (a : A.ρ.invariants) :
    (cupCharClassProf A χ).hom a =
      (inflation A U 2).hom ((cupCharClass (A.quotientToInvariants (U : Subgroup G)) ψ).hom
        (invariantsToQuotient (U : Subgroup G) a)) := by
  have := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  change _ = (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((groupCohomology.isoCocycles₂ _).inv _))
  rw [inflation_π]
  congr 1
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cochainOf_cocycleι_cyclesMap_inflationCochains]
  funext v
  rw [hwc, groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  rw [hψ]
  rfl

end Cocycles

end ProfiniteInt

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory groupCohomology IntermediateField GroupCoh

section Generic

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem inhomogeneousCochains_d_one_apply (A : Rep.{u} k G) (f : (Fin 1 → G) → A) (g : Fin 2 → G) :
    (inhomogeneousCochains.d A 1).hom f g =
      A.ρ (g 0) (f (fun _ => g 1)) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  simp only [inhomogeneousCochains.d_hom_apply]
  simp only [e1]
  simp
  rw [e2, e3]
  abel

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem inflation_H2π_eq_zero_iff (A : Rep.{u} k G) [IsSmoothRep A] (U : OpenNormalSubgroup G)
    (z : cocycles₂ (A.quotientToInvariants (U : Subgroup G))) :
    (inflation A U 2).hom (H2π _ z) = 0 ↔
      ∃ f : G → A, IsLocallyConstant f ∧ ∀ g h : G,
        A.ρ g (f h) - f (g * h) + f g = (z ((g : G ⧸ (U : Subgroup G)), (h : G ⧸ (U : Subgroup G))) : A) := by
  change (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((isoCocycles₂ _).inv z)) = 0 ↔ _
  rw [inflation_π]
  change ((cochains A).homologyπ 2).hom _ = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  have hR : ∀ v : Fin 2 → G, cochainOf A (((cochains A).iCycles 2).hom
      ((HomologicalComplex.cyclesMap (inflationCochains A U) 2) ((isoCocycles₂ _).inv z))) v =
        (z ((v 0 : G ⧸ (U : Subgroup G)), (v 1 : G ⧸ (U : Subgroup G))) : A) := by
    intro v
    have e := congrFun (cochainOf_cocycleι_cyclesMap_inflationCochains U A ((isoCocycles₂ _).inv z)) v
    refine e.trans ?_
    rw [isoCocycles₂_inv_comp_iCocycles_apply]
    rfl
  have hL : ∀ (w : (cochains A).X 1) (v : Fin 2 → G),
      cochainOf A (((cochains A).d 1 2).hom w) v =
        A.ρ (v 0) (cochainOf A w (fun _ => v 1)) - cochainOf A w (fun _ => v 0 * v 1) +
          cochainOf A w (fun _ => v 0) := by
    intro w v
    have e := congrFun (cochainOf_d (A := A) w) v
    exact e.trans (inhomogeneousCochains_d_one_apply A _ v)
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w (fun _ => g),
      (isLocallyConstant_cochainOf w).comp_continuous (continuous_pi fun _ => continuous_id),
      fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    simp only at e
    rw [hL, hR] at e
    exact e
  · rintro ⟨f, hf, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    rw [hL, hR]
    exact hfz (v 0) (v 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coboundary of a `1`-cochain at `![g, h]`: `(d w)(g, h) = g · w(h) - w(gh) + w(g)`. -/
theorem inhomogeneousCochains_d_one_apply_vec (A : Rep.{u} k G) (w : (Fin 1 → G) → A) (g h : G) :
    (inhomogeneousCochains.d A 1).hom w ![g, h] = A.ρ g (w ![h]) - w ![g * h] + w ![g] := by
  refine (inhomogeneousCochains_d_one_apply A _ ![g, h]).trans ?_
  have e1 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 1) = ![h] := by
    funext i; fin_cases i; rfl
  have e2 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0 * (![g, h] : Fin 2 → G) 1) = ![g * h] := by
    funext i; fin_cases i; rfl
  have e3 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0) = ![g] := by
    funext i; fin_cases i; rfl
  rw [e1, e2, e3]
  rfl

/-- The coboundary of a locally constant `1`-cochain at `![g, h]`. -/
theorem cochainOf_d_one_apply (A : Rep.{u} k G) [IsSmoothRep A] (w : (cochains A).X 1)
    (g h : G) :
    cochainOf A (((cochains A).d 1 2).hom w) ![g, h] =
      A.ρ g (cochainOf A w ![h]) - cochainOf A w ![g * h] + cochainOf A w ![g] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h]).trans (inhomogeneousCochains_d_one_apply_vec A _ g h)

/-- A `2`-cocycle is a coboundary exactly when it is `(g, h) ↦ g · f(h) - f(gh) + f(g)` for a
locally constant `f : G → A`. -/
theorem cohomologyπ_two_eq_zero_iff (A : Rep.{u} k G) [IsSmoothRep A] (z : cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ f : G → A, IsLocallyConstant f ∧ ∀ g h : G,
      cochainOf A (cocycleι A 2 z) ![g, h] = A.ρ g (f h) - f (g * h) + f g := by
  change ((cochains A).homologyπ 2).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w ![g],
      (isLocallyConstant_cochainOf w).comp_continuous
        (continuous_pi fun i => by fin_cases i; exact continuous_id), fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    rw [cochainOf_d_one_apply] at e
    exact e.symm
  · rintro ⟨f, hf, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, cochainOf_d_one_apply]
    exact (hfz (v 0) (v 1)).symm

/-- For a trivial action the coboundary from degree `0` to degree `1` vanishes. -/
theorem cochains_d_zero_one_eq_zero_of_trivial (A : Rep.{u} k G) [IsSmoothRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) : (cochains A).d 0 1 = 0 := by
  rw [cochains_d_zero_one]
  ext f : 2
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  have h : ∀ x : Fin 0 → G, (f : (Fin 0 → G) → A) x = (f : (Fin 0 → G) → A) Fin.elim0 :=
    fun x => by rw [Subsingleton.elim x Fin.elim0]
  simp [inhomogeneousCochains.d_hom_apply, h, hA]
  rfl

/-- For a trivial action a `1`-cocycle has zero class exactly when it vanishes. -/
theorem cohomologyπ_one_eq_zero_iff_of_trivial (A : Rep.{u} k G) [IsSmoothRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (z : cocycles A 1) :
    cohomologyπ A 1 z = 0 ↔ ∀ g : G, cochainOf A (cocycleι A 1 z) ![g] = 0 := by
  change ((cochains A).homologyπ 1).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ,
    cochains_d_zero_one_eq_zero_of_trivial A hA]
  constructor
  · rintro ⟨w, hw⟩ g
    have e := congrArg (fun c => cochainOf A c ![g]) hw
    exact e.symm
  · intro h
    refine ⟨0, ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [hv]
    exact (h (v 0)).symm

/-- For a trivial action a `1`-cocycle is a homomorphism `G → A`. -/
theorem cochainOf_cocycleι_one_mul_of_trivial (A : Rep.{u} k G) [IsSmoothRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (z : cocycles A 1) (g h : G) :
    cochainOf A (cocycleι A 1 z) ![g * h] =
      cochainOf A (cocycleι A 1 z) ![g] + cochainOf A (cocycleι A 1 z) ![h] := by
  have e := congrFun (d_cocycleι z) ![g, h]
  rw [inhomogeneousCochains_d_one_apply_vec, hA, Pi.zero_apply] at e
  rw [← sub_eq_zero, ← neg_eq_zero, ← e]
  abel

/-- For a trivial action, the `1`-cocycle of a locally constant homomorphism `G → A`. -/
noncomputable def cocyclesOneOfHom (A : Rep.{u} k G) [IsSmoothRep A] (hA : ∀ (g : G) (a : A), A.ρ g a = a)
    (f : G → A) (hf : IsLocallyConstant f) (hmul : ∀ g h : G, f (g * h) = f g + f h) :
    cocycles A 1 :=
  (cochains A).cyclesMk
    (mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0))) 2
    (by simp) (by
      apply cochainOf_injective
      refine (cochainOf_d (A := A) _).trans ?_
      funext v
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      rw [hv, inhomogeneousCochains_d_one_apply_vec, cochainOf_mkCochain]
      change A.ρ (v 0) (f (v 1)) - f (v 0 * v 1) + f (v 0) = 0
      rw [hA, hmul]
      abel)

/-- The values of `cocyclesOneOfHom`. -/
theorem cochainOf_cocyclesOneOfHom (A : Rep.{u} k G) [IsSmoothRep A]
    (hA : ∀ (g : G) (a : A), A.ρ g a = a) (f : G → A) (hf : IsLocallyConstant f)
    (hmul : ∀ g h : G, f (g * h) = f g + f h) (v : Fin 1 → G) :
    cochainOf A (cocycleι A 1 (cocyclesOneOfHom A hA f hf hmul)) v = f (v 0) := by
  have e : cocycleι A 1 (cocyclesOneOfHom A hA f hf hmul) =
      mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)) :=
    (cochains A).i_cyclesMk _ _ _ _
  rw [e, cochainOf_mkCochain]

end Generic

def charKerOpen {G : Type*} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    OpenNormalSubgroup G where
  toSubgroup := charKer (charAdd χ)
  isOpen' := by
    have e : (charKer (charAdd χ) : Set G) = (fun g : G => χ (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    change IsOpen (charKer (charAdd χ) : Set G)
    rw [e]
    exact (isOpen_discrete _).preimage (χ.continuous_toFun.comp continuous_ofMul)
  isNormal' := inferInstance

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory groupCohomology IntermediateField GroupCoh


section Comparison

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

theorem toGroupCohomology_cupCharClassProf (A : Rep ℤ G) [IsSmoothRep A]
    (χ : Additive G →ₜ+ QZ) (a : A.ρ.invariants) :
    (toGroupCohomology A 2).hom ((cupCharClassProf A χ).hom a) =
      (cupCharClass A (charAdd χ)).hom a := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (cochainsι A) 2) w
  refine e.trans ?_
  change (groupCohomology.π A 2).hom _ = (groupCohomology.π A 2).hom ((isoCocycles₂ A).inv.hom _)
  congr 1
  apply (ModuleCat.mono_iff_injective ((inhomogeneousCochains A).iCycles 2)).1 inferInstance
  have e1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (cochainsι A) 2) w
  refine e1.trans ?_
  rw [isoCocycles₂_inv_comp_iCocycles_apply]
  funext v
  exact hwc v

variable [DiscreteTopology G] [IsCyclic G]

theorem cupCharClassProf_surjective (A : Rep ℤ G) [IsSmoothRep A] (χ : Additive G →ₜ+ QZ)
    (hχ : Function.Injective χ) : Function.Surjective (cupCharClassProf A χ).hom := by
  intro x
  have hinj : Function.Injective (toGroupCohomology A 2).hom := by
    rw [← isoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  have hχ' : Function.Injective (charAdd χ) := QZ.toAddCircle.injective.comp hχ
  obtain ⟨a, ha⟩ := cupCharClass_surjective (A := A) (charAdd χ) hχ'
    ((toGroupCohomology A 2).hom x)
  exact ⟨a, hinj (by rw [toGroupCohomology_cupCharClassProf, ha])⟩

end Comparison

section OrderTwo

variable {G : Type} [Group G] [Fintype G]

theorem eq_of_ne_one_of_card_eq_two (h : Fintype.card G = 2) {g g' : G} (hg : g ≠ 1) (hg' : g' ≠ 1) :
    g = g' := by
  classical
  by_contra hne
  have h3 : ({1, g, g'} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp [Ne.symm hg, Ne.symm hg']
  have := Finset.card_le_univ ({1, g, g'} : Finset G)
  omega

theorem char_eq_half_of_card_eq_two (h : Fintype.card G = 2) (χ : Additive G →+ QZ) {g : G}
    (hg : χ (Additive.ofMul g) ≠ 0) : χ (Additive.ofMul g) = QZ.mk (1 / 2) := by
  have h2 : (2 : ℕ) • χ (Additive.ofMul g) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ← h, pow_card_eq_one, ofMul_one, map_zero]
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div (by norm_num) h2
  rw [hm] at hg ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    apply hg
    rw [mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero]
  · rw [add_nsmul, one_nsmul, mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero, zero_add]
    norm_num

end OrderTwo

end Langlands.ProfiniteCohomology
