/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints

/-!
# Points of a group scheme attached to derivations

The morphism `S[ε] ⟶ G`, `a ↦ g^♯(a) + ε d(a)`, attached to a derivation `d : 𝒪_G → g_*𝒪_S`
(`AlgebraicGeometry.GrpObj.pointOfDerivation`), and the morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S` attached
to it (`AlgebraicGeometry.GrpObj.homOfDerivation`).
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

/-! ### Points attached to derivations -/

omit [GrpObj G] in
/-- The morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S` attached to a derivation `d : 𝒪_G → g_*𝒪_S` over `f⁻¹𝒪_S`,
for a morphism `g : S ⟶ G`: the universal property of `Ω¹_{G/S}` and the adjunction
`g^* ⊣ g_*`. -/
noncomputable def homOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S :=
  ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).desc D))

omit [GrpObj G] in
theorem omegaHom_eq_homOfDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    omegaHom G v = homOfDerivation G _ (infDerivation G v) :=
  rfl

/-- The morphisms `ω_{G/S} ⟶ 𝒪_S` attached to derivations along two morphisms `g₁ = g₂ = e` agree
if the derivations do. -/
theorem pullbackCongr_inv_comp_homOfDerivation {g₁ g₂ : S ⟶ G.left} (h₁ : g₁ = unitSection G)
    (h₂ : g₂ = unitSection G)
    (D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (hD : ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)), D₁.d a ≍ D₂.d a) :
    (Scheme.Modules.pullbackCongr h₁).inv.app G.hom.cotangentSheaf ≫ homOfDerivation G g₁ D₁ =
      (Scheme.Modules.pullbackCongr h₂).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₂ D₂ := by
  subst h₁ h₂
  obtain rfl : D₁ = D₂ := by
    ext V a
    exact eq_of_heq (hD a)
  rfl

omit [GrpObj G] in
/-- The components `Γ(G, U) → Γ(S, g⁻¹U)` of a derivation `d : 𝒪_G → g_*𝒪_S`. -/
def derivationApp (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) : Γ(G.left, U) →+ Γ(S, g ⁻¹ᵁ U) :=
  D.d (X := Opposite.op U)

omit [GrpObj G] in
theorem derivationApp_mul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) (a b : Γ(G.left, U)) :
    derivationApp G g D U (a * b) =
      g.app U a * derivationApp G g D U b + g.app U b * derivationApp G g D U a :=
  D.d_mul a b

omit [GrpObj G] in
@[simp]
theorem derivationApp_one (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) :
    derivationApp G g D U 1 = 0 :=
  D.d_one _

omit [GrpObj G] in
theorem derivationApp_map (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) {U V : G.left.Opens} (i : V ⟶ U) (a : Γ(G.left, U)) :
    derivationApp G g D V (G.left.presheaf.map i.op a) =
      S.presheaf.map (homOfLE (g.preimage_mono i.le)).op (derivationApp G g D U a) :=
  D.d_map i.op a

omit [GrpObj G] in
/-- The ring homomorphism `Γ(G, U) → Γ(S, g⁻¹U)[ε]`, `a ↦ g^♯(a) + ε d(a)`, attached to a
derivation `d : 𝒪_G → g_*𝒪_S`. -/
noncomputable def pointOfDerivationRingHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : G.left.Opens) :
    Γ(G.left, U) →+* DualNumber Γ(S, g ⁻¹ᵁ U) where
  toFun a := inl (g.app U a) + inr (derivationApp G g D U a)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
        zero_add, smul_eq_mul, op_smul_eq_mul, map_mul]
      rw [derivationApp_mul]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

omit [GrpObj G] in
/-- The morphism of presheafed spaces `S[ε] ⟶ G`, `a ↦ g^♯(a) + ε d(a)`, attached to a derivation
`d : 𝒪_G → g_*𝒪_S`. -/
noncomputable def pointOfDerivationHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbers.toPresheafedSpace ⟶ G.left.toPresheafedSpace where
  base := g.base
  c :=
    { app U := CommRingCat.ofHom (pointOfDerivationRingHom G g D U.unop)
      naturality U V i := by
        ext a
        change pointOfDerivationRingHom G g D V.unop (G.left.presheaf.map i a) =
          DualNumber.mapRingHom (S.presheaf.map _).hom (pointOfDerivationRingHom G g D U.unop a)
        ext
        · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            fst_add, fst_inl, fst_inr, add_zero, DualNumber.fst_mapRingHom]
          exact ConcreteCategory.congr_hom (g.c.naturality i) a
        · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            snd_add, snd_inl, snd_inr, zero_add, DualNumber.snd_mapRingHom]
          exact derivationApp_map G g D i.unop a }

omit [GrpObj G] in
theorem ι_comp_pointOfDerivationHom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbersι.toPshHom ≫ pointOfDerivationHom G g D = g.toPshHom := by
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, PresheafedSpace.comp_base, eqToHom_refl,
    Functor.whiskerRight_id', TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj,
    TopologicalSpace.Opens.map_comp_obj, PresheafedSpace.comp_c_app, NatTrans.id_app,
    Category.comp_id, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  change (pointOfDerivationRingHom G g D U a).fst = g.app U a
  simp [pointOfDerivationRingHom]

omit [GrpObj G] in
/-- The morphism of schemes `S[ε] ⟶ G`, `a ↦ g^♯(a) + ε d(a)`, attached to a derivation
`d : 𝒪_G → g_*𝒪_S`: its stalk maps are local since their reductions modulo `ε` are those of `g`. -/
noncomputable def pointOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) : S.dualNumbers ⟶ G.left where
  toHom := pointOfDerivationHom G g D
  prop y := by
    have h := PresheafedSpace.stalkMap.comp S.dualNumbersι.toPshHom (pointOfDerivationHom G g D) y
    rw [PresheafedSpace.stalkMap.congr_hom _ _ (ι_comp_pointOfDerivationHom G g D),
      eqToHom_refl, Category.id_comp] at h
    have := g.prop y
    rw [h, CommRingCat.hom_comp] at this
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ this

omit [GrpObj G] in
@[reassoc (attr := simp)]
theorem ι_comp_pointOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    S.dualNumbersι ≫ pointOfDerivation G g D = g :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (ι_comp_pointOfDerivationHom G g D))

omit [GrpObj G] in
/-- A derivation over `f⁻¹𝒪_S` kills the functions pulled back from `S`. -/
theorem derivationApp_app (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (U : S.Opens) (b : Γ(S, U)) :
    derivationApp G g D (G.hom ⁻¹ᵁ U) (G.hom.app U b) = 0 := by
  have h : G.hom.c = (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      G.hom.base).unit.app S.presheaf ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} G.hom.base).map G.hom.pullbackPresheafHom := by
    rw [Scheme.Hom.pullbackPresheafHom]
    exact (((TopCat.Presheaf.pullbackPushforwardAdjunction _ _).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)).symm
  have h2 := ConcreteCategory.congr_hom (congr_app h (Opposite.op U)) b
  change D.d (G.hom.c.app (Opposite.op U) b) = 0
  rw [h2]
  exact D.d_app _

omit [GrpObj G] in
/-- The point attached to a derivation along a section `g` of `G ⟶ S` is a point over `S`. -/
theorem pointOfDerivation_comp_hom (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (hg : g ≫ G.hom = 𝟙 S) :
    pointOfDerivation G g D ≫ G.hom = S.dualNumbersProj := by
  rw [Scheme.eq_dualNumbersProj_comp_of_snd_eq_zero (pointOfDerivation G g D ≫ G.hom),
    ι_comp_pointOfDerivation_assoc, hg, Category.comp_id]
  intro U b
  change (pointOfDerivationRingHom G g D _ (G.hom.app U b)).snd = 0
  simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    snd_add, snd_inl, snd_inr, zero_add]
  exact derivationApp_app G g D U b

omit [GrpObj G] in
/-- A point `v : S[ε] ⟶ G` is the point attached to its derivation `d_v` along `i ≫ v`. -/
theorem pointOfDerivation_infDerivation (v : Scheme.dualNumbersOver S ⟶ G) :
    pointOfDerivation G (S.dualNumbersι ≫ v.left) (infDerivation G v) = v.left := by
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_))
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change pointOfDerivationRingHom G (S.dualNumbersι ≫ v.left) (infDerivation G v) U a =
    v.left.app U a
  ext
  · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      fst_add, fst_inl, fst_inr, add_zero]
    rfl
  · simp only [pointOfDerivationRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      snd_add, snd_inl, snd_inr, zero_add]
    rfl

omit [GrpObj G] in
theorem pointOfDerivation_congr {g₁ g₂ : S ⟶ G.left} (h : g₁ = g₂)
    {D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom}
    {D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom}
    (hD : ∀ {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)), D₁.d a ≍ D₂.d a) :
    pointOfDerivation G g₁ D₁ = pointOfDerivation G g₂ D₂ := by
  subst h
  obtain rfl : D₁ = D₂ := by
    ext V a
    exact eq_of_heq (hD a)
  rfl

end GrpObj

end InfPoints

end AlgebraicGeometry
