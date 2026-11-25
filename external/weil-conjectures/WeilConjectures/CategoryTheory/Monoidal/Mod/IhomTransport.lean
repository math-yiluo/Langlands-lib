/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomComp

/-!
# Transport of internal homs of modules along a lax monoidal functor

Let `G : C ⥤ D` be a lax braided functor and `ρ : B ⟶ G A` a morphism of commutative monoids,
`F = mapModComap ρ` the induced functor on modules. Suppose given comparison morphisms
`c M N : F Hom_A(M, N) ⟶ Hom_B(F M, F N)` whose uncurried forms are `G` of the evaluations. Given
isomorphisms `φ_M : F M ≅ M'`, `φ_N : F N ≅ N'`, we get `F Hom_A(M, N) ⟶ Hom_B(M', N')`
(`CategoryTheory.Mod.trHom`), and morphisms into internal homs whose uncurried forms are
compatible with the `φ`'s are compatible with these (`CategoryTheory.Mod.map_comp_trHom`). As an
application, `CategoryTheory.Mod.ihomIhomComparison` is compatible with such transports
(`CategoryTheory.Mod.map_ihomIhomComparison_comp_trHom`); this is used both for the pullback
along a weakly étale morphism and for the Weil structures.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (G : C ⥤ D) [G.LaxMonoidal]

omit [BraidedCategory C] [BraidedCategory D] in
/-- Transport of a composite pairing `(x ⊗ y) ⊗ z ↦ e (x ⊗ d (y ⊗ z))` along a lax monoidal
functor. -/
lemma tensorHom_associator_whiskerLeft_comp {X a E D' K : C} {X' a' E' D'' K' : D}
    (fX : G.obj X ⟶ X') (fa : G.obj a ⟶ a') (fE : G.obj E ⟶ E') (fD : G.obj D' ⟶ D'')
    (fK : G.obj K ⟶ K') (δ : a ⊗ E ⟶ D') (δ' : a' ⊗ E' ⟶ D'') (e : X ⊗ D' ⟶ K)
    (e' : X' ⊗ D'' ⟶ K') (hδ : (fa ⊗ₘ fE) ≫ δ' = Functor.LaxMonoidal.μ G _ _ ≫ G.map δ ≫ fD)
    (he : (fX ⊗ₘ fD) ≫ e' = Functor.LaxMonoidal.μ G _ _ ≫ G.map e ≫ fK) :
    ((fX ⊗ₘ fa) ⊗ₘ fE) ≫ (α_ _ _ _).hom ≫ X' ◁ δ' ≫ e' =
      Functor.LaxMonoidal.μ G _ _ ▷ G.obj E ≫ Functor.LaxMonoidal.μ G _ _ ≫
        G.map ((α_ _ _ _).hom ≫ X ◁ δ ≫ e) ≫ fK := by
  have h₁ : fX ⊗ₘ (Functor.LaxMonoidal.μ G _ _ ≫ G.map δ ≫ fD) =
      G.obj X ◁ (Functor.LaxMonoidal.μ G _ _ ≫ G.map δ) ≫ (fX ⊗ₘ fD) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.assoc]
  rw [associator_naturality_assoc, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, hδ, h₁, Category.assoc, he, G.map_comp, G.map_comp]
  simp only [Category.assoc]
  rw [associativity_assoc, MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right_assoc]

variable (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
  (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)

include hβ in
/-- Transport of the pairing `(x ⊗ y) ⊗ t ↦ e₂ (y ⊗ e₁ (t ⊗ x))` along a lax braided
functor. -/
lemma tensorHom_braiding_associator_comp {a E T H L : C} {a' E' T' H' L' : D}
    (fa : G.obj a ⟶ a') (fE : G.obj E ⟶ E') (fT : G.obj T ⟶ T') (fH : G.obj H ⟶ H')
    (fL : G.obj L ⟶ L') (e₁ : T ⊗ a ⟶ H) (e₁' : T' ⊗ a' ⟶ H') (e₂ : E ⊗ H ⟶ L)
    (e₂' : E' ⊗ H' ⟶ L') (h₁ : (fT ⊗ₘ fa) ≫ e₁' = Functor.LaxMonoidal.μ G _ _ ≫ G.map e₁ ≫ fH)
    (h₂ : (fE ⊗ₘ fH) ≫ e₂' = Functor.LaxMonoidal.μ G _ _ ≫ G.map e₂ ≫ fL) :
    ((fa ⊗ₘ fE) ⊗ₘ fT) ≫ (β_ a' E').hom ▷ T' ≫ (α_ _ _ _).hom ≫ E' ◁ ((β_ a' T').hom ≫ e₁') ≫
        e₂' =
      Functor.LaxMonoidal.μ G _ _ ▷ G.obj T ≫ Functor.LaxMonoidal.μ G _ _ ≫
        G.map ((β_ a E).hom ▷ T ≫ (α_ _ _ _).hom ≫ E ◁ ((β_ a T).hom ≫ e₁) ≫ e₂) ≫ fL := by
  have s₁ : ((fa ⊗ₘ fE) ⊗ₘ fT) ≫ (β_ a' E').hom ▷ T' =
      (β_ _ _).hom ▷ G.obj T ≫ ((fE ⊗ₘ fa) ⊗ₘ fT) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      BraidedCategory.braiding_naturality, Category.comp_id, Category.id_comp]
  have s₂ : (fE ⊗ₘ (fa ⊗ₘ fT)) ≫ E' ◁ ((β_ a' T').hom ≫ e₁') =
      G.obj E ◁ ((β_ _ _).hom ≫ Functor.LaxMonoidal.μ G _ _ ≫ G.map e₁) ≫ (fE ⊗ₘ fH) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, BraidedCategory.braiding_naturality_assoc, h₁]
    simp only [Category.assoc]
  rw [reassoc_of% s₁, associator_naturality_assoc, reassoc_of% s₂, h₂, G.map_comp, G.map_comp,
    G.map_comp]
  simp only [Category.assoc]
  rw [← μ_natural_left_assoc, ← comp_whiskerRight_assoc, hβ, comp_whiskerRight_assoc,
    associativity_assoc, ← μ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    G.map_comp, ← reassoc_of% (hβ a T)]

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

open scoped Obj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [SymmetricCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] (ρ : B ⟶ G.obj A) [IsMonHom ρ]
  (c : ∀ M N : Mod C A, (mapModComap ρ).obj ((ihom M).obj N) ⟶
    (ihom ((mapModComap ρ).obj M)).obj ((mapModComap ρ).obj N))

/-- The transport `F Hom_A(M, N) ⟶ Hom_B(F M, F N) ⟶ Hom_B(M', N')` along `φ_M : F M ≅ M'` and
`φ_N : F N ≅ N'`. -/
noncomputable def trHom {M N : Mod C A} {M' N' : Mod D B} (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') :
    (mapModComap ρ).obj ((ihom M).obj N) ⟶ (ihom M').obj N' :=
  c M N ≫ (ihomMap φM.inv).app _ ≫ (ihom M').map φN.hom

/-- The transport `F Hom_A(M, N) ≅ Hom_B(M', N')`, when the comparison is an isomorphism. -/
noncomputable def trIso [∀ M N, IsIso (c M N)] {M N : Mod C A} {M' N' : Mod D B}
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N') :
    (mapModComap ρ).obj ((ihom M).obj N) ≅ (ihom M').obj N' :=
  asIso (c M N) ≪≫ (ihomMapIso φM.symm).app _ ≪≫ (ihom M').mapIso φN

/-- The transport isomorphism has the transport morphism as underlying morphism. -/
lemma trIso_hom [∀ M N, IsIso (c M N)] {M N : Mod C A} {M' N' : Mod D B}
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N') :
    (trIso ρ c φM φN).hom = trHom ρ c φM φN :=
  rfl


/-- The transport is an isomorphism when the comparisons are. -/
instance isIso_trHom [∀ M N, IsIso (c M N)] {M N : Mod C A} {M' N' : Mod D B}
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N') :
    IsIso (trHom ρ c φM φN) :=
  inferInstanceAs (IsIso (trIso ρ c φM φN).hom)

variable {ρ c}
variable (hc : ∀ M N : Mod C A,
  uncurryHom (c M N) = Functor.LaxMonoidal.μ G _ _ ≫ G.map (evaluation M N))

include hc in
/-- The evaluation is compatible with the transport. -/
lemma trHom_evaluation {M N : Mod C A} {M' N' : Mod D B} (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') :
    ((trHom ρ c φM φN).hom ⊗ₘ φM.hom.hom) ≫ evaluation M' N' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (evaluation M N) ≫ φN.hom.hom := by
  have hφ : φM.hom.hom ≫ φM.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [trHom, Mod.comp_hom', Mod.comp_hom', tensorHom_def', comp_whiskerRight,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [evaluation_naturality, evaluation_ihomMap_assoc, ← whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hφ, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, ← Category.assoc, ← uncurryHom, hc, Category.assoc]

include hc in
/-- A morphism into an internal hom whose uncurried form is compatible with the `φ`'s is
compatible with the transport. -/
lemma map_comp_trHom {P M N : Mod C A} {P' M' N' : Mod D B} (φP : (mapModComap ρ).obj P ≅ P')
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N')
    (κ : P ⟶ (ihom M).obj N) (κ' : P' ⟶ (ihom M').obj N')
    (h : (φP.hom.hom ⊗ₘ φM.hom.hom) ≫ uncurryHom κ' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (uncurryHom κ) ≫ φN.hom.hom) :
    (mapModComap ρ).map κ ≫ trHom ρ c φM φN = φP.hom ≫ κ' := by
  have : IsIso φM.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map φM.hom))
  apply uncurryHom_injective
  rw [← cancel_epi (((mapModComap ρ).obj P).X ◁ φM.hom.hom)]
  simp only [uncurryHom, Mod.comp_hom', comp_whiskerRight, Category.assoc] at h ⊢
  rw [whisker_exchange_assoc]
  conv_lhs => rw [← tensorHom_def'_assoc, trHom_evaluation hc]
  conv_rhs => rw [← tensorHom_def'_assoc, h]
  rw [G.map_comp]
  exact (μ_natural_left_assoc G κ.hom M.X _).trans (by simp only [Category.assoc])

include hc in
/-- A morphism into an internal hom out of a tensor product, whose uncurried form is compatible
with the `φ`'s, is compatible with the transport. -/
lemma tensorHom_comp_eq_of_uncurry {P M N Q : Mod C A} {P' M' N' Q' : Mod D B}
    (φP : (mapModComap ρ).obj P ≅ P') (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') (φQ : (mapModComap ρ).obj Q ≅ Q')
    (u : P.X ⊗ M.X ⟶ ((ihom N).obj Q).X) (u' : P'.X ⊗ M'.X ⟶ ((ihom N').obj Q').X)
    (h : ((φP.hom.hom ⊗ₘ φM.hom.hom) ⊗ₘ φN.hom.hom) ≫ u' ▷ N'.X ≫ evaluation N' Q' =
      Functor.LaxMonoidal.μ G _ _ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G _ _ ≫
        G.map (u ▷ N.X ≫ evaluation N Q) ≫ φQ.hom.hom) :
    (φP.hom.hom ⊗ₘ φM.hom.hom) ≫ u' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map u ≫ (trHom ρ c φN φQ).hom := by
  have : IsIso φN.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map φN.hom))
  apply hom_ext_of_evaluation (D := N')
  rw [← cancel_epi ((((mapModComap ρ).obj P).X ⊗ ((mapModComap ρ).obj M).X) ◁ φN.hom.hom)]
  rw [comp_whiskerRight_assoc, ← tensorHom_def'_assoc]
  erw [h]
  symm
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc]
  erw [whisker_exchange_assoc, whisker_exchange_assoc, ← tensorHom_def'_assoc, trHom_evaluation hc,
    μ_natural_left_assoc]
  rw [G.map_comp, Category.assoc]
  rfl

variable (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
  (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)

include hc hβ in
/-- The uncurried form of `toIhomIhom` is compatible with the transport. -/
lemma tensorHom_uncurryHom_toIhomIhom [∀ M N, IsIso (c M N)] {a H L : Mod C A}
    {a' H' L' : Mod D B} (φa : (mapModComap ρ).obj a ≅ a') (φH : (mapModComap ρ).obj H ≅ H')
    (φL : (mapModComap ρ).obj L ≅ L') :
    (φa.hom.hom ⊗ₘ (trIso ρ c φH φL).hom.hom) ≫ uncurryHom (toIhomIhom a' H' L') =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (uncurryHom (toIhomIhom a H L)) ≫
        (trHom ρ c (trIso ρ c φa φH) φL).hom :=
  tensorHom_comp_eq_of_uncurry hc φa (trIso ρ c φH φL) (trIso ρ c φa φH) φL _ _ (by
    rw [uncurryHom_toIhomIhom, uncurryHom_toIhomIhom]
    exact tensorHom_braiding_associator_comp G hβ _ _ _ _ _ _ _ _ _
      (trHom_evaluation hc φa φH) (trHom_evaluation hc φH φL))

include hc hβ in
/-- **`ihomIhomComparison` is compatible with transport along a lax braided functor.** -/
theorem map_ihomIhomComparison_comp_trHom [∀ M N, IsIso (c M N)] {a H L K : Mod C A}
    {a' H' L' K' : Mod D B} (φa : (mapModComap ρ).obj a ≅ a')
    (φH : (mapModComap ρ).obj H ≅ H') (φL : (mapModComap ρ).obj L ≅ L')
    (φK : (mapModComap ρ).obj K ≅ K') :
    (mapModComap ρ).map (ihomIhomComparison a H L K) ≫
        trHom ρ c φa (trIso ρ c (trIso ρ c φH φL) φK) =
      (trIso ρ c (trIso ρ c (trIso ρ c φa φH) φL) φK).hom ≫ ihomIhomComparison a' H' L' K' :=
  map_comp_trHom hc _ φa _ _ _ (tensorHom_comp_eq_of_uncurry hc _ φa (trIso ρ c φH φL) φK _ _ (by
    rw [uncurryHom_ihomIhomComparison, uncurryHom_ihomIhomComparison]
    exact tensorHom_associator_whiskerLeft_comp G _ _ _ _ _ _ _ _ _
      (tensorHom_uncurryHom_toIhomIhom hc hβ φa φH φL) (trHom_evaluation hc _ φK)))

include hc hβ in
/-- If the comparisons are isomorphisms, the transported `ihomIhomComparison` is an isomorphism if
`ihomIhomComparison` of the transported modules is. -/
lemma isIso_map_ihomIhomComparison [∀ M N, IsIso (c M N)] {a H L K : Mod C A}
    {a' H' L' K' : Mod D B} (φa : (mapModComap ρ).obj a ≅ a')
    (φH : (mapModComap ρ).obj H ≅ H') (φL : (mapModComap ρ).obj L ≅ L')
    (φK : (mapModComap ρ).obj K ≅ K') [IsIso (ihomIhomComparison a' H' L' K')] :
    IsIso ((mapModComap ρ).map (ihomIhomComparison a H L K)) := by
  have : IsIso ((mapModComap ρ).map (ihomIhomComparison a H L K) ≫
      trHom ρ c φa (trIso ρ c (trIso ρ c φH φL) φK)) := by
    rw [map_ihomIhomComparison_comp_trHom hc hβ φa φH φL φK]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (trHom ρ c φa (trIso ρ c (trIso ρ c φH φL) φK))

include hc hβ in
/-- `CategoryTheory.Mod.map_ihomIhomComparison_comp_trHom` with the transports given as variables
equal to the iterated transports. -/
theorem map_ihomIhomComparison_comp_of_eq [∀ M N, IsIso (c M N)] {a H L K : Mod C A}
    {a' H' L' K' : Mod D B} (φa : (mapModComap ρ).obj a ≅ a')
    (φH : (mapModComap ρ).obj H ≅ H') (φL : (mapModComap ρ).obj L ≅ L')
    (φK : (mapModComap ρ).obj K ≅ K')
    (tE : (mapModComap ρ).obj ((ihom H).obj L) ≅ (ihom H').obj L')
    (hE : tE = trIso ρ c φH φL)
    (tT : (mapModComap ρ).obj ((ihom a).obj H) ≅ (ihom a').obj H')
    (hT : tT = trIso ρ c φa φH)
    (tD : (mapModComap ρ).obj ((ihom ((ihom a).obj H)).obj L) ≅ (ihom ((ihom a').obj H')).obj L')
    (hD : tD = trIso ρ c tT φL)
    (tEK : (mapModComap ρ).obj ((ihom ((ihom H).obj L)).obj K) ≅
      (ihom ((ihom H').obj L')).obj K')
    (hEK : tEK = trIso ρ c tE φK)
    (tS : (mapModComap ρ).obj ((ihom ((ihom ((ihom a).obj H)).obj L)).obj K) ≅
      (ihom ((ihom ((ihom a').obj H')).obj L')).obj K')
    (hS : tS = trIso ρ c tD φK)
    (tG : (mapModComap ρ).obj ((ihom a).obj ((ihom ((ihom H).obj L)).obj K)) ≅
      (ihom a').obj ((ihom ((ihom H').obj L')).obj K'))
    (hG : tG = trIso ρ c φa tEK) :
    (mapModComap ρ).map (ihomIhomComparison a H L K) ≫ tG.hom =
      tS.hom ≫ ihomIhomComparison a' H' L' K' := by
  subst hE hT hD hEK hS hG
  exact map_ihomIhomComparison_comp_trHom hc hβ φa φH φL φK

end CategoryTheory.Mod
