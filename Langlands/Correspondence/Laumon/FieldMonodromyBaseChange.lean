import Langlands.Correspondence.Laumon.FieldMonodromy
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift

/-!
# Change of field for the monodromy of lisse sheaves on the spectrum of a field
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

-- Use the instances with which the lisse stalk functor was defined.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

namespace Langlands.Henniart.Laumon

open ProEtale Scheme.FiniteEtale

section Restriction

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Restriction over `Z` with the target pullback transported along `h ≫ t = s`. -/
private theorem resOver_app_comp_map_upperStarCongr {S T Z : Scheme.{u}} {s : S ⟶ Z}
    {t : T ⟶ Z} (h : S ⟶ T) (e : h ≫ t = s) (F : Sheaf (Scheme.ProEt.topology Z) A) :
    (resOver A h (rfl : h ≫ t = h ≫ t)).app F ≫
        (Sheaf.Γ _ A).map ((upperStarCongr A e).hom.app F) = (resOver A h e).app F := by
  subst s
  simp [upperStarCongr]

/-- Restriction over `Y` along `h` followed by `Γ(S₁, (y₁ ≫ f)^* F) ≅ Γ(S₁, y₁^* f^* F)` is
`Γ(S₂, (y₂ ≫ f)^* F) ≅ Γ(S₂, y₂^* f^* F)` followed by restriction over `X` along `h`. -/
private theorem resOver_app_comp_map_upperStarComp {X Y S₁ S₂ : Scheme.{u}} (f : X ⟶ Y)
    {y₁ : S₁ ⟶ X} {y₂ : S₂ ⟶ X} (h : S₁ ⟶ S₂) (e : h ≫ y₂ = y₁) (e' : h ≫ y₂ ≫ f = y₁ ≫ f)
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (resOver A h e').app F ≫ (Sheaf.Γ _ A).map ((upperStarComp A y₁ f).hom.app F) =
      (Sheaf.Γ _ A).map ((upperStarComp A y₂ f).hom.app F) ≫
        (resOver A h e).app ((f)^*[A].obj F) := by
  have hn := (globalSectionsToUpperStar A h).naturality ((upperStarComp A y₂ f).hom.app F)
  simp only [Functor.comp_map] at hn
  rw [resOver_app, resOver_app, Category.assoc, reassoc_of% hn, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  have key := upperStarFactor_hom_app_assoc A (rfl : y₂ ≫ f = y₂ ≫ f) e' e
    (rfl : y₁ ≫ f = y₁ ≫ f) F
  rw [upperStarFactor_rfl, upperStarFactor_rfl] at key
  rw [← cancel_epi ((upperStarFactor A e').hom.app F), Iso.hom_inv_id_app_assoc,
    reassoc_of% key, Iso.hom_inv_id_app, Category.comp_id]

/-- A commuting square of maps over the base gives a commuting square on sections after
pullback. -/
private theorem resOver_baseChange {X Y S T : Scheme.{u}} (f : X ⟶ Y)
    (s : S ⟶ Y) (t : T ⟶ X) (i : T ⟶ S) (hi : i ≫ s = t ≫ f)
    (a : S ⟶ S) (b : T ⟶ T) (ha : a ≫ s = s) (hb : b ≫ t = t)
    (h : i ≫ a = b ≫ i) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (resOver A a ha).app F ≫
      ((resOver A i hi).app F ≫ (Sheaf.Γ _ A).map ((upperStarComp A t f).hom.app F)) =
    ((resOver A i hi).app F ≫ (Sheaf.Γ _ A).map ((upperStarComp A t f).hom.app F)) ≫
      (resOver A b hb).app ((f)^*[A].obj F) := by
  have hbt : b ≫ t ≫ f = t ≫ f := by rw [← Category.assoc, hb]
  have hia : (i ≫ a) ≫ s = t ≫ f := by rw [Category.assoc, ha, hi]
  have hbi : (b ≫ i) ≫ s = t ≫ f := by rw [Category.assoc, hi, hbt]
  rw [← Category.assoc, resOver_comp A i a hi ha hia F, Category.assoc,
    ← resOver_app_comp_map_upperStarComp A f b hb hbt F, ← Category.assoc,
    resOver_comp A b i hbt hi hbi F, resOver_congr A h hia hbi]

end Restriction

section Galois

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The Galois action is the inverse reparametrization path for `Spec σ`, followed by the
identification of the two geometric points. -/
private theorem galoisToAut_asIso_eq {K₀ : Type u} [CommRing K₀] [Algebra K₀ (AlgebraicClosure Ω)]
    (y : Spec (.of K₀) ⟶ Y) (σ : AlgebraicClosure Ω ≃ₐ[K₀] AlgebraicClosure Ω) :
    (galoisToAut y σ).asIso =
      (fiberReparamIso (specMapIso σ.toRingEquiv) (pointOfAlgebra (AlgebraicClosure Ω) y)).symm ≪≫
        eqToIso (congrArg fiber (specMapIso_hom_comp_pointOfAlgebra y σ)) := by
  ext P x
  apply fiber_ext
  rw [galoisToAut_hom_app_left, Iso.trans_hom, NatTrans.comp_app, FintypeCat.comp_apply,
    eqToIso_fiber_hom_app_left (specMapIso_hom_comp_pointOfAlgebra y σ),
    Iso.symm_hom, fiberReparamIso_inv_app_left]
  rfl

variable {l : ℕ} [Fact l.Prime]

/-- Transport by precomposition with a point isomorphism is restriction of sections. -/
private theorem mono_precomp_hom_app (M : LisseMonodromy l Y Ω)
    (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (e : a.hom ≫ y = z)
    (G : LisseSheaf l Y) :
    (M.mono ((fiberReparamIso a y).symm ≪≫ eqToIso (congrArg fiber e))).hom.app G =
      (resOver (WeilCoefficients.{u} l) a.hom e).app G.obj.X := by
  have h : (M.mono (fiberReparamIso a y)).app G = reparamStalkIso l a y G.obj.X :=
    Iso.ext (M.mono_reparam a y G)
  rw [M.mono_trans, Iso.trans_hom, NatTrans.comp_app, M.mono_eqToIso_hom_app e,
    M.mono_symm, Iso.symm_hom, ← Iso.app_inv, h,
    ← Scheme.UniversalCovers.resOver_app_eq_reparamStalkIso_inv]
  exact resOver_app_comp_map_upperStarCongr _ _ e G.obj.X

/-- The Galois action on a stalk is restriction of sections along `Spec σ`. -/
theorem LisseMonodromy.mono_galoisToAut_hom_app (M : LisseMonodromy l Y Ω) {K₀ : Type u}
    [CommRing K₀] [Algebra K₀ (AlgebraicClosure Ω)] (y : Spec (.of K₀) ⟶ Y)
    (σ : AlgebraicClosure Ω ≃ₐ[K₀] AlgebraicClosure Ω) (G : LisseSheaf l Y) :
    (M.mono (galoisToAut y σ).asIso).hom.app G =
      (resOver (WeilCoefficients.{u} l) (specMapIso σ.toRingEquiv).hom
        (specMapIso_hom_comp_pointOfAlgebra y σ)).app G.obj.X := by
  rw [galoisToAut_asIso_eq]
  exact mono_precomp_hom_app M _ (specMapIso_hom_comp_pointOfAlgebra y σ) G

end Galois

section Stalk

open Scheme

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y]
  {Ω Ω' : Type u} [Field Ω] [Field Ω'] {l : ℕ} [Fact l.Prime]
  {y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} {z : Spec (.of (AlgebraicClosure Ω')) ⟶ Y}
  (a : Spec (.of (AlgebraicClosure Ω')) ⟶ Spec (.of (AlgebraicClosure Ω)))
  (ha : a ≫ y = z) (G : LisseSheaf l Y)

local notation "U" => Scheme.universalCovers Y Ω

private theorem isIso_resOver_stalk :
    IsIso ((resOver (WeilCoefficients.{u} l) a ha).app G.obj.X) := by
  have := (U).isIso_ptRes_app
    (fun t H ↦ IsAdicLisseSheaf.exists_iso_upperStar_universalCover U t H.property) y G
  have hξ : (a ≫ (U).pt y) ≫ (U).proj y = z := by rw [Category.assoc, (U).pt_proj, ha]
  have hcomp : ((U).ptRes l y).app G.obj.X ≫ (resOver (WeilCoefficients.{u} l) a ha).app G.obj.X =
      (liftRes l y (a ≫ (U).pt y) hξ).app G.obj.X :=
    resOver_comp (WeilCoefficients.{u} l) a ((U).pt y) ha ((U).pt_proj y) hξ G.obj.X
  have := isIso_liftRes_app (l := l) y (a ≫ (U).pt y) hξ G
  exact IsIso.of_isIso_fac_left hcomp

end Stalk

section Field

variable {K L Ω ΩL : Type u} [Field K] [Field L] [Field Ω] [Field ΩL]
  [Algebra K L] [Algebra K ΩL] [Algebra L ΩL] [IsScalarTower K L ΩL]
  [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosure L ΩL]

private def extendEmbedding (ι : Ω →ₐ[K] ΩL) : AlgebraicClosure Ω →+* AlgebraicClosure ΩL :=
  letI : Algebra Ω (AlgebraicClosure ΩL) :=
    ((algebraMap ΩL (AlgebraicClosure ΩL)).comp ι.toRingHom).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure Ω →ₐ[Ω] AlgebraicClosure ΩL).toRingHom

omit [IsSepClosure K Ω] in
private theorem extendEmbedding_algebraMap (ι : Ω →ₐ[K] ΩL) (x : Ω) :
    extendEmbedding ι (algebraMap Ω (AlgebraicClosure Ω) x) =
      algebraMap ΩL (AlgebraicClosure ΩL) (ι x) := by
  let : Algebra Ω (AlgebraicClosure ΩL) :=
    ((algebraMap ΩL (AlgebraicClosure ΩL)).comp ι.toRingHom).toAlgebra
  exact (IsAlgClosed.lift : AlgebraicClosure Ω →ₐ[Ω] AlgebraicClosure ΩL).commutes x

private theorem fieldGaloisLift_algebraMap {F E : Type u} [Field F] [Field E]
    [Algebra F E] [IsSepClosure F E] (σ : Gal(E/F)) (x : E) :
    fieldGaloisLift F E σ (algebraMap E (AlgebraicClosure E) x) =
      algebraMap E (AlgebraicClosure E) (σ x) := by
  have h : (fieldGaloisLift F E σ).restrictNormal E = σ :=
    (fieldGaloisLift F E).symm_apply_apply σ
  rw [← AlgEquiv.restrictNormal_commutes, h]

omit [Algebra K L] [IsScalarTower K L ΩL] in
private theorem extendEmbedding_commutes (ι : Ω →ₐ[K] ΩL) (σ : Gal(Ω/K)) (τ : Gal(ΩL/L))
    (h : ∀ x, ι (σ x) = τ (ι x)) :
    (extendEmbedding ι).comp (fieldGaloisLift K Ω σ).toRingEquiv.toRingHom =
      (fieldGaloisLift L ΩL τ).toRingEquiv.toRingHom.comp (extendEmbedding ι) := by
  have := IsSepClosure.sep_closed K (K := Ω)
  have : IsPurelyInseparable Ω (AlgebraicClosure Ω) :=
    Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
  apply IsPurelyInseparable.injective_comp_algebraMap Ω (AlgebraicClosure Ω) (AlgebraicClosure ΩL)
  ext x
  change extendEmbedding ι (fieldGaloisLift K Ω σ (algebraMap Ω (AlgebraicClosure Ω) x)) =
    fieldGaloisLift L ΩL τ (extendEmbedding ι (algebraMap Ω (AlgebraicClosure Ω) x))
  rw [fieldGaloisLift_algebraMap, extendEmbedding_algebraMap, extendEmbedding_algebraMap,
    fieldGaloisLift_algebraMap, h]

private abbrev specEmbedding (ι : Ω →ₐ[K] ΩL) :
    Spec (.of (AlgebraicClosure ΩL)) ⟶ Spec (.of (AlgebraicClosure Ω)) :=
  Spec.map (CommRingCat.ofHom (extendEmbedding ι))

omit [IsSepClosure K Ω] [IsSepClosure L ΩL] in
private theorem specEmbedding_point (ι : Ω →ₐ[K] ΩL) :
    specEmbedding ι ≫ fieldGeometricPoint K Ω = fieldGeometricPoint L ΩL ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  simp only [fieldGeometricPoint, pointOfAlgebra, Category.comp_id, ← Spec.map_comp]
  congr 1
  ext x
  change extendEmbedding ι (algebraMap K (AlgebraicClosure Ω) x) =
    algebraMap L (AlgebraicClosure ΩL) (algebraMap K L x)
  rw [IsScalarTower.algebraMap_apply K Ω (AlgebraicClosure Ω), extendEmbedding_algebraMap,
    ι.commutes, IsScalarTower.algebraMap_apply L ΩL (AlgebraicClosure ΩL),
    IsScalarTower.algebraMap_apply K L ΩL]

variable {l : ℕ} [Fact l.Prime]

local notation "s_K" => fieldGeometricPoint K Ω
local notation "s_L" => fieldGeometricPoint L ΩL
local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap K L))

private def fieldStalkBaseChangeIso (ι : Ω →ₐ[K] ΩL) (G : LisseSheaf l (Spec (.of K))) :
    (lisseStalk l s_K).obj G ≅ (lisseStalk l s_L).obj (G.upperStar l f) := by
  let r := (resOver (WeilCoefficients.{u} l) (specEmbedding ι)
    (specEmbedding_point (L := L) ι)).app G.obj.X
  let hr : IsIso r := isIso_resOver_stalk (specEmbedding ι) (specEmbedding_point (L := L) ι) G
  exact @asIso (WeilCoefficients.{u} l) _ _ _ r hr ≪≫ upperStarStalkIso l f s_L G.obj.X

/-- The stalk over `K` identifies with the stalk of the pullback to `L` through the embedding of
separable closures `ι`. -/
def fieldMonodromyBaseChange (ι : Ω →ₐ[K] ΩL) (G : LisseSheaf l (Spec (.of K))) :
    LisseMonodromy.StalkSpace s_K G ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace s_L (G.upperStar l f) :=
  WeilCoefficients.linearEquivOfIso (fieldStalkBaseChangeIso ι G)

private theorem fieldStalkBaseChangeIso_commutes (ι : Ω →ₐ[K] ΩL)
    (G : LisseSheaf l (Spec (.of K))) (σ : Gal(Ω/K)) (τ : Gal(ΩL/L))
    (h : ∀ x, ι (σ x) = τ (ι x)) :
    ((universalLisseMonodromy l (Spec (.of K)) Ω).mono
      (fieldGaloisToAut K Ω σ).asIso).hom.app G ≫ (fieldStalkBaseChangeIso ι G).hom =
      (fieldStalkBaseChangeIso ι G).hom ≫ ((universalLisseMonodromy l (Spec (.of L)) ΩL).mono
        (fieldGaloisToAut L ΩL τ).asIso).hom.app (G.upperStar l f) := by
  let a := (specMapIso (fieldGaloisLift K Ω σ).toRingEquiv).hom
  let b := (specMapIso (fieldGaloisLift L ΩL τ).toRingEquiv).hom
  have ha : a ≫ s_K = s_K :=
    specMapIso_hom_comp_pointOfAlgebra (𝟙 (Spec (.of K))) (fieldGaloisLift K Ω σ)
  have hb : b ≫ s_L = s_L :=
    specMapIso_hom_comp_pointOfAlgebra (𝟙 (Spec (.of L))) (fieldGaloisLift L ΩL τ)
  have hab : specEmbedding ι ≫ a = b ≫ specEmbedding ι := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (Spec.map ∘ CommRingCat.ofHom) (extendEmbedding_commutes ι σ τ h)
  have hK : ((universalLisseMonodromy l (Spec (.of K)) Ω).mono
      (fieldGaloisToAut K Ω σ).asIso).hom.app G =
      (resOver (WeilCoefficients.{u} l) a ha).app G.obj.X :=
    LisseMonodromy.mono_galoisToAut_hom_app (universalLisseMonodromy l (Spec (.of K)) Ω)
      (𝟙 (Spec (.of K))) (fieldGaloisLift K Ω σ) G
  have hL : ((universalLisseMonodromy l (Spec (.of L)) ΩL).mono
      (fieldGaloisToAut L ΩL τ).asIso).hom.app (G.upperStar l f) =
      (resOver (WeilCoefficients.{u} l) b hb).app ((f)^*[WeilCoefficients.{u} l].obj G.obj.X) :=
    LisseMonodromy.mono_galoisToAut_hom_app (universalLisseMonodromy l (Spec (.of L)) ΩL)
      (𝟙 (Spec (.of L))) (fieldGaloisLift L ΩL τ) (G.upperStar l f)
  rw [hK, hL]
  exact resOver_baseChange (WeilCoefficients.{u} l) f s_K s_L (specEmbedding ι)
    (specEmbedding_point (L := L) ι) a b ha hb hab G.obj.X

/-- The stalk comparison intertwines the actions of compatible automorphisms of the two separable
closures. -/
theorem fieldMonodromyBaseChange_commutes (ι : Ω →ₐ[K] ΩL) (G : LisseSheaf l (Spec (.of K)))
    (σ : Gal(Ω/K)) (τ : Gal(ΩL/L)) (h : ∀ x, ι (σ x) = τ (ι x))
    (v : LisseMonodromy.StalkSpace s_K G) :
    fieldMonodromyBaseChange ι G (fieldMonodromy l K Ω G σ v) =
      fieldMonodromy l L ΩL (G.upperStar l f) τ (fieldMonodromyBaseChange ι G v) := by
  have e := congrArg ((WeilCoefficients.toModuleCat l).map)
    (fieldStalkBaseChangeIso_commutes ι G σ τ h)
  simp only [Functor.map_comp] at e
  exact congrArg (fun m ↦ ModuleCat.Hom.hom m v) e

end Field

end Langlands.Henniart.Laumon
