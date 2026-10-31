import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof

/-!
# Higher direct images of flasque modules and the square vanishing condition

Higher direct images of flasque modules vanish along every morphism of schemes. For a
commutative square `gZ ≫ i = i' ≫ g` with closed immersions `i` and `i'`, vanishing of the
higher direct images of `N` along `gZ` implies vanishing of the higher direct images of
`i'_* N` along `g`. This removes the third vanishing hypothesis from
`derivedRestrictionMap_comp_derivedBaseChangeMap`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

attribute [local instance] HasDerivedCategory.standard

section Flasque

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `F` flasque, the pushforward
`f_* I ⟶ f_* Q` is an epimorphism. -/
lemma epi_pushforward_map_of_isFlasque {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₁.presheaf] :
    Epi ((Scheme.Modules.pushforward f).map S.g) := by
  have hS' : (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).ShortExact := hS.map_of_exact _
  have : TopCat.Sheaf.IsFlasque (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).X₁ :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque S.X₁.presheaf)
  refine ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective _ ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro V t y hy
  have hsurj := (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact hS' (U := f ⁻¹ᵁ V))
  exact ⟨V, le_rfl, hsurj _, hy⟩

/-- Higher direct images of flasque modules vanish in every positive degree. -/
theorem isZero_higherDirectImage_of_isFlasque (q : ℕ) (F : X.Modules)
    [TopCat.Presheaf.IsFlasque F.presheaf] :
    IsZero ((higherDirectImage f (q + 1)).obj F) := by
  let G := Scheme.Modules.pushforward f
  change IsZero ((G.rightDerived (q + 1)).obj F)
  induction q generalizing F with
  | zero =>
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact F
    have := DerivedPlus.epi_rightDerivedδ_of_isZero G hS 0 1 rfl
      (G.isZero_rightDerived_obj_injective_succ 0 (Injective.under F))
    refine IsZero.of_epi_eq_zero (DerivedPlus.rightDerivedδ G hS 0 1 rfl) ?_
    have h0 : Epi ((G.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc F).g) := by
      have e : (G.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc F).g =
          (G.rightDerivedZeroIsoSelf.hom.app _ ≫
            G.map (PushforwardInjectiveAcyclic.injectiveSc F).g) ≫
            G.rightDerivedZeroIsoSelf.inv.app _ := by
        rw [← G.rightDerivedZeroIsoSelf.hom.naturality, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id]
      have : TopCat.Presheaf.IsFlasque
          (PushforwardInjectiveAcyclic.injectiveSc F).X₁.presheaf := ‹_›
      have := epi_pushforward_map_of_isFlasque f hS
      rw [e]
      infer_instance
    rw [← cancel_epi ((G.rightDerived 0).map (PushforwardInjectiveAcyclic.injectiveSc F).g),
      DerivedPlus.rightDerived_map_comp_δ, comp_zero]
  | succ n ih =>
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact F
    have := DerivedPlus.epi_rightDerivedδ_of_isZero G hS (n + 1) (n + 2) rfl
      (G.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under F))
    have : TopCat.Presheaf.IsFlasque (cokernel (Injective.ι F)).presheaf :=
      PushforwardInjectiveAcyclic.isFlasque_cokernel F
    exact IsZero.of_epi (DerivedPlus.rightDerivedδ G hS (n + 1) (n + 2) rfl)
      (ih (cokernel (Injective.ι F)))

/-- Pushforwards of injective modules have vanishing higher direct images along every
morphism. -/
theorem isZero_higherDirectImage_pushforward_injective {Z : Scheme.{u}} (h : Z ⟶ X)
    (J : Z.Modules) [Injective J] (q : ℕ) :
    IsZero ((higherDirectImage f (q + 1)).obj ((Scheme.Modules.pushforward h).obj J)) := by
  have : TopCat.Presheaf.IsFlasque J.presheaf := PushforwardInjectiveAcyclic.isFlasque_of_injective J
  have : TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward h).obj J).presheaf :=
    PushforwardInjectiveAcyclic.isFlasque_pushforward h J
  exact isZero_higherDirectImage_of_isFlasque f q _

end Flasque

section Square

variable {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (gZ : Z' ⟶ Z) (sq : gZ ≫ i = i' ≫ g)

include i sq in
/-- For a commutative square `gZ ≫ i = i' ≫ g` with closed immersions `i` and `i'`, if the
higher direct images of `N` along `gZ` vanish, so do the higher direct images of `i'_* N`
along `g`. -/
theorem isZero_higherDirectImage_pushforward_of_square (N : Z'.Modules)
    (hN : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj N)) (q : ℕ) :
    IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pushforward i').obj N)) := by
  have := preservesHomology_pushforward_of_isClosedImmersion i
  have := isIso_compComparison (Scheme.Modules.pushforward g)
    (pushforwardSquareIso g i i' gZ sq).symm N
    (isZero_higherDirectImage_of_isClosedImmersion i' N)
    (fun J _ q => isZero_higherDirectImage_pushforward_injective g i' J q) (q + 1)
  exact (isZero_rightDerived_comp_of_preservesHomology _ _ N (q + 1) (hN q)).of_iso
    (asIso (compComparison (Scheme.Modules.pushforward g)
      (pushforwardSquareIso g i i' gZ sq).symm N
      (isZero_higherDirectImage_of_isClosedImmersion i' N) (q + 1))).symm

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
include sq in
/-- Vanishing of the higher direct images along `gZ` transfers along the pullback comparison
`gZ^* i^* M ≅ i'^* g^* M`. -/
lemma isZero_higherDirectImage_pullbackSquare (M : X.Modules)
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M)))) (q : ℕ) :
    IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) :=
  (hMZ q).of_iso ((higherDirectImage gZ (q + 1)).mapIso
    ((pullbackSquareIso g i i' gZ sq).app M)).symm

include sq in
/-- The third vanishing hypothesis of `derivedRestrictionMap_comp_derivedBaseChangeMap` follows
from the second. -/
theorem isZero_higherDirectImage_pushforward_pullbackSquare (M : X.Modules)
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M)))) (q : ℕ) :
    IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pushforward i').obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)))) :=
  isZero_higherDirectImage_pushforward_of_square g i i' gZ sq _
    (isZero_higherDirectImage_pullbackSquare g i i' gZ sq M hMZ) q

end Square

section BaseChange

variable {X X' Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R') (f : X ⟶ Spec R)
  (f' : X' ⟶ Spec R') (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (gZ : Z' ⟶ Z)
  (sq : gZ ≫ i = i' ≫ g)

/-- Derived restriction along closed immersions commutes with derived base change, assuming
only the vanishing hypotheses of the two derived base change maps. -/
theorem derivedRestrictionMap_comp_derivedBaseChangeMap_of_vanishing (M : X.Modules)
    (hM : ∀ q : ℕ,
      IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M)))) :
    derivedRestrictionMap i f M ≫
        derivedBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M) hMZ ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections (i' ≫ f')) ⋙
            DerivedCategory.Plus.ι).map ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      derivedBaseChangeMap φ f f' g w M hM ≫
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
          (derivedRestrictionMap i' f' ((Scheme.Modules.pullback g).obj M)) :=
  derivedRestrictionMap_comp_derivedBaseChangeMap φ f f' g w i i' gZ sq M hM hMZ
    (isZero_higherDirectImage_pushforward_pullbackSquare g i i' gZ sq M hMZ)

/-- Degreewise form of `derivedRestrictionMap_comp_derivedBaseChangeMap_of_vanishing`. -/
theorem restrictionCohomologyMap_comp_baseChangeMap_of_vanishing (M : X.Modules)
    (hM : ∀ q : ℕ,
      IsZero ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hMZ : ∀ q : ℕ, IsZero ((higherDirectImage gZ (q + 1)).obj
      ((Scheme.Modules.pullback gZ).obj ((Scheme.Modules.pullback i).obj M))))
    (n : ℕ) :
    restrictionCohomologyMap i f M n ≫
        baseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm φ f f' g w i i' gZ sq)
          ((Scheme.Modules.pullback i).obj M) hMZ
          (fun J hJ q => (pushforwardInjectiveAcyclic Z' Z gZ J hJ q).2 R (i ≫ f)) n ≫
        (ModuleCat.restrictScalars φ.hom).map ((relativeCohomology (i' ≫ f') n).map
          ((pullbackSquareIso g i i' gZ sq).hom.app M)) =
      baseChangeMap φ f f' g w M hM
          (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n ≫
        (ModuleCat.restrictScalars φ.hom).map
          (restrictionCohomologyMap i' f' ((Scheme.Modules.pullback g).obj M) n) :=
  restrictionCohomologyMap_comp_baseChangeMap φ f f' g w i i' gZ sq M hM hMZ
    (isZero_higherDirectImage_pushforward_pullbackSquare g i i' gZ sq M hMZ) n

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
