import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Building.UnramifiedValuationDescentReduction

/-! # The affine apartment map in unramified descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}


private instance affineDescentExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (hiT : IsMaximalSplitTorus (T := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hE : RelativeRoot.HasOppositeFactorPairs (T := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (B : ValuationBuildingData G) (f : B.S ⟶ T)

/-- Fixedness of an upper apartment point under all coefficient automorphisms. -/
def apartmentGaloisFixed (x : D.Apartment) : Prop :=
  ∀ σ : (inertiaFixedField F) ≃ₐ[F] (inertiaFixedField F), RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val

/-- Torus-then-field restriction of an upper apartment point. -/
def apartmentRestriction (x : D.Apartment) : RootFunctionFamily B.S G :=
  torusFieldRestrictedRootFunctionFamily (k := F) (K := (inertiaFixedField F)) (G := G) (T := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)) (j := ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE x.isValuation
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)

/-- Restriction preserves a translation coming from the lower torus. -/
theorem apartmentRestriction_descent_vadd (x y : D.Apartment) (v : V B.S)
    (h : y.val = descentCocharacterMap F (inertiaFixedField F) f
      B.isMaximalSplitTorus.isSplitSubtorus.1 v +ᵥ x.val) :
    apartmentRestriction hiT hE D B f y =
      v +ᵥ apartmentRestriction hiT hE D B f x := by
  unfold apartmentRestriction
  have ht := torusFieldRestrictedRootFunctionFamily_descent_vadd
    (k := F) (K := inertiaFixedField F) (S := B.S) (T := T) (G := G)
    f iT B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
    (φ := x.val) (ψ := y.val) x.isValuation y.isValuation v h
  exact ht

variable
  (hcar : ∀ ψ : RootFunctionFamily B.S G,
    ψ ∈ B.apartment.carrier ↔ ∃ x : D.Apartment, (apartmentGaloisFixed D) x ∧ ψ = (apartmentRestriction hiT hE D B f) x)
  (hinj : ∀ x y : D.Apartment, (apartmentGaloisFixed D) x → (apartmentGaloisFixed D) y → (apartmentRestriction hiT hE D B f) x = (apartmentRestriction hiT hE D B f) y → x = y)

include hinj in
/-- Translation of a descended apartment point is the pushed-forward translation
of its Galois-fixed lift. -/
theorem descentPoint_val_mk_vadd (v : V B.S) (w : B.Apartment) :
    (descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar
      ((Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ w)).val =
      (descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v +ᵥ (descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w).val := by
  let x := descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w
  let y : D.Apartment := ⟨(descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v +ᵥ x.val, D.vadd_mem x.mem _⟩
  have hx : apartmentGaloisFixed D x :=
    descentPoint_fixed B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w
  have hy : (apartmentGaloisFixed D) y := by
    intro σ
    change RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ ((descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v +ᵥ x.val) = (descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v +ᵥ x.val
    rw [RootFunctionFamily.galoisAction_vadd, galoisCocharacterAction_descentCocharacterMap,
      hx σ]
  have hres : (apartmentRestriction hiT hE D B f) y = v +ᵥ (apartmentRestriction hiT hE D B f) x :=
    apartmentRestriction_descent_vadd hiT hE D B f x y v rfl
  have hxres : w.val = (apartmentRestriction hiT hE D B f) x :=
    descentPoint_val B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w
  have hval : ((Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ w).val = (apartmentRestriction hiT hE D B f) y := by
    calc
      _ = v +ᵥ w.val := KPApartmentData.val_mk_vadd v w
      _ = v +ᵥ (apartmentRestriction hiT hE D B f) x := congrArg (v +ᵥ ·) hxres
      _ = _ := hres.symm
  have heq : descentPoint B (apartmentGaloisFixed D)
      (apartmentRestriction hiT hE D B f) hcar
      ((Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ w) = y :=
    descentPoint_eq B (apartmentGaloisFixed D)
      (apartmentRestriction hiT hE D B f) hcar hinj hy _ hval
  exact congrArg (fun z : D.Apartment => z.val) heq

include hiT hE D hcar hinj in
/-- The cocharacter push-forward respects the kernels used to form the reduced
translation spaces. -/
theorem descentCocharacterMap_mem_rootAnnihilator (v : V B.S)
    (hv : v ∈ rootAnnihilator B.i) : (descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v ∈ rootAnnihilator (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty B.Apartment)
  have hw : (Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ w = w :=
    KPApartmentData.Apartment.ext (w.isValuation.vadd_eq_self_iff.2 hv)
  have h := descentPoint_val_mk_vadd hiT hE D B f hcar hinj v w
  rw [hw] at h
  exact (descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w).isValuation.vadd_eq_self_iff.1 h.symm

/-- The linear part of the fixed-lift apartment map, induced by scalar extension
and the torus inclusion on real cocharacters. -/
def descentTranslationMap : TranslationSpace B.i →ₗ[ℝ] TranslationSpace (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
  (rootAnnihilator B.i).liftQ ((rootAnnihilator (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)).mkQ.comp (descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1)) (by
    intro v hv
    change (Submodule.Quotient.mk ((descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v) : TranslationSpace (S := ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (descentCocharacterMap_mem_rootAnnihilator hiT hE D B f hcar hinj v hv))

@[simp]
theorem descentTranslationMap_mk (v : V B.S) :
    descentTranslationMap hiT hE D B f hcar hinj (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((descentCocharacterMap F (inertiaFixedField F) f B.isMaximalSplitTorus.isSplitSubtorus.1) v) := rfl

/-- The existing `descentPoint` map is affine for the reduced translation spaces.
The hypotheses are precisely the carrier and (apartmentGaloisFixed D)-point uniqueness comparisons
in valuation descent. -/
def descentAffineMap : B.Apartment →ᵃ[ℝ] D.Apartment where
  toFun := descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar
  linear := descentTranslationMap hiT hE D B f hcar hinj
  map_vadd' w q := by
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      apply KPApartmentData.Apartment.ext
      exact descentPoint_val_mk_vadd hiT hE D B f hcar hinj v w

@[simp]
theorem descentAffineMap_apply (w : B.Apartment) :
    descentAffineMap hiT hE D B f hcar hinj w = descentPoint B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w := rfl

theorem descentAffineMap_injective :
    Function.Injective (descentAffineMap hiT hE D B f hcar hinj) :=
  descentPoint_injective B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar

/-- The affine apartment map has fixed image for the coefficient action. -/
theorem descentAffineMap_fixed (w : B.Apartment) (σ : (inertiaFixedField F) ≃ₐ[F] (inertiaFixedField F)) :
    RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ
        (descentAffineMap hiT hE D B f hcar hinj w).val =
      (descentAffineMap hiT hE D B f hcar hinj w).val :=
  descentPoint_fixed B (apartmentGaloisFixed D) (apartmentRestriction hiT hE D B f) hcar w σ

end Langlands.Geometry.Building.UnramifiedBuildingDescent
