/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.PurityFiniteSetting.FrameKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame

/-! # The finite class of an étale frame

We define the class `finiteFrameClass` of a scheme-theoretic étale frame in a fixed finite
purity setting, as the ordered supported cup product of the support boundaries of the
pulled-back affine-line coordinate Kummer classes.

## Implementation details

The coordinate Kummer class over `Spec k` (with its standing hypothesis `e ∣ n`) is pulled
back along the unit-defined map to `G_m`. The empty product is the unit and the singleton is
its own boundary. The common zero support is identified with `Z ×_V U`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Direct image along an isomorphism of schemes is an equivalence, with inverse the direct
image along the inverse isomorphism. -/
def frameLowerStarEquivalence (A : Type*) [Category.{u + 1} A] {D D' : Scheme.{u}}
    (e : D ≅ D') : Sheaf (Scheme.ProEt.topology D) A ≌ Sheaf (Scheme.ProEt.topology D') A :=
  CategoryTheory.Equivalence.mk (lowerStar A e.hom) (lowerStar A e.inv)
    ((lowerStarId A D).symm ≪≫ eqToIso (by rw [e.hom_inv_id]) ≪≫
      (lowerStarComp A e.hom e.inv).symm)
    (lowerStarComp A e.inv e.hom ≪≫ eqToIso (by rw [e.inv_hom_id]) ≪≫ lowerStarId A D')

/-- Transport the closed constant coefficient along an isomorphism of closed subschemes
over the ambient scheme: direct image along an isomorphism is the inverse image along its
inverse, which preserves the constant coefficient. -/
def finiteFrameClosedCoefficientIso (P : PurityFiniteSetting.{u}) {D D' X : Scheme.{u}}
    (c : D ⟶ X) (g : D' ⟶ X) (e : D ≅ D') (w : e.hom ≫ g = c) :
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).obj (P.constant D) ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) g).obj (P.constant D') := by
  subst w
  exact (lowerStarComp (ModuleCat.{u + 1} P.Coefficient) e.hom g).symm.app (P.constant D) ≪≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) g).mapIso
      (((frameLowerStarEquivalence (ModuleCat.{u + 1} P.Coefficient) e).toAdjunction.leftAdjointUniq
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) e.inv)).app
          (P.constant D) ≪≫ P.frameConstantPullback e.inv)

/-- The supported unit for the zero ideal. Its closed immersion is an isomorphism:
the inverse is the universal lift of the identity through the empty zero locus.
Pushforward composition, the identity comparison, and the constant-unit comparison
then give precisely 1 in H^0(X,A_X), including for an empty scheme. -/
def finiteFrameEmptyClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (f : Fin 0 → Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameCoefficientTwist h X 0)) 0 := by
  let c := X.zeroLocusSubschemeι (Set.range f)
  let r := Scheme.Hom.liftZeroLocusSubscheme (𝟙 X) (s := Set.range f) (fun t ht ↦ by
    obtain ⟨a, _⟩ := ht
    exact Fin.elim0 a)
  have hr : r ≫ c = 𝟙 X :=
    Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
  letI : IsIso c := ⟨⟨r, by
    apply (cancel_mono c).mp
    simp only [Category.assoc, hr, Category.comp_id, Category.id_comp], hr⟩⟩
  let e : (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) ≅
      P.frameCoefficientTwist h X 0 := (cupConstantIso P X).symm
  exact (cupSingle P X).map
    ((P.finiteFrameClosedCoefficientIso c (𝟙 X) (asIso c) (Category.comp_id c)).hom ≫
      (lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X) ≫
      (cupConstantIso P X).hom ≫ e.hom) ≫
    (shiftFunctorZero (CupDerivedCategory P X) ℤ).inv.app _

/-- The zero locus of a family of global sections is the intersection of the zero locus
of its prefix with the zero locus of its last member. -/
def finiteFrameZeroLocusIso {X : Scheme.{u}} (n : ℕ) (f : Fin (n + 1) → Γ(X, ⊤)) :
    X.zeroLocusSubscheme (Set.range f) ≅
      pullback (X.zeroLocusSubschemeι (Set.range fun k : Fin n ↦ f k.castSucc))
        (X.zeroLocusSubschemeι {f (Fin.last n)}) where
  hom := pullback.lift
    ((X.zeroLocusSubschemeι (Set.range f)).liftZeroLocusSubscheme (by
      rintro _ ⟨k, rfl⟩
      exact Scheme.zeroLocusSubschemeι_appTop ⟨k.castSucc, rfl⟩))
    ((X.zeroLocusSubschemeι (Set.range f)).liftZeroLocusSubscheme (by
      rintro t rfl
      exact Scheme.zeroLocusSubschemeι_appTop ⟨Fin.last n, rfl⟩))
    (by simp)
  inv := (pullback.fst _ _ ≫ X.zeroLocusSubschemeι _).liftZeroLocusSubscheme (by
    rintro _ ⟨k, rfl⟩
    induction k using Fin.lastCases with
    | last =>
      rw [pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _), map_zero]
    | cast k =>
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Scheme.zeroLocusSubschemeι_appTop (s := Set.range fun k : Fin n ↦ f k.castSucc) ⟨k, rfl⟩,
        map_zero])
  hom_inv_id := by
    rw [← cancel_mono (X.zeroLocusSubschemeι _)]
    simp only [Category.assoc, Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι,
      pullback.lift_fst_assoc, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [← cancel_mono (X.zeroLocusSubschemeι _)]
      simp only [Category.assoc, pullback.lift_fst_assoc,
        Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι, Category.id_comp]
    · rw [← cancel_mono (X.zeroLocusSubschemeι _)]
      simp only [Category.assoc, pullback.lift_snd_assoc,
        Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι, Category.id_comp,
        pullback.condition]

/-- Append the boundary of the last section to the supported product of the prefix: the
supported cup product, followed by the identification of the common zero support and the
multiplication of the nonnegative finite twists. -/
def finiteFrameCupNext (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (n : ℕ) (f : Fin (n + 1) → Γ(X, ⊤))
    (α : cupSupportedHom P (X.zeroLocusSubschemeι (Set.range fun k : Fin n ↦ f k.castSucc))
      ((cupSingle P X).obj (P.frameCoefficientTwist h X n)) (2 * (n : ℤ))) :
    cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
      ((cupSingle P X).obj (P.frameCoefficientTwist h X (n + 1))) (2 * ((n + 1 : ℕ) : ℤ)) :=
  letI : X.Over (Spec (.of P.field.k)) := ⟨a⟩
  let i := X.zeroLocusSubschemeι (Set.range fun k : Fin n ↦ f k.castSucc)
  let j := X.zeroLocusSubschemeι {f (Fin.last n)}
  let F : CupPlus P X := ⟨(cupSingle P X).obj (P.frameCoefficientTwist h X n), ⟨0, by
    dsimp only [cupSingle]
    infer_instance⟩⟩
  let G : CupPlus P X := ⟨(cupSingle P X).obj (P.frameCoefficientTwist h X 1), ⟨0, by
    dsimp only [cupSingle]
    infer_instance⟩⟩
  (cupSingle P X).map (P.finiteFrameClosedCoefficientIso (X.zeroLocusSubschemeι (Set.range f))
      (cupIntersection i j) (finiteFrameZeroLocusIso n f)
      (by
        simp only [finiteFrameZeroLocusIso, i, j, pullback.lift_fst_assoc,
          Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι])).hom ≫
    supportedCup P i j F G (2 * (n : ℤ)) 2 α (P.finiteFrameBoundary h X a (f (Fin.last n))) ≫
    (shiftFunctor (CupDerivedCategory P X) (2 * (n : ℤ) + 2)).map
      (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X) (hDM := cupMonoidal P X)
        (P.frameCoefficientTensorNext h X n).hom) ≫
    eqToHom (by
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rfl)

/-- Ordered supported product with explicit edge cases. For c=0 it is the unit;
for c=1 it is precisely the single principal boundary, after the tautological support
identification. For c>=2 append the last factor to the product of the prefix. -/
def finiteFrameBoundaryProduct (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → (f : Fin c → Γ(X, ⊤)) →
      cupSupportedHom P (X.zeroLocusSubschemeι (Set.range f))
        ((cupSingle P X).obj (P.frameCoefficientTwist h X c)) (2 * (c : ℤ))
  | 0, f => P.finiteFrameEmptyClass h X f
  | 1, f => by
    have hf : Set.range f = {f 0} := by
      ext t
      constructor
      · rintro ⟨k, rfl⟩
        exact congrArg f (Fin.eq_zero k)
      · intro ht
        exact ⟨0, (Set.mem_singleton_iff.mp ht).symm⟩
    rw [hf]
    simpa only [Nat.cast_one, mul_one] using P.finiteFrameBoundary h X a (f 0)
  | c + 2, f => P.finiteFrameCupNext h X a (c + 1) f
      (P.finiteFrameBoundaryProduct h X a (c + 1) (fun k ↦ f k.castSucc))

/-- The class of an étale frame of pure codimension `c` (expressed by the stalk Krull-dimension
condition) in the fixed finite purity setting: the product of the support boundaries of the
affine-line coordinate Kummer classes, a class supported on the common zero locus, of degree
`2c` and coefficient twist of order `c`. -/
def finiteFrameClass (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    (n : ℕ) [SmoothOfRelativeDimension n v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (_hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (F.U.zeroLocusSubschemeι (Set.range F.f))
      ((cupSingle P F.U).obj (P.frameCoefficientTwist h F.U c)) (2 * (c : ℤ)) :=
  P.finiteFrameBoundaryProduct h F.U (F.e ≫ v ≫ b) c F.f

end WeilConjectures.PurityFiniteSetting
