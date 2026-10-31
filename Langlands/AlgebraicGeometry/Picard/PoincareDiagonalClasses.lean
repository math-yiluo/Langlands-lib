import Langlands.AlgebraicGeometry.Picard.PoincarePointClasses

/-! # The Mumford map of a diagonal Poincaré pullback at a point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (IsoClasses isoClass pullbackHom)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The Poincaré pullback along a product of points of the dual is the tensor product of
the two Poincaré pullbacks. -/
lemma nonempty_relativePullback_poincareFamily_mul_iso {T : Over S} (u u' : T ⟶ (DA).X) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) (u * u')).obj (poincareFamily A hA) ≅
      RigidifiedLineBundle.tensor preservation
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) u).obj (poincareFamily A hA))
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) u').obj (poincareFamily A hA))) := by
  let _ := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  have h := congrArg Subtype.val ((dualAbelianSchemePointMulEquiv A hA geometryA preservation
    MA evaluationA stability composition unitCoherence associativity comparison symmetry
    T).map_mul u u')
  exact (RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ _ _ _).mp h

/-- Poincaré classes are multiplicative in the dual variable. -/
lemma familyPointClass_poincareFamily_mul_left {Z : Over S} (u u' : Z ⟶ (DA).X)
    (x : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) (u * u') x =
      familyPointClass preservation A (poincareFamily A hA) u x *
        familyPointClass preservation A (poincareFamily A hA) u' x := by
  obtain ⟨e⟩ := nonempty_relativePullback_poincareFamily_mul_iso preservation A hA geometryA
    MA evaluationA stability composition unitCoherence associativity comparison symmetry u u'
  have h1 := familyPointClass_relativePullback preservation A (poincareFamily A hA) (u * u')
    (𝟙 Z) x
  have h2 := familyPointClass_relativePullback preservation A (poincareFamily A hA) u (𝟙 Z) x
  have h3 := familyPointClass_relativePullback preservation A (poincareFamily A hA) u' (𝟙 Z) x
  erw [Category.id_comp] at h1 h2 h3
  rw [← h1, ← h2, ← h3, ← familyPointClass_tensor]
  exact familyPointClass_eq_of_iso preservation A e (𝟙 Z) x

include stability in
/-- Poincaré classes are multiplicative in the variable on `A` (theorem of the square). -/
lemma familyPointClass_poincareFamily_mul_right {Z : Over S} (z : Z ⟶ dualScheme A hA)
    (x y : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) z (x * y) =
      familyPointClass preservation A (poincareFamily A hA) z x *
        familyPointClass preservation A (poincareFamily A hA) z y := by
  obtain ⟨e⟩ := nonempty_pullback_pairOver_mul_iso preservation
    picardZeroLineBundleClassification stability
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions A hA (poincareFamily A hA)
    (poincareFamily_universal A hA).1 z x y
  exact (LineBundle.isoClass_eq_of_iso e).trans (LineBundle.isoClass_tensor preservation _ _)

/-- The class of `x^* (1, f)^* P` is the Poincaré class at `(x f, x)`. -/
lemma isoClass_pullback_poincareDiagonalBundle (f : A.X ⟶ dualScheme A hA) {Z : Over S}
    (x : Z ⟶ A.X) :
    isoClass preservation ((LineBundle.pullback x.left).obj (poincareDiagonalBundle A hA f)) =
      familyPointClass preservation A (poincareFamily A hA) (x ≫ f) x := by
  rw [poincareDiagonalBundle,
    isoClass_pullback_pullback preservation _ _ (comp_relativeDiagonal A x)]
  exact familyPointClass_relativePullback preservation A (poincareFamily A hA) f x x

/-- A bundle from the base pulled back to `T ×_S A` through a point is trivial when `T` has
one point. -/
lemma isoClass_pullback_baseBundle_eq_one {T : Over S} [Unique T.left]
    (x : relativeOver A T ⟶ A.X) (N : LineBundle S) :
    isoClass preservation ((LineBundle.pullback x.left).obj
      ((LineBundle.pullback A.X.hom).obj N)) = 1 := by
  rw [isoClass_pullback_pullback preservation x.left A.X.hom (Over.w x),
    ← LineBundle.pullbackHom_isoClass]
  exact LineBundle.pullbackHom_eq_one_of_factor preservation (relativeFst A T).left T.hom rfl _

/-- A class pulled back to `T ×_S A` along the first projection is trivial when `T` has one
point. -/
lemma pullbackHom_relativeFst_eq_one {T : Over S} [Unique T.left] {W : Scheme.{u}}
    (k : T.left ⟶ W) {h : (relativeOver A T).left ⟶ W} (w : (relativeFst A T).left ≫ k = h)
    (q : IsoClasses preservation W) : pullbackHom preservation h q = 1 :=
  LineBundle.pullbackHom_eq_one_of_factor preservation (relativeFst A T).left k w q

include stability in
/-- Two points of the dual with isomorphic Poincaré pullbacks are equal. -/
lemma eq_of_nonempty_relativePullback_poincareFamily_iso {T : Over S}
    (u v : T ⟶ dualScheme A hA)
    (h : Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) u).obj (poincareFamily A hA) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) v).obj (poincareFamily A hA))) : u = v := by
  apply dualPointClass_injective stability A hA T
  apply Subtype.ext
  exact ((RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ _ _ u).mpr h).trans
    ((RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ _ _ v).mpr ⟨Iso.refl _⟩).symm

section Diagonal

variable (lam0 : A.X ⟶ (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry).X)
  [IsMonHom lam0]
variable (B : LineBundle S)
variable (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj
  (poincareDiagonalBundle A hA lam0).obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
  (unitSection_comp A) (poincareDiagonalBundle A hA lam0) B evaluationB).obj.carrier M.obj ≅
    structureSheaf A.X.left)
variable (square : MumfordBundlePicardZeroStatement.{u})

/-- At a point `t` of `A` over a one-point scheme `T` where the Poincaré slices are
symmetric, the Poincaré class of the Mumford map of `(1, λ)^* P` at `(t, a)` is the square of
the class at `(t λ, a)`. -/
lemma familyPointClass_mumfordSchemeMap_poincareDiagonal {T : Over S} [Unique T.left]
    (t : T ⟶ A.X) (hsym : PoincareSliceSymmetric A hA lam0 t) :
    familyPointClass preservation A (poincareFamily A hA)
        (relativeFst A T ≫ t ≫ mumfordSchemeMapOfLineBundle preservation A
          (poincareDiagonalBundle A hA lam0) B evaluationB M evaluation square hA)
        (relativeSnd A T) =
      familyPointClass preservation A (poincareFamily A hA) (relativeFst A T ≫ t ≫ lam0)
          (relativeSnd A T) *
        familyPointClass preservation A (poincareFamily A hA) (relativeFst A T ≫ t ≫ lam0)
          (relativeSnd A T) := by
  -- the Mumford class at `(τ, a)`, with `τ = t ∘ pr₁` and `a = pr₂`
  have e0 := familyPointClass_relativePullback preservation A (poincareFamily A hA)
    (mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) B evaluationB
      M evaluation square hA) (relativeFst A T ≫ t) (relativeSnd A T)
  rw [Category.assoc] at e0
  rw [← e0, familyPointClass_eq_of_iso preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso preservation A
        (poincareDiagonalBundle A hA lam0) B evaluationB M evaluation square hA),
    familyPointClass_mumfordFamily, isoClass_pullback_tensor,
    isoClass_pullback_baseBundle_eq_one preservation A _ B, mul_one]
  set τ := relativeFst A T ≫ t with hτ
  set a := relativeSnd A T with ha
  -- the factor `τ^* M` comes from `T`
  have hM : isoClass preservation ((LineBundle.pullback τ.left).obj M) = 1 :=
    pullbackHom_relativeFst_eq_one preservation A t.left (Over.comp_left _ _ _ _ _).symm
      (isoClass preservation M)
  -- the diagonal factor at `τ * a`
  have hdiag : isoClass preservation
      ((LineBundle.pullback (τ * a).left).obj (poincareDiagonalBundle A hA lam0)) =
        familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) τ *
          familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) a *
        (familyPointClass preservation A (poincareFamily A hA) (a ≫ lam0) τ *
          familyPointClass preservation A (poincareFamily A hA) (a ≫ lam0) a) := by
    have h2 : (τ * a) ≫ lam0 = (τ ≫ lam0) * (a ≫ lam0) := MonObj.mul_comp _ _ _
    rw [isoClass_pullback_poincareDiagonalBundle preservation A hA lam0 (τ * a)]
    refine (familyPointClass_congr preservation A (poincareFamily A hA) h2 rfl).trans ?_
    rw [familyPointClass_poincareFamily_mul_left preservation A hA geometryA MA
        evaluationA stability composition unitCoherence associativity comparison symmetry]
    exact congrArg₂ (· * ·)
      (familyPointClass_poincareFamily_mul_right preservation A hA stability (τ ≫ lam0) τ a)
      (familyPointClass_poincareFamily_mul_right preservation A hA stability (a ≫ lam0) τ a)
  -- the class at `(τ λ, τ)` comes from `T`
  have hττ : familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) τ = 1 := by
    have h := familyPointClass_comp preservation A (poincareFamily A hA) (relativeFst A T)
      (t ≫ lam0) t
    rw [LineBundle.isoClasses_eq_one_of_unique preservation
      (familyPointClass preservation A (poincareFamily A hA) (t ≫ lam0) t), map_one] at h
    exact (familyPointClass_congr preservation A (poincareFamily A hA)
      (Category.assoc _ _ _) rfl).trans h
  -- symmetry of the slices through `t`
  have haτ : familyPointClass preservation A (poincareFamily A hA) (a ≫ lam0) τ =
      familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) a := by
    have h : familyPointClass preservation A (poincareFamily A hA)
          (relativeFst A T ≫ t ≫ lam0) (relativeSnd A T) =
        familyPointClass preservation A (poincareFamily A hA) (relativeSnd A T ≫ lam0)
          (relativeFst A T ≫ t) :=
      LineBundle.isoClass_eq_iff.mpr hsym
    exact h.symm.trans (familyPointClass_congr preservation A (poincareFamily A hA)
      (Category.assoc _ _ _).symm rfl)
  -- the diagonal class at `a` cancels against `a^* M`
  have haa : familyPointClass preservation A (poincareFamily A hA) (a ≫ lam0) a *
      isoClass preservation ((LineBundle.pullback a.left).obj M) = 1 := by
    have ev : LineBundle.tensor preservation (LineBundle.tensor preservation
        (poincareDiagonalBundle A hA lam0) ((LineBundle.pullback A.X.hom).obj B)) M ≅
        LineBundle.trivial A.X.left := ObjectProperty.isoMk _ evaluation
    have h := congrArg (pullbackHom preservation a.left) (LineBundle.isoClass_eq_of_iso ev)
    rw [LineBundle.isoClass_tensor, map_mul, LineBundle.isoClass_tensor, map_mul,
      LineBundle.pullbackHom_isoClass, LineBundle.pullbackHom_isoClass,
      LineBundle.pullbackHom_isoClass,
      isoClass_pullback_poincareDiagonalBundle preservation A hA lam0 a,
      isoClass_pullback_baseBundle_eq_one preservation A a B, mul_one,
      LineBundle.isoClass_trivial, map_one] at h
    exact h
  have hassoc : familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) a =
      familyPointClass preservation A (poincareFamily A hA) (relativeFst A T ≫ t ≫ lam0)
        (relativeSnd A T) :=
    familyPointClass_congr preservation A (poincareFamily A hA) (Category.assoc _ _ _) rfl
  rw [hdiag, hM, hττ, haτ, ← hassoc]
  calc _ = familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) a *
        familyPointClass preservation A (poincareFamily A hA) (τ ≫ lam0) a *
        (familyPointClass preservation A (poincareFamily A hA) (a ≫ lam0) a *
          isoClass preservation ((LineBundle.pullback a.left).obj M)) := by
          simp only [one_mul, mul_one]; ac_rfl
    _ = _ := by rw [haa, mul_one]

/-- At a point `t` of `A` over a one-point scheme where the Poincaré slices are symmetric,
the Mumford map of `(1, λ)^* P` sends `t` to `(t λ)^2`. -/
lemma comp_mumfordSchemeMap_poincareDiagonal {T : Over S} [Unique T.left]
    (t : T ⟶ A.X) (hsym : PoincareSliceSymmetric A hA lam0 t) :
    t ≫ mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) B
        evaluationB M evaluation square hA =
      ((t ≫ lam0) * (t ≫ lam0) : T ⟶ (DA).X) := by
  apply eq_of_nonempty_relativePullback_poincareFamily_iso A hA stability
  obtain ⟨e1⟩ := nonempty_relativePullback_poincareFamily_mul_iso preservation A hA geometryA
    MA evaluationA stability composition unitCoherence associativity comparison symmetry
    (t ≫ lam0) (t ≫ lam0)
  have h : isoClass preservation ((RigidifiedLineBundle.forget _).obj
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (t ≫ mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) B
          evaluationB M evaluation square hA)).obj (poincareFamily A hA))) =
      isoClass preservation ((RigidifiedLineBundle.forget _).obj
        (RigidifiedLineBundle.tensor preservation
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
            (t ≫ lam0)).obj (poincareFamily A hA))
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
            (t ≫ lam0)).obj (poincareFamily A hA)))) := by
    rw [isoClass_forget_eq_familyPointClass, isoClass_forget_eq_familyPointClass,
      familyPointClass_tensor, familyPointClass_relativePullback]
    have hr := familyPointClass_relativePullback preservation A (poincareFamily A hA)
      (t ≫ lam0) (relativeFst A T) (relativeSnd A T)
    exact (familyPointClass_mumfordSchemeMap_poincareDiagonal preservation A hA geometryA MA
      evaluationA stability composition unitCoherence associativity comparison symmetry lam0 B
      evaluationB M evaluation square t hsym).trans (congrArg₂ (· * ·) hr.symm hr.symm)
  obtain ⟨e'⟩ := LineBundle.isoClass_eq_iff.mp h
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
    ((relativeProjection A.X.hom).app T)
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T) e'
  exact ⟨e2 ≪≫ e1.symm⟩

end Diagonal

end Langlands.AbelianScheme
