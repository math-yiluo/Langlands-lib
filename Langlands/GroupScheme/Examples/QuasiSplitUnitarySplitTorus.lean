import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankStatement
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The diagonal matrix associated to a family of units. -/
def familyDiagonal (A : Type*) [CommRing A] : (n → Aˣ) →* GL n A :=
  (Units.map (Matrix.diagonalRingHom n A).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

@[simp] theorem familyDiagonal_apply {A : Type*} [CommRing A] (t : n → Aˣ) (i j : n) :
    familyDiagonal A t i j = if i = j then (t i : A) else 0 := rfl

variable (e : n → ℤ) (he : Function.Injective e)

/-- For distinct weights the block Levi group is the group of diagonal units. -/
def diagonalLeviEquiv (A : Type*) [CommRing A] :
    (n → Aˣ) ≃* blockLeviSubgroup A e :=
  MulEquiv.ofBijective
    ({
      toFun := fun t => ⟨familyDiagonal A t, fun i j hij => by
        rw [familyDiagonal_apply, ite_eq_right (fun h => hij (congrArg e h))]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) } :
      (n → Aˣ) →* blockLeviSubgroup A e)
    ⟨by
      intro t s h
      funext i
      apply Units.ext
      have h' := congrArg (fun g : blockLeviSubgroup A e => g.val i i) h
      change familyDiagonal A t i i = familyDiagonal A s i i at h'
      simpa only [familyDiagonal_apply, ite_true] using h',
    by
      intro g
      have hd : Matrix.diagonal (fun i => g.val i i) = (g.val : Matrix n n A) := by
        ext i j
        by_cases hij : i = j
        · subst j; simp
        · rw [Matrix.diagonal_apply_ne _ hij]
          exact (g.property i j (fun h => hij (he h))).symm
      have hu : IsUnit (fun i => g.val i i) :=
        Matrix.isUnit_diagonal.mp (hd.symm ▸ g.val.isUnit)
      obtain ⟨t, ht⟩ := hu
      refine ⟨MulEquiv.piUnits t, ?_⟩
      apply Subtype.ext
      apply Units.ext
      change Matrix.diagonal (fun i => ((MulEquiv.piUnits t i : Aˣ) : A)) = _
      change Matrix.diagonal (t : n → A) = _
      rw [ht, hd]⟩

@[simp] theorem diagonalLeviEquiv_symm_val {A : Type*} [CommRing A]
    (g : blockLeviSubgroup A e) (i : n) :
    ((diagonalLeviEquiv e he A).symm g i : A) = g.val i i := by
  have h := congrArg (fun g : blockLeviSubgroup A e => g.val i i)
    ((diagonalLeviEquiv e he A).apply_symm_apply g)
  change familyDiagonal A ((diagonalLeviEquiv e he A).symm g) i i = g.val i i at h
  simpa only [familyDiagonal_apply, ite_true] using h

/-- Reindexing a family of units along the universe lift. -/
def liftUnitsEquiv (A : Type*) [CommRing A] : (ULift.{u} n → Aˣ) ≃* (n → Aˣ) where
  toFun t i := t ⟨i⟩
  invFun t i := t i.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (R : CommRingCat.{u})

/-- The points of the diagonal block Levi scheme are families of units. -/
def diagonalLeviPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (blockLeviScheme n R e).X) ≃* (ULift.{u} n → Γ(T.left, ⊤)ˣ) :=
  (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_blockLevi (n := n) (R := R) e)) T).trans
      ((diagonalLeviEquiv e he _).symm.trans (liftUnitsEquiv _).symm)

theorem diagonalLeviPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (g : T ⟶ (blockLeviScheme n R e).X) :
    diagonalLeviPointsEquiv e he R T' (a ≫ g) =
      splitTorus.unitsRestrict (ULift.{u} n) a (diagonalLeviPointsEquiv e he R T g) := by
  funext i
  apply Units.ext
  change
    (((diagonalLeviEquiv e he _).symm
      (Corepresented.pointsEquiv _ _ T' (a ≫ g))) i.down).val =
    a.left.appTop.hom
      (((diagonalLeviEquiv e he _).symm
        (Corepresented.pointsEquiv _ _ T g)) i.down).val
  erw [Corepresented.pointsEquiv_naturality, diagonalLeviEquiv_symm_val,
    diagonalLeviEquiv_symm_val]
  rfl

/-- The split torus is the diagonal block Levi subgroup for an injective weight vector. -/
def diagonalTorusIso : splitTorus (Spec R) (ULift.{u} n) ≅ blockLeviScheme n R e :=
  isoOfPointModels (fun T : Over (Spec R) => ULift.{u} n → Γ(T.left, ⊤)ˣ)
    (fun a => splitTorus.unitsRestrict (ULift.{u} n) a)
    (splitTorus.pointsEquiv (ULift.{u} n)) (diagonalLeviPointsEquiv e he R)
    (fun a x => splitTorus.pointsEquiv_naturality _ a x)
    (fun a x => diagonalLeviPointsEquiv_naturality e he R a x)

end GeneralLinear

namespace QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)
  (hc : c ≠ AlgEquiv.refl)

/-- The base change to the quadratic field contains a closed split torus with two factors. -/
theorem exists_rankTwo_splitTorus (hc : c ≠ AlgEquiv.refl) :
    ∃ (I : Type u) (_ : Finite I), Nat.card I = 2 ∧
      ∃ i : splitTorus (Spec (CommRingCat.of E)) I ⟶ baseChangeGroupScheme b c,
        IsClosedSubgroup i := by
  have he : Function.Injective (weights 1) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [weights]
  let e := GeneralLinear.diagonalTorusIso (weights 1) he (CommRingCat.of E)
  let i := e.hom ≫ GeneralLinear.blockLeviHom (Fin 2) (CommRingCat.of E) (weights 1) ≫
    (splittingIso b c hc).inv
  refine ⟨ULift.{u} (Fin 2), inferInstance, by simp, i, ?_⟩
  have h₁ : IsClosedImmersion e.hom.hom.hom.left := IsClosedSubgroup.of_iso e
  have h₂ : IsClosedImmersion
      (GeneralLinear.blockLeviHom (Fin 2) (CommRingCat.of E) (weights 1)).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockLeviHom _ _ _
  have h₃ : IsClosedImmersion (splittingIso b c hc).inv.hom.hom.left :=
    IsClosedSubgroup.of_iso (splittingIso b c hc).symm
  change IsClosedImmersion (e.hom.hom.hom.left ≫
    (GeneralLinear.blockLeviHom (Fin 2) (CommRingCat.of E) (weights 1)).hom.hom.left ≫
    (splittingIso b c hc).inv.hom.hom.left)
  infer_instance

end QuasiSplitUnitary
end Langlands.GroupScheme
