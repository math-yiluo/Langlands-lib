import Langlands.GroupScheme.Torus.DiagonalizableCharacterStatement
import Langlands.GroupScheme.Torus.Grouplike
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Characters and homomorphisms of diagonalizable groups: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace DiagonalizableCharacter

section Evaluation

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- Evaluation of the points of `D(Λ)` at `m`, with values in the points of `𝔾_m`. -/
def evalPoints (m : Λ) (U : Over (Spec R)) :
    (U ⟶ (Diagonalizable.groupScheme R Λ).X) →* (U ⟶ (Gm (Spec R)).X) where
  toFun x := (Gm.pointsEquiv (Spec R) U).symm
    (Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd m))
  map_one' := by simp
  map_mul' x y := by simp

theorem evalPoints_naturality (m : Λ) {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    evalPoints R Λ m U' (a ≫ x) = a ≫ evalPoints R Λ m U x := by
  apply (Gm.pointsEquiv (Spec R) U').injective
  rw [Gm.pointsEquiv_naturality]
  change Gm.pointsEquiv (Spec R) U' ((Gm.pointsEquiv (Spec R) U').symm
      (Diagonalizable.characterPointsEquiv R Λ U' (a ≫ x) (.ofAdd m))) =
    Units.map a.left.appTop.hom.toMonoidHom (Gm.pointsEquiv (Spec R) U
      ((Gm.pointsEquiv (Spec R) U).symm
        (Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd m))))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    Diagonalizable.characterPointsEquiv_naturality]

/-- The character `t ↦ t(m)` of `D(Λ)`. -/
def evalCharacter (m : Λ) : characterLattice (Diagonalizable.groupScheme R Λ) :=
  Additive.ofMul (homOfPoints (evalPoints R Λ m) (evalPoints_naturality R Λ m))

theorem evalCharacter_apply (m : Λ) (U : Over (Spec R))
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom (evalCharacter R Λ m)).hom.hom) =
      Diagonalizable.characterPointsEquiv R Λ U x (Multiplicative.ofAdd m) := by
  change Gm.pointsEquiv _ U
    (x ≫ (homOfPoints (evalPoints R Λ m) (evalPoints_naturality R Λ m)).hom.hom) = _
  rw [comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

end Evaluation

section Universal

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- The comparison `Γ(D(Λ)) ≅ R[Λ]` of coordinate algebras. -/
abbrev sectionsIso :
    ((algΓ R).obj (Diagonalizable.groupScheme R Λ).X).unop ≅ Diagonalizable.algebra R Λ :=
  Corepresented.affineSectionsIso (Diagonalizable.algebra R Λ)

/-- A point `x` of `D(Λ)` over `U` is classified by `R[Λ] ≅ Γ(D(Λ)) → Γ(U)`. -/
theorem lift_characterPointsEquiv (U : Over (Spec R))
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    Diagonalizable.lift R Λ (Diagonalizable.characterPointsEquiv R Λ U x) =
      (sectionsIso R Λ).inv ≫ ((algΓ R).map x).unop := by
  have h₁ := Corepresented.pointsEquiv_eq_affinePointsEquiv (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) (Diagonalizable.algebra R Λ)
    ((algSpec R).map (𝟙 (Diagonalizable.algebra R Λ)).op)
  rw [Corepresented.affinePointsEquiv_map] at h₁
  have h₂ := Corepresented.pointsEquiv_naturality (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) x (𝟙 _)
  rw [Category.comp_id] at h₂
  rw [op_id, CategoryTheory.Functor.map_id] at h₁
  have h₃ : Corepresented.pointsEquiv (Diagonalizable.functor R Λ)
      (Diagonalizable.grpCorepresentation R Λ) U x =
        (Diagonalizable.corepresentation R Λ).homEquiv
          ((sectionsIso R Λ).inv ≫ ((algΓ R).map x).unop) := by
    refine h₂.trans ((congrArg (ConcreteCategory.hom
      ((Diagonalizable.functor R Λ).map ((algΓ R).map x).unop)) h₁).trans ?_)
    rw [(Diagonalizable.corepresentation R Λ).homEquiv_comp]
    refine congrArg _ ?_
    rw [← Category.id_comp (sectionsIso R Λ).inv,
      (Diagonalizable.corepresentation R Λ).homEquiv_comp]
    rfl
  exact (Equiv.symm_apply_eq _).2 h₃

/-- Changing the coefficients of a character along `g` composes its classifying map with `g`. -/
theorem lift_map {B C : CommAlgCat.{u} R} (s : Multiplicative Λ →* Bˣ) (g : B ⟶ C) :
    Diagonalizable.lift R Λ ((Units.map g.hom.toRingHom.toMonoidHom).comp s) =
      Diagonalizable.lift R Λ s ≫ g := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    change (Diagonalizable.lift R Λ _).hom (AddMonoidAlgebra.single γ 1) =
      g.hom ((Diagonalizable.lift R Λ s).hom (AddMonoidAlgebra.single γ 1))
    rw [Diagonalizable.lift_single, Diagonalizable.lift_single, one_smul, one_smul]
    rfl
  · exact Subsingleton.elim _ _

end Universal

/-- A natural family of homomorphisms from the points of `D(Λ)` to the global units. -/
structure NaturalUnits (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] where
  /-- The homomorphism on the points over each test scheme. -/
  app : ∀ U : Over (Spec R), (U ⟶ (Diagonalizable.groupScheme R Λ).X) →* (Γ(U.left, ⊤))ˣ
  /-- Naturality in the test scheme. -/
  naturality : ∀ {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X),
    app U' (a ≫ x) = Units.map a.left.appTop.hom.toMonoidHom (app U x)

namespace NaturalUnits

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ] (c : NaturalUnits R Λ)

/-- The value of `c` at the universal point, as an element of `R[Λ]`. -/
def value : AddMonoidAlgebra R Λ :=
  (sectionsIso R Λ).hom.hom
    (c.app (Diagonalizable.groupScheme R Λ).X (𝟙 _) :
      Γ((Diagonalizable.groupScheme R Λ).X.left, ⊤))

/-- **Value formula**: the value of `c` at a point `x` is the image of `c.value` under the
algebra map `R[Λ] → Γ(U)` classifying `x`. -/
theorem app_eq (U : Over (Spec R)) (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    (c.app U x : Γ(U.left, ⊤)) =
      (Diagonalizable.lift R Λ (B := ((algΓ R).obj U).unop)
        (Diagonalizable.characterPointsEquiv R Λ U x)).hom c.value := by
  rw [lift_characterPointsEquiv]
  have h := c.naturality x (𝟙 _)
  rw [Category.comp_id] at h
  rw [h]
  have e := ConcreteCategory.congr_hom (sectionsIso R Λ).hom_inv_id
    (c.app (Diagonalizable.groupScheme R Λ).X (𝟙 _) :
      Γ((Diagonalizable.groupScheme R Λ).X.left, ⊤))
  change x.left.appTop.hom (c.app (Diagonalizable.groupScheme R Λ).X (𝟙 _) :
      Γ((Diagonalizable.groupScheme R Λ).X.left, ⊤)) =
    ((algΓ R).map x).unop.hom ((sectionsIso R Λ).inv.hom ((sectionsIso R Λ).hom.hom
      (c.app (Diagonalizable.groupScheme R Λ).X (𝟙 _) :
        Γ((Diagonalizable.groupScheme R Λ).X.left, ⊤))))
  erw [e]
  rfl

/-- The affine test scheme `Spec B` over `Spec R`. -/
abbrev affine (B : CommAlgCat.{u} R) : Over (Spec R) := (algSpec R).obj (op B)

/-- The section comparison `B → Γ(Spec B)`. -/
abbrev toSections (B : CommAlgCat.{u} R) : B ⟶ ((algΓ R).obj (affine B)).unop :=
  (Corepresented.affineSectionsIso B).inv

/-- The point of `D(Λ)` over `Spec B` given by a character `Λ → Bˣ`. -/
def affinePoint (B : CommAlgCat.{u} R) (s : Multiplicative Λ →* Bˣ) :
    affine B ⟶ (Diagonalizable.groupScheme R Λ).X :=
  (Diagonalizable.characterPointsEquiv R Λ (affine B)).symm
    ((Units.map (toSections B).hom.toRingHom.toMonoidHom).comp s)

theorem affinePoint_mul (B : CommAlgCat.{u} R) (s s' : Multiplicative Λ →* Bˣ) :
    affinePoint B (s * s') = affinePoint B s * affinePoint B s' := by
  rw [affinePoint, affinePoint, affinePoint, MonoidHom.comp_mul, map_mul]

theorem affinePoint_one (B : CommAlgCat.{u} R) :
    affinePoint (Λ := Λ) B 1 = 1 := by
  rw [affinePoint, MonoidHom.comp_one, map_one]

theorem toSections_lift (B : CommAlgCat.{u} R) (s : Multiplicative Λ →* Bˣ) :
    (toSections B).hom ((Diagonalizable.lift R Λ s).hom c.value) =
      (c.app (affine B) (affinePoint B s) : Γ((affine B).left, ⊤)) := by
  rw [c.app_eq, affinePoint, MulEquiv.apply_symm_apply, lift_map]
  rfl

theorem toSections_injective (B : CommAlgCat.{u} R) :
    Function.Injective (toSections B).hom := by
  intro a b h
  have ea : (Corepresented.affineSectionsIso B).hom.hom ((toSections B).hom a) = a :=
    ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a
  have eb : (Corepresented.affineSectionsIso B).hom.hom ((toSections B).hom b) = b :=
    ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id b
  rw [← ea, ← eb, h]

/-- Evaluation of `c.value` at characters is multiplicative in the character. -/
theorem lift_mul (B : CommAlgCat.{u} R) (s s' : Multiplicative Λ →* Bˣ) :
    (Diagonalizable.lift R Λ (s * s')).hom c.value =
      (Diagonalizable.lift R Λ s).hom c.value * (Diagonalizable.lift R Λ s').hom c.value := by
  apply toSections_injective B
  rw [map_mul, c.toSections_lift, c.toSections_lift, c.toSections_lift, affinePoint_mul,
    map_mul, Units.val_mul]

theorem lift_one (B : CommAlgCat.{u} R) :
    (Diagonalizable.lift R Λ (1 : Multiplicative Λ →* Bˣ)).hom c.value = 1 := by
  apply toSections_injective B
  rw [map_one, c.toSections_lift, affinePoint_one, map_one, Units.val_one]

end NaturalUnits

section Grouplike

open CharacterAction

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- The base ring as an algebra over itself. -/
abbrev baseAlg (R : CommRingCat.{u}) : CommAlgCat.{u} R := CommAlgCat.of R R

/-- Over the base ring, evaluation of the group algebra is the classifying map `lift`. -/
theorem evaluate_eq_lift {D : CommAlgCat.{u} R} (x : baseAlg R ⟶ D)
    (t : Multiplicative Λ →* Dˣ) (q : AddMonoidAlgebra R Λ) :
    (evaluate (M := Λ) x t).hom q = (Diagonalizable.lift R Λ t).hom q := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add q q' hq hq' => rw [map_add, map_add, hq, hq']
  | single m r =>
    erw [evaluate_single]
    rw [Diagonalizable.lift_single, Algebra.smul_def]
    congr 1
    exact x.hom.commutes r

/-- The value of a natural family of units is grouplike. -/
theorem NaturalUnits.isGrouplike_value (c : NaturalUnits R Λ) :
    IsGrouplike (M := Λ) (B := baseAlg R) c.value := by
  refine ⟨?_, ?_⟩
  · have h := c.lift_mul (algebra (M := Λ) (algebra (M := Λ) (baseAlg R)))
      (universal (M := Λ) (algebra (M := Λ) (baseAlg R)))
      (mapCharacter (constant (M := Λ) (algebra (M := Λ) (baseAlg R)))
        (universal (M := Λ) (baseAlg R)))
    rw [← evaluate_eq_lift (constant (M := Λ) (baseAlg R) ≫
        constant (M := Λ) (algebra (M := Λ) (baseAlg R))),
      ← evaluate_eq_lift (constant (M := Λ) (baseAlg R) ≫
        constant (M := Λ) (algebra (M := Λ) (baseAlg R))),
      ← evaluate_eq_lift (constant (M := Λ) (baseAlg R) ≫
        constant (M := Λ) (algebra (M := Λ) (baseAlg R)))] at h
    have e₁ : evaluate (constant (M := Λ) (baseAlg R) ≫
        constant (M := Λ) (algebra (M := Λ) (baseAlg R)))
        (mapCharacter (constant (M := Λ) (algebra (M := Λ) (baseAlg R)))
          (universal (M := Λ) (baseAlg R))) =
          constant (M := Λ) (algebra (M := Λ) (baseAlg R)) := by
      rw [← evaluate_comp, evaluate_constant_universal, Category.id_comp]
    have e₂ : evaluate (constant (M := Λ) (baseAlg R) ≫
        constant (M := Λ) (algebra (M := Λ) (baseAlg R)))
        (universal (M := Λ) (algebra (M := Λ) (baseAlg R))) =
          coefficientMap (constant (M := Λ) (baseAlg R)) := rfl
    rw [e₁, e₂] at h
    rw [diagonalMap]
    exact h.trans (mul_comm _ _)
  · rw [evaluate_eq_lift]
    exact c.lift_one (baseAlg R)

/-- Over a field, a grouplike element of `k[Λ]` is a monomial `single m 1`. -/
theorem eq_single_of_isGrouplike {k : Type u} [Field k] {v : AddMonoidAlgebra k Λ}
    (hv : IsGrouplike (M := Λ) (B := baseAlg (CommRingCat.of k)) v) :
    ∃ m, v = AddMonoidAlgebra.single m 1 := by
  classical
  have h01 : ∀ p, v.coeff p = 0 ∨ v.coeff p = 1 := fun p =>
    (IsIdempotentElem.iff_eq_zero_or_one (G₀ := k)).1 (hv.isIdempotentElem_coeff p)
  have hsum : ∑ n ∈ v.coeff.support, v.coeff n = (1 : k) := hv.sum_coeff
  obtain ⟨m, hm⟩ : ∃ m, v.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun n _ => h n)] at hsum
    exact zero_ne_one hsum
  have hm1 : v.coeff m = 1 := (h01 m).resolve_left hm
  refine ⟨m, ?_⟩
  ext n
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact hm1
  · have h0 : v.coeff n * v.coeff m = 0 := hv.coeff_mul_coeff_of_ne h
    rwa [hm1, mul_one] at h0

end Grouplike

section Core

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- At the universal point, the classifying map is the inverse section comparison. -/
theorem lift_characterPointsEquiv_id :
    Diagonalizable.lift R Λ (Diagonalizable.characterPointsEquiv R Λ _
      (𝟙 (Diagonalizable.groupScheme R Λ).X)) = (sectionsIso R Λ).inv := by
  rw [lift_characterPointsEquiv, CategoryTheory.Functor.map_id, unop_id, Category.comp_id]

theorem characterPointsEquiv_val (U : Over (Spec R))
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) (m : Λ) :
    (Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd m) : Γ(U.left, ⊤)) =
      (Diagonalizable.lift R Λ (B := ((algΓ R).obj U).unop)
        (Diagonalizable.characterPointsEquiv R Λ U x)).hom (AddMonoidAlgebra.single m 1) := by
  rw [Diagonalizable.lift_single, one_smul]
  rfl

namespace NaturalUnits

variable (c : NaturalUnits R Λ)

/-- `c` is evaluation at `m` exactly when its universal value is the monomial `single m 1`. -/
theorem app_eq_iff (m : Λ) :
    (∀ (U : Over (Spec R)) (x : U ⟶ (Diagonalizable.groupScheme R Λ).X),
      c.app U x = Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd m)) ↔
        c.value = AddMonoidAlgebra.single m 1 := by
  constructor
  · intro h
    have e := congrArg Units.val (h _ (𝟙 _))
    rw [c.app_eq, characterPointsEquiv_val, lift_characterPointsEquiv_id] at e
    have ei := congrArg (sectionsIso R Λ).hom.hom e
    have h₁ := ConcreteCategory.congr_hom (sectionsIso R Λ).inv_hom_id c.value
    have h₂ := ConcreteCategory.congr_hom (sectionsIso R Λ).inv_hom_id
      (AddMonoidAlgebra.single m (1 : R))
    exact h₁.symm.trans (ei.trans h₂)
  · intro hm U x
    apply Units.ext
    rw [c.app_eq, hm, characterPointsEquiv_val]

/-- **Core lemma**: over a field, a natural family of units on the points of `D(Λ)` is
evaluation at exactly one `m ∈ Λ`. -/
theorem existsUnique {k : Type u} [Field k] (c : NaturalUnits (CommRingCat.of k) Λ) :
    ∃! m : Λ, ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
      c.app U x = Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ U x (.ofAdd m) := by
  obtain ⟨m, hm⟩ := eq_single_of_isGrouplike c.isGrouplike_value
  refine ⟨m, (c.app_eq_iff m).2 hm, fun m' hm' => ?_⟩
  have h := ((c.app_eq_iff m').1 hm').symm.trans hm
  exact AddMonoidAlgebra.single_left_injective (one_ne_zero (α := k)) h

end NaturalUnits

end Core

section Final

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

namespace NaturalUnits

/-- The values of a character of `D(Λ)`, as a natural family of units. -/
def ofCharacter (χ : characterLattice (Diagonalizable.groupScheme R Λ)) : NaturalUnits R Λ where
  app U :=
    { toFun := fun x => Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ).hom.hom)
      map_one' := by
        change Gm.pointsEquiv _ U (1 ≫ (CommGroupScheme.groupHom χ).hom.hom) = 1
        rw [MonObj.one_comp, map_one]
      map_mul' := fun x y => by
        change Gm.pointsEquiv _ U ((x * y) ≫ (CommGroupScheme.groupHom χ).hom.hom) =
          Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ).hom.hom) *
            Gm.pointsEquiv _ U (y ≫ (CommGroupScheme.groupHom χ).hom.hom)
        rw [MonObj.mul_comp, map_mul] }
  naturality a x := by
    change Gm.pointsEquiv _ _ ((a ≫ x) ≫ (CommGroupScheme.groupHom χ).hom.hom) =
      Units.map a.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv _ _ (x ≫ (CommGroupScheme.groupHom χ).hom.hom))
    rw [Category.assoc, Gm.pointsEquiv_naturality]

/-- The `m'`-th coordinate of a homomorphism `f : D(Λ) → D(Λ')`, as a natural family of
units on the points of `D(Λ)`. -/
def ofHom {Λ' : Type u} [AddCommGroup Λ']
    (f : (Diagonalizable.groupScheme R Λ).toGrp ⟶ (Diagonalizable.groupScheme R Λ').toGrp)
    (m' : Λ') : NaturalUnits R Λ where
  app U :=
    { toFun := fun x => Diagonalizable.characterPointsEquiv R Λ' U (x ≫ f.hom.hom) (.ofAdd m')
      map_one' := by
        change Diagonalizable.characterPointsEquiv R Λ' U (1 ≫ f.hom.hom) (.ofAdd m') = 1
        rw [MonObj.one_comp, map_one, MonoidHom.one_apply]
      map_mul' := fun x y => by
        change Diagonalizable.characterPointsEquiv R Λ' U ((x * y) ≫ f.hom.hom) (.ofAdd m') =
          Diagonalizable.characterPointsEquiv R Λ' U (x ≫ f.hom.hom) (.ofAdd m') *
            Diagonalizable.characterPointsEquiv R Λ' U (y ≫ f.hom.hom) (.ofAdd m')
        rw [MonObj.mul_comp, map_mul, MonoidHom.mul_apply] }
  naturality a x := by
    change Diagonalizable.characterPointsEquiv R Λ' _ ((a ≫ x) ≫ f.hom.hom) (.ofAdd m') =
      Units.map a.left.appTop.hom.toMonoidHom
        (Diagonalizable.characterPointsEquiv R Λ' _ (x ≫ f.hom.hom) (.ofAdd m'))
    rw [Category.assoc, Diagonalizable.characterPointsEquiv_naturality]

end NaturalUnits

/-- Part 2: over a field, `g ↦ D(g)` is a bijection `Hom(Λ', Λ) → Hom(D(Λ), D(Λ'))`. -/
theorem restrictMap_bijective (k : Type u) [Field k] (Λ Λ' : Type u) [AddCommGroup Λ]
    [AddCommGroup Λ'] :
    Function.Bijective
      (fun g : Λ' →+ Λ => Diagonalizable.restrictMap (CommRingCat.of k) g) := by
  constructor
  · intro g₁ g₂ h
    change Diagonalizable.restrictMap (CommRingCat.of k) g₁ =
      Diagonalizable.restrictMap (CommRingCat.of k) g₂ at h
    ext l'
    have h₁ : ∀ (U : Over (Spec (CommRingCat.of k)))
        (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
        (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of k) g₁) l').app U x =
          Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ U x (.ofAdd (g₁ l')) :=
      fun U x => Diagonalizable.pointsEquiv_restrictMap _ g₁ x l'
    have h₂ : ∀ (U : Over (Spec (CommRingCat.of k)))
        (x : U ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
        (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of k) g₁) l').app U x =
          Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ U x (.ofAdd (g₂ l')) := by
      rw [h]
      exact fun U x => Diagonalizable.pointsEquiv_restrictMap _ g₂ x l'
    exact (NaturalUnits.ofHom (Diagonalizable.restrictMap (CommRingCat.of k) g₁) l').existsUnique.unique
      h₁ h₂
  · intro f
    choose g hg using fun m' : Λ' => (NaturalUnits.ofHom f m').existsUnique
    have hadd : ∀ a b : Λ', g (a + b) = g a + g b := fun a b =>
      ((hg (a + b)).2 (g a + g b) (fun U x => by
        change Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' U (x ≫ f.hom.hom)
            (.ofAdd (a + b)) = _
        rw [ofAdd_add, map_mul, ofAdd_add, map_mul]
        exact congrArg₂ (· * ·) ((hg a).1 U x) ((hg b).1 U x))).symm
    refine ⟨AddMonoidHom.mk' g hadd, ?_⟩
    apply hom_ext_points
    intro T x
    apply (Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ' T).injective
    apply MonoidHom.ext
    intro l'
    exact (Diagonalizable.pointsEquiv_restrictMap _ (AddMonoidHom.mk' g hadd) x l'.toAdd).trans
      ((hg l'.toAdd).1 T x).symm

end Final

end DiagonalizableCharacter

open DiagonalizableCharacter in
/-- **Characters and homomorphisms of diagonalizable groups** (Milne, *Algebraic Groups*,
Lemma 12.4 and Theorem 12.9(a)). -/
theorem diagonalizableCharacter : DiagonalizableCharacterStatement.{u} := by
  intro k _
  exact ⟨fun Λ _ _ => ⟨fun m => ⟨evalCharacter _ Λ m, evalCharacter_apply _ Λ m⟩,
      fun χ => (NaturalUnits.ofCharacter χ).existsUnique⟩,
    fun Λ Λ' _ _ _ _ => restrictMap_bijective k Λ Λ'⟩

end Langlands.GroupScheme
