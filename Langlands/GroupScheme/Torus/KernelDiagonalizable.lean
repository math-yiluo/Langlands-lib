import Langlands.GroupScheme.Torus.QuotientCharacters
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.AbelianScheme.Kernel

/-! # The actual kernel of a split-torus character is diagonalizable -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace characterLattice

variable {k : Type u} [CommRing k] [IsDomain k]
variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Evaluation at an actual point, with values in the global units of the test scheme. -/
def pointCharacters (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ T.X) →* (Multiplicative (characterLattice T) →* (Γ(U.left, ⊤))ˣ) where
  toFun x :=
    { toFun := fun χ => Gm.pointsEquiv _ U
        (x ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom)
      map_one' := by
        change Gm.pointsEquiv _ U
          (x ≫ (CommGroupScheme.groupHom (0 : characterLattice T)).hom.hom) = 1
        rw [comp_groupHom_zero, map_one]
      map_mul' := fun χ ψ => by
        change Gm.pointsEquiv _ U
          (x ≫ (CommGroupScheme.groupHom (χ.toAdd + ψ.toAdd)).hom.hom) = _
        rw [comp_groupHom_add, map_mul] }
  map_one' := by
    apply MonoidHom.ext
    intro χ
    change Gm.pointsEquiv _ U
      (1 ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom) = 1
    rw [MonObj.one_comp, map_one]
  map_mul' := by
    intro x y
    apply MonoidHom.ext
    intro χ
    change Gm.pointsEquiv _ U
      ((x * y) ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom) = _
    rw [MonObj.mul_comp, map_mul]
    rfl

omit [IsDomain k] in
@[simp] theorem pointCharacters_apply (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ T.X) (χ : characterLattice T) :
    pointCharacters T U x (.ofAdd χ) =
      Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ).hom.hom) := rfl

/-- In split coordinates, evaluation is exactly the usual character of the lattice. -/
theorem pointCharacters_split (I : Type u) [Fintype I] [DecidableEq I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) :
    pointCharacters T U x =
      (Diagonalizable.charEquiv
        ((comapIso (T' := splitTorus.commGroupScheme _ I) e).symm.trans
          (splitTorus.characterLatticeEquiv k I)) _).symm
        (splitTorus.pointsEquiv I U (x ≫ e.hom.hom.hom)) := by
  apply MonoidHom.ext
  intro χ
  let c := comapIso (T' := splitTorus.commGroupScheme _ I) e
  let b := splitTorus.characterLatticeEquiv k I
  have heval : x ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom =
      (x ≫ e.hom.hom.hom) ≫
        (CommGroupScheme.groupHom (c.symm χ.toAdd)).hom.hom := by
    conv_lhs => rw [← c.apply_symm_apply χ.toAdd]
    rfl
  change Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom) =
    ∏ j, splitTorus.pointsEquiv I U (x ≫ e.hom.hom.hom) j ^ b (c.symm χ.toAdd) j
  rw [heval]
  conv_lhs => rw [← b.symm_apply_apply (c.symm χ.toAdd)]
  exact splitTorus.pointsEquiv_characterLatticeEquiv_symm k I _ _

theorem pointCharacters_bijective (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of k))) :
    Function.Bijective (pointCharacters T U) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ := Fintype.ofFinite I
  let c := comapIso (T' := splitTorus.commGroupScheme _ I) e
  let b := c.symm.trans (splitTorus.characterLatticeEquiv k I)
  let q := ((isoPointsEquiv e U).trans (splitTorus.pointsEquiv I U)).trans
    (Diagonalizable.charEquiv b (Γ(U.left, ⊤))ˣ).symm
  have hq : (pointCharacters T U : (U ⟶ T.X) →
      (Multiplicative (characterLattice T) →* (Γ(U.left, ⊤))ˣ)) = q := by
    funext x
    exact pointCharacters_split T I e U x
  rw [hq]
  exact q.bijective

/-- A split torus corepresents characters of its actual character lattice on all tests. -/
def pointCharactersEquiv (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ T.X) ≃* (Multiplicative (characterLattice T) →* (Γ(U.left, ⊤))ˣ) :=
  MulEquiv.ofBijective (pointCharacters T U) (pointCharacters_bijective T hT U)

omit [IsDomain k] in
theorem pointCharacters_naturality {U U' : Over (Spec (CommRingCat.of k))}
    (f : U' ⟶ U) (x : U ⟶ T.X) (χ : characterLattice T) :
    pointCharacters T U' (f ≫ x) (.ofAdd χ) =
      Units.map f.left.appTop.hom.toMonoidHom (pointCharacters T U x (.ofAdd χ)) := by
  simp only [pointCharacters_apply, Category.assoc, Gm.pointsEquiv_naturality]

end characterLattice

namespace Diagonalizable

variable {k : Type u} [CommRing k] [IsDomain k]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
variable (a : characterLattice T)

/-- Points of the actual scheme kernel are precisely lattice characters killing `a`. -/
def kernelCharacterPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ (kernel (CommGroupScheme.groupHom a)).X) ≃*
      annihilator a (Γ(U.left, ⊤))ˣ where
  toFun x := ⟨characterLattice.pointCharacters T U
    (x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom), by
      change Gm.pointsEquiv _ U
        ((x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
          (CommGroupScheme.groupHom a).hom.hom) = 1
      have hx : (x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
          (CommGroupScheme.groupHom a).hom.hom = 1 :=
        (kernelPointsEquiv (CommGroupScheme.groupHom a) U x).property
      rw [hx, map_one]⟩
  invFun χ := (kernelPointsEquiv (CommGroupScheme.groupHom a) U).symm
    ⟨(characterLattice.pointCharactersEquiv T hT U).symm χ.val, by
      apply (Gm.pointsEquiv _ U).injective
      rw [map_one]
      change characterLattice.pointCharacters T U
        ((characterLattice.pointCharactersEquiv T hT U).symm χ.val) (.ofAdd a) = 1
      have h := congrArg (fun ψ : Multiplicative (characterLattice T) →*
          (Γ(U.left, ⊤))ˣ => ψ (.ofAdd a))
        ((characterLattice.pointCharactersEquiv T hT U).apply_symm_apply χ.val)
      exact h.trans χ.property⟩
  left_inv x := by
    apply (kernelPointsEquiv (CommGroupScheme.groupHom a) U).injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply]
    change (characterLattice.pointCharactersEquiv T hT U).symm
      (characterLattice.pointCharactersEquiv T hT U
        (x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom)) = _
    exact (characterLattice.pointCharactersEquiv T hT U).symm_apply_apply _
  right_inv χ := by
    apply Subtype.ext
    change characterLattice.pointCharacters T U
      ((kernelPointsEquiv (CommGroupScheme.groupHom a) U).symm _ ≫
        (kernelι (CommGroupScheme.groupHom a)).hom.hom) = χ.val
    rw [← kernelPointsEquiv_val]
    rw [MulEquiv.apply_symm_apply]
    exact (characterLattice.pointCharactersEquiv T hT U).apply_symm_apply χ.val
  map_mul' x y := by
    apply Subtype.ext
    change characterLattice.pointCharacters T U
      ((x * y) ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) = _
    rw [MonObj.mul_comp, map_mul]
    rfl

@[simp] theorem kernelCharacterPointsEquiv_apply (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ (kernel (CommGroupScheme.groupHom a)).X) (b : characterLattice T) :
    (kernelCharacterPointsEquiv T hT a U x).val (.ofAdd b) =
      Gm.pointsEquiv _ U
        ((x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
          (CommGroupScheme.groupHom b).hom.hom) := rfl

/-- Restriction of characters killing `a` along every refinement of the test scheme. -/
def annihilatorRestrict {U U' : Over (Spec (CommRingCat.of k))} (f : U' ⟶ U) :
    annihilator a (Γ(U.left, ⊤))ˣ →* annihilator a (Γ(U'.left, ⊤))ˣ where
  toFun χ := ⟨(Units.map f.left.appTop.hom.toMonoidHom).comp χ.val, by
    change Units.map f.left.appTop.hom.toMonoidHom (χ.val (.ofAdd a)) = 1
    rw [χ.property, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_one (Units.map f.left.appTop.hom.toMonoidHom)
  map_mul' χ ψ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro b
    exact map_mul (Units.map f.left.appTop.hom.toMonoidHom) (χ.val b) (ψ.val b)

theorem kernelCharacterPointsEquiv_naturality
    {U U' : Over (Spec (CommRingCat.of k))} (f : U' ⟶ U)
    (x : U ⟶ (kernel (CommGroupScheme.groupHom a)).X) :
    kernelCharacterPointsEquiv T hT a U' (f ≫ x) =
      annihilatorRestrict T a f (kernelCharacterPointsEquiv T hT a U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change Gm.pointsEquiv _ U'
    (((f ≫ x) ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
      (CommGroupScheme.groupHom b.toAdd).hom.hom) =
    Units.map f.left.appTop.hom.toMonoidHom
      (Gm.pointsEquiv _ U
        ((x ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
          (CommGroupScheme.groupHom b.toAdd).hom.hom))
  simp only [Category.assoc, Gm.pointsEquiv_naturality]

/-- The diagonalizable point model with its explicit character type. -/
def characterPointsEquiv (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]
    (U : Over (Spec R)) :
    (U ⟶ (groupScheme R Λ).X) ≃*
      (Multiplicative Λ →* (Γ(U.left, ⊤))ˣ) :=
  Corepresented.pointsEquiv (functor R Λ) (grpCorepresentation R Λ) U

theorem characterPointsEquiv_naturality (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] {U U' : Over (Spec R)} (f : U' ⟶ U)
    (x : U ⟶ (groupScheme R Λ).X) (b : Λ) :
    characterPointsEquiv R Λ U' (f ≫ x) (.ofAdd b) =
      Units.map f.left.appTop.hom.toMonoidHom
        (characterPointsEquiv R Λ U x (.ofAdd b)) := by
  unfold characterPointsEquiv
  erw [Corepresented.pointsEquiv_naturality]
  rfl

/-- The diagonalizable quotient has the same annihilator point model. -/
def quotientCharacterPointsEquiv (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ (groupScheme (CommRingCat.of k) (quotientLattice a)).X) ≃*
      annihilator a (Γ(U.left, ⊤))ˣ :=
  (characterPointsEquiv (CommRingCat.of k) (quotientLattice a) U).trans
      (quotientCharactersEquiv a (Γ(U.left, ⊤))ˣ)

omit [IsDomain k] in
theorem quotientCharacterPointsEquiv_naturality
    {U U' : Over (Spec (CommRingCat.of k))} (f : U' ⟶ U)
    (x : U ⟶ (groupScheme (CommRingCat.of k) (quotientLattice a)).X) :
    quotientCharacterPointsEquiv T a U' (f ≫ x) =
      annihilatorRestrict T a f (quotientCharacterPointsEquiv T a U x) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv _ _ U' (f ≫ x)
    (.ofAdd (quotientMap a b.toAdd)) = _
  rw [characterPointsEquiv_naturality]
  rfl

/-- The scheme-theoretic kernel of `a` is `D(X*(T)/ℤa)`, with the full relation. -/
def kernelDiagonalizableIso :
    kernel (CommGroupScheme.groupHom a) ≅
      (groupScheme (CommRingCat.of k) (quotientLattice a)).toGrp :=
  isoOfPointModels
    (fun U : Over (Spec (CommRingCat.of k)) => annihilator a (Γ(U.left, ⊤))ˣ)
    (fun f => annihilatorRestrict T a f)
    (kernelCharacterPointsEquiv T hT a)
    (quotientCharacterPointsEquiv T a)
    (kernelCharacterPointsEquiv_naturality T hT a)
    (quotientCharacterPointsEquiv_naturality T a)

/-- On points, the inverse kernel model evaluates a character on its quotient class. -/
theorem kernelDiagonalizableIso_inv
    (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ (groupScheme (CommRingCat.of k) (quotientLattice a)).X)
    (b : characterLattice T) :
    Gm.pointsEquiv _ U
      (((x ≫ (kernelDiagonalizableIso T hT a).inv.hom.hom) ≫
          (kernelι (CommGroupScheme.groupHom a)).hom.hom) ≫
        (CommGroupScheme.groupHom b).hom.hom) =
      (characterPointsEquiv (CommRingCat.of k) (quotientLattice a) U x)
          (.ofAdd (quotientMap a b)) := by
  have h := isoOfPointModels_inv
    (fun U : Over (Spec (CommRingCat.of k)) => annihilator a (Γ(U.left, ⊤))ˣ)
    (fun f => annihilatorRestrict T a f)
    (kernelCharacterPointsEquiv T hT a)
    (quotientCharacterPointsEquiv T a)
    (kernelCharacterPointsEquiv_naturality T hT a)
    (quotientCharacterPointsEquiv_naturality T a) U x
  exact congrArg (fun χ : annihilator a (Γ(U.left, ⊤))ˣ => χ.val (.ofAdd b)) h

include hT in
/-- The quotient character group is finitely generated, retaining any torsion. -/
theorem quotientLattice_fg : AddGroup.FG (quotientLattice a) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let b := (splitTorus.characterLatticeEquiv k I).symm.trans c
  let : AddGroup.FG (characterLattice T) :=
    AddGroup.fg_of_surjective (f := b.toAddMonoidHom) b.surjective
  infer_instance

end Diagonalizable

end Langlands.GroupScheme
