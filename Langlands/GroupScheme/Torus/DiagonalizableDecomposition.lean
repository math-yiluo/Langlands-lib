import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Free and finite factors of diagonalizable group schemes -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj DirectSum

namespace Langlands.GroupScheme.Diagonalizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

section Characters

variable (A B : Type u) [AddCommGroup A] [AddCommGroup B]

/-- Characters of a product are pairs of characters, without any torsion restriction. -/
def productCharactersEquiv (M : Type v) [CommGroup M] :
    (Multiplicative (A × B) →* M) ≃*
      (Multiplicative A →* M) × (Multiplicative B →* M) where
  toFun χ :=
    (χ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl A B)),
      χ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr A B)))
  invFun χ :=
    { toFun := fun b => χ.1 (.ofAdd b.toAdd.1) * χ.2 (.ofAdd b.toAdd.2)
      map_one' := by simp
      map_mul' := fun b c => by
        change χ.1 (.ofAdd (b.toAdd.1 + c.toAdd.1)) *
            χ.2 (.ofAdd (b.toAdd.2 + c.toAdd.2)) = _
        rw [show Multiplicative.ofAdd (b.toAdd.1 + c.toAdd.1) =
            Multiplicative.ofAdd b.toAdd.1 * .ofAdd c.toAdd.1 from rfl,
          show Multiplicative.ofAdd (b.toAdd.2 + c.toAdd.2) =
            Multiplicative.ofAdd b.toAdd.2 * .ofAdd c.toAdd.2 from rfl,
          map_mul, map_mul, mul_mul_mul_comm] }
  left_inv χ := by
    apply MonoidHom.ext
    intro b
    change χ (.ofAdd (b.toAdd.1, 0)) * χ (.ofAdd (0, b.toAdd.2)) = χ b
    rw [← map_mul]
    congr 1
    change Multiplicative.ofAdd (b.toAdd.1 + 0, 0 + b.toAdd.2) = b
    simp
  right_inv χ := by
    apply Prod.ext
    · apply MonoidHom.ext
      intro b
      change χ.1 b * χ.2 1 = χ.1 b
      simp
    · apply MonoidHom.ext
      intro b
      change χ.1 1 * χ.2 b = χ.2 b
      simp
  map_mul' χ ψ := by
    apply Prod.ext <;> apply MonoidHom.ext <;> intro b <;> rfl

end Characters

variable (R : CommRingCat.{u})

/-- Character-point naturality as an equality of full character homomorphisms. -/
theorem characterPointsEquiv_natural (A : Type u) [AddCommGroup A]
    {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ (groupScheme R A).X) :
    characterPointsEquiv R A T' (a ≫ x) =
      (Units.map a.left.appTop.hom.toMonoidHom).comp
        (characterPointsEquiv R A T x) := by
  apply MonoidHom.ext
  intro b
  exact characterPointsEquiv_naturality R A a x b.toAdd

section Congruence

variable {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)

/-- Reindexing the characters of the actual diagonalizable group. -/
def congrCharacterPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme R A).X) ≃* (Multiplicative B →* (Γ(T.left, ⊤))ˣ) :=
  (characterPointsEquiv R A T).trans e.toMultiplicative.monoidHomCongrLeft

theorem congrCharacterPointsEquiv_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme R A).X) :
    congrCharacterPointsEquiv R e T' (a ≫ x) =
      (Units.map a.left.appTop.hom.toMonoidHom).comp
        (congrCharacterPointsEquiv R e T x) := by
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv R A T' (a ≫ x) (.ofAdd (e.symm b.toAdd)) = _
  rw [characterPointsEquiv_naturality]
  rfl

/-- An actual group-scheme isomorphism induced by a character-group isomorphism. -/
def congrIso : (groupScheme R A).toGrp ≅ (groupScheme R B).toGrp :=
  isoOfPointModels (fun T : Over (Spec R) => Multiplicative B →* (Γ(T.left, ⊤))ˣ)
    (fun a => MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom))
    (congrCharacterPointsEquiv R e) (characterPointsEquiv R B)
    (congrCharacterPointsEquiv_naturality R e) (characterPointsEquiv_natural R B)

/-- Reindexing gives the expected evaluation on every test scheme. -/
theorem congrIso_hom (T : Over (Spec R)) (x : T ⟶ (groupScheme R A).X)
    (b : B) :
    characterPointsEquiv R B T (x ≫ (congrIso R e).hom.hom.hom) (.ofAdd b) =
      characterPointsEquiv R A T x (.ofAdd (e.symm b)) := by
  exact congrArg (fun χ : Multiplicative B →* (Γ(T.left, ⊤))ˣ => χ (.ofAdd b))
    (isoOfPointModels_hom
      (fun T : Over (Spec R) => Multiplicative B →* (Γ(T.left, ⊤))ˣ)
      (fun a => MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom))
      (congrCharacterPointsEquiv R e) (characterPointsEquiv R B)
      (congrCharacterPointsEquiv_naturality R e) (characterPointsEquiv_natural R B) T x)

end Congruence

section Products

variable (A B : Type u) [AddCommGroup A] [AddCommGroup B]

/-- Pair of character coordinates for a diagonalizable group with product lattice. -/
def productCharacterPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme R (A × B)).X) ≃*
      (Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
        (Multiplicative B →* (Γ(T.left, ⊤))ˣ) :=
  (characterPointsEquiv R (A × B) T).trans (productCharactersEquiv A B _)

/-- Pair of character coordinates for the actual product of diagonalizable groups. -/
def tensorCharacterPointsEquiv (T : Over (Spec R)) :
    (T ⟶ ((groupScheme R A).toGrp ⊗ (groupScheme R B).toGrp).X) ≃*
      (Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
        (Multiplicative B →* (Γ(T.left, ⊤))ˣ) :=
  (productPointsEquiv _ _ T).trans
    { (characterPointsEquiv R A T).toEquiv.prodCongr
        (characterPointsEquiv R B T).toEquiv with
      map_mul' := fun x y => Prod.ext
        (map_mul (characterPointsEquiv R A T) x.1 y.1)
        (map_mul (characterPointsEquiv R B T) x.2 y.2) }

/-- Restricting a pair of characters under a change of test scheme. -/
def productCharacterRestrict {T T' : Over (Spec R)} (a : T' ⟶ T) :
    ((Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
      (Multiplicative B →* (Γ(T.left, ⊤))ˣ)) →*
    ((Multiplicative A →* (Γ(T'.left, ⊤))ˣ) ×
      (Multiplicative B →* (Γ(T'.left, ⊤))ˣ)) :=
  (MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom)).prodMap
    (MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom))

theorem productCharacterPointsEquiv_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme R (A × B)).X) :
    productCharacterPointsEquiv R A B T' (a ≫ x) =
      productCharacterRestrict R A B a (productCharacterPointsEquiv R A B T x) := by
  apply Prod.ext <;> apply MonoidHom.ext <;> intro b
  · change characterPointsEquiv R (A × B) T' (a ≫ x) (.ofAdd (b.toAdd, 0)) = _
    rw [characterPointsEquiv_naturality]
    rfl
  · change characterPointsEquiv R (A × B) T' (a ≫ x) (.ofAdd (0, b.toAdd)) = _
    rw [characterPointsEquiv_naturality]
    rfl

theorem tensorCharacterPointsEquiv_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T)
    (x : T ⟶ ((groupScheme R A).toGrp ⊗ (groupScheme R B).toGrp).X) :
    tensorCharacterPointsEquiv R A B T' (a ≫ x) =
      productCharacterRestrict R A B a (tensorCharacterPointsEquiv R A B T x) := by
  apply Prod.ext
  · change characterPointsEquiv R A T' ((a ≫ x) ≫ fst _ _) = _
    rw [Category.assoc, characterPointsEquiv_natural]
    rfl
  · change characterPointsEquiv R B T' ((a ≫ x) ≫ snd _ _) = _
    rw [Category.assoc, characterPointsEquiv_natural]
    rfl

/-- The actual diagonalizable group of a product lattice is the product group scheme. -/
def productIso : (groupScheme R (A × B)).toGrp ≅
    (groupScheme R A).toGrp ⊗ (groupScheme R B).toGrp :=
  isoOfPointModels (fun T : Over (Spec R) =>
      (Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
        (Multiplicative B →* (Γ(T.left, ⊤))ˣ))
    (fun a => productCharacterRestrict R A B a)
    (productCharacterPointsEquiv R A B) (tensorCharacterPointsEquiv R A B)
    (productCharacterPointsEquiv_naturality R A B)
    (tensorCharacterPointsEquiv_naturality R A B)

end Products

section Decomposition

variable {Λ : Type u} [AddCommGroup Λ]
    {I A : Type u} [Fintype I] [DecidableEq I] [AddCommGroup A]

/-- A lattice decomposition gives an actual split torus times a diagonalizable factor. -/
def splitFiniteIso (e : Λ ≃+ (I → ℤ) × A) :
    (groupScheme R Λ).toGrp ≅
      splitTorus (Spec R) I ⊗ (groupScheme R A).toGrp :=
  congrIso R e ≪≫ productIso R (I → ℤ) A ≪≫
    ((splitIso R (AddEquiv.refl (I → ℤ))) ⊗ᵢ Iso.refl _)

/-- A finite character group gives a finite morphism over the original base,
including characteristic torsion and nilpotents. -/
instance isFinite [Finite A] : IsFinite (groupScheme R A).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R (AddMonoidAlgebra R A))))
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap R (AddMonoidAlgebra R A)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

/-- Every finitely generated character group yields a split torus times a finite
full diagonalizable factor over the original base ring. -/
theorem exists_splitFiniteIso (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    ∃ (I A : Type u) (_ : Fintype I) (_ : AddCommGroup A) (_ : Finite A),
      Nonempty ((groupScheme R Λ).toGrp ≅
        splitTorus (Spec R) I ⊗ (groupScheme R A).toGrp) := by
  classical
  obtain ⟨n, J, hJ, p, hp, e, ⟨b⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod Λ
  have : ∀ i : J, NeZero (p i ^ e i) :=
    fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let A := ULift.{u} (⨁ i : J, ZMod (p i ^ e i))
  have : Finite (⨁ i : J, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let c : (Fin n →₀ ℤ) ≃+ (ULift.{u} (Fin n) → ℤ) :=
    Finsupp.addEquivFunOnFinite.trans
      (AddEquiv.arrowCongr Equiv.ulift.symm (AddEquiv.refl ℤ))
  let b' : Λ ≃+ (ULift.{u} (Fin n) → ℤ) × A :=
    b.trans (c.prodCongr AddEquiv.ulift.symm)
  exact ⟨ULift.{u} (Fin n), A, inferInstance, inferInstance, inferInstance,
    ⟨splitFiniteIso R b'⟩⟩

end Decomposition

end Langlands.GroupScheme.Diagonalizable
