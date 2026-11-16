import Langlands.GroupScheme.Reductive.CorootTorusProjection
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessGeometry

/-! # Split product geometry of the coroot torus projection -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Finite J]
  (P : RootDatum J (I → ℤ) (I → ℤ))

/-- A section of the quotient of the coordinate lattice by the coroot annihilator. -/
def corootLatticeSection : ((I → ℤ) ⧸ cocenterLattice P) →ₗ[ℤ] (I → ℤ) := by
  letI := Langlands.RootDatum.free_quotient_corootAnnihilator P Set.univ
  exact Classical.choose ((cocenterLattice P).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (cocenterLattice P).mkQ_surjective))

@[simp]
theorem mkQ_corootLatticeSection (q : (I → ℤ) ⧸ cocenterLattice P) :
    (cocenterLattice P).mkQ (corootLatticeSection P q) = q := by
  let := Langlands.RootDatum.free_quotient_corootAnnihilator P Set.univ
  exact DFunLike.congr_fun (Classical.choose_spec
    ((cocenterLattice P).mkQ.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cocenterLattice P).mkQ_surjective))) q

/-- The coordinate lattice is the product of its annihilator and a free quotient. -/
def corootLatticeSplit :
    (cocenterLattice P × ((I → ℤ) ⧸ cocenterLattice P)) ≃ₗ[ℤ] (I → ℤ) :=
  LinearEquiv.ofBijective ((cocenterLattice P).subtype.coprod (corootLatticeSection P)) (by
    constructor
    · intro x y h
      have hq : x.2 = y.2 := by
        have h' := congrArg (cocenterLattice P).mkQ h
        change (cocenterLattice P).mkQ (x.1.val + corootLatticeSection P x.2) =
          (cocenterLattice P).mkQ (y.1.val + corootLatticeSection P y.2) at h'
        rw [map_add, map_add, mkQ_corootLatticeSection, mkQ_corootLatticeSection,
          show (cocenterLattice P).mkQ x.1.val = 0 from
            (Submodule.Quotient.mk_eq_zero (cocenterLattice P)).mpr x.1.property,
          show (cocenterLattice P).mkQ y.1.val = 0 from
            (Submodule.Quotient.mk_eq_zero (cocenterLattice P)).mpr y.1.property,
          zero_add, zero_add] at h'
        exact h'
      apply Prod.ext
      · apply Subtype.ext
        have hx : x.1.val + corootLatticeSection P x.2 =
            y.1.val + corootLatticeSection P y.2 := h
        rw [hq] at hx
        exact add_right_cancel hx
      · exact hq
    · intro x
      let q := (cocenterLattice P).mkQ x
      have hx : x - corootLatticeSection P q ∈ cocenterLattice P := by
        rw [← Submodule.Quotient.mk_eq_zero]
        change (cocenterLattice P).mkQ (x - corootLatticeSection P q) = 0
        rw [map_sub, mkQ_corootLatticeSection]
        exact sub_self _
      refine ⟨(⟨x - corootLatticeSection P q, hx⟩, q), ?_⟩
      change x - corootLatticeSection P q + corootLatticeSection P q = x
      exact sub_add_cancel _ _)

@[simp]
theorem corootLatticeSplit_inl (m : cocenterLattice P) :
    corootLatticeSplit P (m, 0) = m.val := by
  change m.val + corootLatticeSection P 0 = m.val
  simp

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.Diagonalizable

/-- The first coordinate of the diagonalizable product comparison restricts to
characters on the first summand. -/
theorem productIso_hom_fst (R : CommRingCat.{u}) (A B : Type u)
    [AddCommGroup A] [AddCommGroup B] (T : Over (Spec R))
    (x : T ⟶ (groupScheme R (A × B)).X) (a : A) :
    characterPointsEquiv R A T
        ((x ≫ (productIso R A B).hom.hom.hom) ≫ fst _ _) (.ofAdd a) =
      characterPointsEquiv R (A × B) T x (.ofAdd (a, 0)) := by
  exact congrArg (fun χ : (Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
      (Multiplicative B →* (Γ(T.left, ⊤))ˣ) => χ.1 (.ofAdd a))
    (isoOfPointModels_hom
      (fun T : Over (Spec R) => (Multiplicative A →* (Γ(T.left, ⊤))ˣ) ×
        (Multiplicative B →* (Γ(T.left, ⊤))ˣ))
      (fun a => productCharacterRestrict R A B a)
      (productCharacterPointsEquiv R A B) (tensorCharacterPointsEquiv R A B)
      (productCharacterPointsEquiv_naturality R A B)
      (tensorCharacterPointsEquiv_naturality R A B) T x)

end Langlands.GroupScheme.Diagonalizable

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Fintype I] [DecidableEq I] [Finite J]
  (R : CommRingCat.{u}) (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The split torus whose characters are the quotient by the coroot annihilator. -/
abbrev corootSubtorus : CommGroupScheme (Spec R) :=
  Diagonalizable.groupScheme R ((I → ℤ) ⧸ cocenterLattice P)

omit [DecidableEq I] in
/-- The free quotient lattice gives a split torus over every coefficient ring. -/
theorem isSplitTorus_corootSubtorus : IsSplitTorus (corootSubtorus R P).toGrp := by
  let := Langlands.RootDatum.free_quotient_corootAnnihilator P Set.univ
  let b := Module.Free.chooseBasis ℤ ((I → ℤ) ⧸ cocenterLattice P)
  exact Diagonalizable.isSplitTorus R b.equivFun.toAddEquiv

/-- A splitting of the character lattice gives a product decomposition of the
coordinate torus with the coroot quotient as its first factor. -/
def corootProjectionProductIso : splitTorus (Spec R) I ≅
    (corootQuotient R P).toGrp ⊗ (corootSubtorus R P).toGrp :=
  (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).symm ≪≫
    Diagonalizable.congrIso R (corootLatticeSplit P).symm.toAddEquiv ≪≫
      Diagonalizable.productIso R (cocenterLattice P) ((I → ℤ) ⧸ cocenterLattice P)

/-- The actual torus projection becomes first projection in the product coordinates. -/
theorem corootProjectionProductIso_fst :
    (corootProjectionProductIso R P).hom.hom.hom ≫ fst _ _ =
      (corootProjection R P).hom.hom := by
  apply (yoneda.map_injective)
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  apply (Diagonalizable.characterPointsEquiv R (cocenterLattice P) T.unop).injective
  apply MonoidHom.ext
  intro m
  change Diagonalizable.characterPointsEquiv R (cocenterLattice P) T.unop
      (x ≫ ((corootProjectionProductIso R P).hom.hom.hom ≫ fst _ _)) (.ofAdd m.toAdd) =
    Diagonalizable.characterPointsEquiv R (cocenterLattice P) T.unop
      (x ≫ (corootProjection R P).hom.hom) (.ofAdd m.toAdd)
  simp only [corootProjectionProductIso, Iso.trans_hom, Grp.comp_hom_hom,
    Iso.symm_hom, ← Category.assoc]
  dsimp only [corootQuotient, corootSubtorus]
  rw [Diagonalizable.productIso_hom_fst, Diagonalizable.congrIso_hom]
  change Diagonalizable.characterPointsEquiv R (I → ℤ) T.unop
    (x ≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv.hom.hom)
      (.ofAdd (corootLatticeSplit P (m.toAdd, 0))) = _
  rw [corootLatticeSplit_inl]
  simp only [corootProjection, Grp.comp_hom_hom, ← Category.assoc]
  exact (Diagonalizable.pointsEquiv_restrictMap R
    (cocenterLattice P).subtype.toAddMonoidHom
    (x ≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv.hom.hom)
    m.toAdd).symm

/-- The coroot quotient projection is smooth over every coefficient ring. -/
theorem smooth_corootProjection : Smooth (corootProjection R P).hom.hom.left := by
  exact GaloisNormSmoothnessGeometry.smooth_of_iso_fst
    ((Grp.forget (Over (Spec R))).mapIso (corootProjectionProductIso R P))
    (corootProjection R P).hom.hom
    (congrArg (fun f => f.left) (corootProjectionProductIso_fst R P))
    (isSplitTorus_corootSubtorus R P).smooth

/-- The coroot quotient projection is surjective, including over the zero ring. -/
theorem surjective_corootProjection :
    Surjective (corootProjection R P).hom.hom.left := by
  let D := (corootQuotient R P).toGrp
  let H := (corootSubtorus R P).toGrp
  have hfst : Surjective (fst D.X H.X).left := by
    constructor
    intro x
    refine ⟨(lift (𝟙 D.X) (1 : D.X ⟶ H.X)).left x, ?_⟩
    exact congrArg (fun f : D.X ⟶ D.X => f.left x) (lift_fst _ _)
  let : Surjective (fst D.X H.X).left := hfst
  let : IsIso (corootProjectionProductIso R P).hom.hom.hom :=
    (Grp.forget (Over (Spec R))).map_isIso (corootProjectionProductIso R P).hom
  let : IsIso (corootProjectionProductIso R P).hom.hom.hom.left :=
    (Over.forget (Spec R)).map_isIso (corootProjectionProductIso R P).hom.hom.hom
  rw [← corootProjectionProductIso_fst R P]
  change Surjective ((corootProjectionProductIso R P).hom.hom.hom.left ≫
    (fst D.X H.X).left)
  infer_instance

end Langlands.GroupScheme.RelativeDerived
