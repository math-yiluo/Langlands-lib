import Langlands.GroupScheme.Absolute.TriangularCharacterKernelDescent
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # Actual diagonal characters on triangular additive coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {N : ℕ} (R : CommRingCat.{u})

theorem triangularWeights_injective :
    Function.Injective (fun i : Fin N => -(i.val : ℤ)) := by
  intro i j h
  apply Fin.ext
  exact Int.ofNat_inj.mp (neg_injective h)

/-- The diagonal coordinate on all relative points of the actual diagonal
block Levi, with its value viewed as a point of the multiplicative group. -/
def diagonalEntryPoints (i : Fin N) (T : Over (Spec R)) :
    (T ⟶ (GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ))).X) →*
      (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    ((Pi.evalMonoidHom (fun _ : ULift.{u} (Fin N) => Γ(T.left, ⊤)ˣ) ⟨i⟩).comp
      (GeneralLinear.diagonalLeviPointsEquiv (fun i : Fin N => -(i.val : ℤ))
        triangularWeights_injective R T).toMonoidHom)

theorem diagonalEntryPoints_naturality (i : Fin N)
    {T V : Over (Spec R)} (f : V ⟶ T)
    (x : T ⟶ (GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ))).X) :
    diagonalEntryPoints R i V (f ≫ x) = f ≫ diagonalEntryPoints R i T x := by
  apply (Gm.pointsEquiv (Spec R) V).injective
  simp only [diagonalEntryPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  rw [GeneralLinear.diagonalLeviPointsEquiv_naturality]
  rfl

/-- The actual diagonal entry homomorphism of the diagonal block Levi. -/
def diagonalEntryHom (i : Fin N) :
    GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)) ⟶
      (Gm (Spec R)).toGrp :=
  homOfPoints (diagonalEntryPoints R i) (diagonalEntryPoints_naturality R i)

theorem diagonalEntryHom_value (i : Fin N) {T : Over (Spec R)}
    (x : T ⟶ (GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ))).X) :
    (Gm.pointsEquiv (Spec R) T (x ≫ (diagonalEntryHom R i).hom.hom) : Γ(T.left, ⊤)) =
      (GeneralLinear.pointsEquiv (Fin N) R T
        (x ≫ (GeneralLinear.blockLeviHom (Fin N) R _).hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i i := by
  rw [diagonalEntryHom, comp_homOfPoints]
  simp only [diagonalEntryPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change ((GeneralLinear.diagonalLeviPointsEquiv _ _ R T x ⟨i⟩ : Γ(T.left, ⊤)ˣ) :
    Γ(T.left, ⊤)) = _
  change ((GeneralLinear.diagonalLeviEquiv (fun i : Fin N => -(i.val : ℤ))
    triangularWeights_injective Γ(T.left, ⊤)).symm
      (Corepresented.pointsEquiv _ _ T x) i : Γ(T.left, ⊤)) = _
  rw [GeneralLinear.diagonalLeviEquiv_symm_val]
  exact congrArg (fun g : GL (Fin N) Γ(T.left, ⊤) => g i i)
    (GeneralLinear.pointsEquiv_cutHom _ x).symm

variable {R} {D : CommGroupScheme (Spec R)}

/-- The genuine ratio character on the supplied full commutative diagonal
group. The group may have torsion characters and need not be reduced. -/
def diagonalRatioCharacter
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (i j : Fin N) : characterLattice D :=
  Additive.ofMul ((d ≫ diagonalEntryHom R i) * (d ≫ diagonalEntryHom R j)⁻¹)

theorem diagonalRatioCharacter_value
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (i j : Fin N) {T : Over (Spec R)} (x : T ⟶ D.X) :
    VectorGroup.charValue (diagonalRatioCharacter d i j) T x =
      (GeneralLinear.pointsEquiv (Fin N) R T
        ((x ≫ d.hom.hom) ≫ (GeneralLinear.blockLeviHom (Fin N) R _).hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i i *
      (GeneralLinear.pointsEquiv (Fin N) R T
        ((x⁻¹ ≫ d.hom.hom) ≫ (GeneralLinear.blockLeviHom (Fin N) R _).hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) j j := by
  change (Gm.pointsEquiv (Spec R) T
    (x ≫ (((d ≫ diagonalEntryHom R i) * (d ≫ diagonalEntryHom R j)⁻¹).hom.hom)) :
      Γ(T.left, ⊤)) = _
  rw [Grp.Hom.hom_mul, Mon.Hom.hom_mul, Grp.Hom.hom_hom_inv,
    MonObj.comp_mul, GrpObj.comp_inv, map_mul, Units.val_mul]
  have hi := diagonalEntryHom_value R i (x ≫ d.hom.hom)
  have hj := diagonalEntryHom_value R j (x⁻¹ ≫ d.hom.hom)
  rw [Grp.comp_hom_hom, ← Category.assoc, hi]
  rw [← GrpObj.inv_comp, Grp.comp_hom_hom, ← Category.assoc, hj]

variable {H : GroupScheme (Spec R)}

/-- A supplied diagonal factorization preserves the diagonal entries of the
original triangular matrices on every relative test scheme. -/
theorem diagonal_factor_entry
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) R _)
    {T : Over (Spec R)} (x : T ⟶ H.X) (i : Fin N) :
    (GeneralLinear.pointsEquiv (Fin N) R T
      (((x ≫ q.hom.hom) ≫ d.hom.hom) ≫
        (GeneralLinear.blockLeviHom (Fin N) R _).hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i i =
      (MatrixRepresentation.pointMatrix
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) T x :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i i := by
  have hfac' := congrArg (fun f => f.hom.hom) hfac
  simp only [Grp.comp_hom_hom] at hfac'
  rw [Category.assoc x q.hom.hom d.hom.hom, hfac',
    ← Category.assoc x j.hom.hom, GeneralLinear.pointsEquiv_blockLimitHom,
    GeneralLinear.coe_blockLeviProjection, GeneralLinear.blockDiagonalPart_apply,
    ite_eq_left rfl]
  rfl

theorem diagonalRatioCharacter_value_lift
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) R _)
    (i l : Fin N) {T : Over (Spec R)} (x : T ⟶ H.X) :
    VectorGroup.charValue (diagonalRatioCharacter d i l) T (x ≫ q.hom.hom) =
      (MatrixRepresentation.pointMatrix
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) T x :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i i *
      (MatrixRepresentation.pointMatrix
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) T x⁻¹ :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) l l := by
  rw [diagonalRatioCharacter_value, ← GrpObj.inv_comp,
    diagonal_factor_entry j q d hfac, diagonal_factor_entry j q d hfac]

/-- Actual ambient conjugation on a full coordinate-refined subgroup. -/
def filtrationConjugation
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (a b : ℕ) :
    AutomorphicAction H
      (filtrationScheme (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b) := by
  have : IsClosedImmersion
      (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom.left :=
    isClosedSubgroup_filtrationHom _ a b
  have : Mono
      (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom :=
    Over.mono_of_mono_left _
  exact LinearKernelTower.normalConjugation _ (isNormal_triangular_filtration j a b)

theorem filtrationConjugation_comp
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (a b : ℕ) {T : Over (Spec R)} (g : T ⟶ H.X)
    (x : T ⟶ (filtrationScheme
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).X) :
    (filtrationConjugation j a b).act g x ≫
      (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom =
    g * (x ≫
      (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom) * g⁻¹ :=
  by
    have : IsClosedImmersion
        (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom.left :=
      isClosedSubgroup_filtrationHom _ a b
    have : Mono
        (filtrationHom (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).hom.hom :=
      Over.mono_of_mono_left _
    exact LinearKernelTower.normalConjugation_comp _
      (isNormal_triangular_filtration j a b) g x

/-- The actual additive coordinate intertwines full ambient conjugation and
the ratio character on any supplied diagonal factorization. -/
theorem filtrationCoordinate_equivariant
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (q : H ⟶ D.toGrp)
    (d : D.toGrp ⟶ GeneralLinear.blockLeviScheme (Fin N) R (fun i => -(i.val : ℤ)))
    (hfac : q ≫ d = j ≫ GeneralLinear.blockLimitHom (Fin N) R _)
    (a b : ℕ) (i l : Fin N) {T : Over (Spec R)} (g : T ⟶ H.X)
    (x : T ⟶ (filtrationScheme
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b).X) :
    (filtrationConjugation j a b).act g x ≫
      (filtrationCoordinate
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b i l).hom.hom =
    (VectorGroup.weightAction (n := 1) (diagonalRatioCharacter d i l)).act
      (g ≫ q.hom.hom)
      (x ≫ (filtrationCoordinate
        (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b i l).hom.hom) := by
  let ρ := j ≫ GeneralLinear.blockParabolicHom (Fin N) R (fun i => -(i.val : ℤ))
  have hg := (upper Γ(T.left, ⊤) N).inv_mem (triangular_pointMatrix_mem_upper j T g)
  have hx := (mem_range_filtrationHom ρ a b
    (x ≫ (filtrationHom ρ a b).hom.hom)).mp ⟨x, rfl⟩
  apply VectorGroup.points_ext
  intro r
  rw [coordinates_filtrationCoordinate, filtrationConjugation_comp,
    map_mul, map_mul, map_inv]
  have he := congrFun (congrFun
    (layer_conj hg hx.1) i) l
  simp only [inv_inv, scale_apply] at he
  rw [he, VectorGroup.coordinates_weightAction_act,
    diagonalRatioCharacter_value_lift j q d hfac]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coordinates_filtrationCoordinate]
  simp only [map_inv]
  ring

end Langlands.GroupScheme.TriangularLayer
