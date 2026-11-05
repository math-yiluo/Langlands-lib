import Langlands.GroupScheme.SplitExistence.UnipotentNormal
import Langlands.GroupScheme.SplitExistence.ExtPoints
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.CocharacterTransport
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.UnipotentProductBound

/-! # The Chevalley group is reductive

Let `k̄` be the algebraic closure of `k` and `G_{k̄}` the base change of the Chevalley group. Its
`k̄`-rational points are `k̄`-valued points of `G` over `k`, so they map injectively to `GL_n(k̄)`
with image in `Γ(k̄)`, and the image contains the generators `diag(χ(wt c))` and `x_j(s)` of
`Γ(k̄)`. Let `R ⊆ G_{k̄}` be a smooth connected unipotent normal closed subgroup. The matrices of
its rational points form a subgroup of `Γ(k̄)` normalized by `Γ(k̄)`, and they are unipotent
(Library `pointMatrix_sub_one_pow_eq_zero_of_isUnipotent`), so they are trivial
(`eq_bot_of_unipotent`). As `R` is reduced and of finite type over `k̄`, the inclusion `R → G_{k̄}`
is then the trivial morphism, so `R` is trivial. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

/-- Postcomposition with a group-scheme homomorphism, on points. -/
def postComp {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H) (T : Over S) :
    (T ⟶ G.X) →* (T ⟶ H.X) where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

namespace ChevGroup

variable (G : D.ChevGroup k)

/-- The base change of the Chevalley group to an algebraic closure of `k`. -/
abbrev geomGroup : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))) :=
  (GroupScheme.baseChange (toAlgebraicClosure k)).obj G.H

/-- The rational points of `G_{k̄}`. -/
abbrev geomPoint := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))

/-- Rational points of `G_{k̄}` as matrices in `GL_n(k̄)`. -/
def geomMat : ((geomPoint (k := k)) ⟶ G.geomGroup.X) →* GL (Fin D.n) (AlgebraicClosure k) :=
  (D.glExt k (AlgebraicClosure k)).toMonoidHom.comp
    ((postComp G.i _).comp (baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H).toMonoidHom)

theorem geomMat_apply (g : (geomPoint (k := k)) ⟶ G.geomGroup.X) :
    G.geomMat g = D.glExt k (AlgebraicClosure k)
      (baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H g ≫ G.i.hom.hom) :=
  rfl

theorem geomMat_mem (g : (geomPoint (k := k)) ⟶ G.geomGroup.X) :
    G.geomMat g ∈ D.chevSub (AlgebraicClosure k) := by
  rw [geomMat_apply, ← mem_chevPoints_iff_glExt]
  exact G.points (AlgebraicClosure k) _

theorem geomMat_injective : Function.Injective G.geomMat := by
  have := G.mono_i
  intro g g' h
  rw [geomMat_apply, geomMat_apply] at h
  exact (baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H).injective
    ((cancel_mono G.i.hom.hom).1 ((D.glExt k (AlgebraicClosure k)).injective h))

/-- Every element of `Γ(k̄)` is the matrix of a rational point of `G_{k̄}`. -/
theorem chevSub_le_range_geomMat : D.chevSub (AlgebraicClosure k) ≤ G.geomMat.range := by
  let e := specRingEquiv k (AlgebraicClosure k)
  have htor : ∀ χ : Multiplicative X →* (AlgebraicClosure k)ˣ, D.torusHom χ ∈ G.geomMat.range := by
    intro χ
    let y := (torusPointsEquiv k (extPoint (AlgebraicClosure k))).symm
      ((Units.map e.symm.toRingHom.toMonoidHom).comp χ)
    refine ⟨(baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H).symm (y ≫ G.t.hom.hom), ?_⟩
    rw [geomMat_apply, MulEquiv.apply_symm_apply, Category.assoc, ← Grp.comp_hom_hom, G.t_comp]
    change glMapEquiv e (GeneralLinear.pointsEquiv _ _ _ (y ≫ (D.torusToGL k).hom.hom)) = _
    rw [pointsEquiv_torusToGL, MulEquiv.apply_symm_apply]
    change Matrix.GeneralLinearGroup.map e.toRingHom _ = _
    rw [torusHom_map]
    congr 1
    ext m
    simp
  have hroot : ∀ (j : J) (s : AlgebraicClosure k), D.x j s ∈ G.geomMat.range := by
    intro j s
    let y := (VectorGroup.coordinates (CommRingCat.of k) 1 (extPoint (AlgebraicClosure k))).symm
      (Multiplicative.ofAdd fun _ => e.symm s)
    refine ⟨(baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H).symm
      (y ≫ (G.u j).hom.hom), ?_⟩
    rw [geomMat_apply, MulEquiv.apply_symm_apply, Category.assoc, ← Grp.comp_hom_hom, G.u_comp]
    change glMapEquiv e (GeneralLinear.pointsEquiv _ _ _ (y ≫ (D.rootToGL k j).hom.hom)) = _
    rw [pointsEquiv_rootToGL]
    change Matrix.GeneralLinearGroup.map e.toRingHom _ = _
    rw [D.x_map]
    congr 1
    simp only [gaCoord, y, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply]
    exact e.apply_symm_apply s
  refine sup_le ?_ ?_
  · rintro _ ⟨χ, rfl⟩
    exact htor χ
  · refine (Subgroup.closure_le _).2 ?_
    intro g hg
    obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hg
    obtain ⟨s, rfl⟩ := mem_rootSub.1 hj
    exact hroot j s

/-- The base change of the embedding `G → GL_n`, as a representation of `G_{k̄}`. -/
def geomRep : MatrixRepresentation G.geomGroup (Fin D.n) :=
  (GroupScheme.baseChange (toAlgebraicClosure k)).map G.i ≫
    (GeneralLinear.baseChangeIso (Fin D.n) (toAlgebraicClosure k)).hom

theorem baseChangeBasePointsEquiv_eq (g : (geomPoint (k := k)) ⟶ G.geomGroup.X) :
    baseChangeBasePointsEquiv (toAlgebraicClosure k) G.H g =
      (Over.homMk (𝟙 _) (by simp) : extPoint (AlgebraicClosure k) ⟶
        (Over.map (toAlgebraicClosure k)).obj geomPoint) ≫
        baseChangePointsEquiv (toAlgebraicClosure k) G.H _ g :=
  rfl

/-- The matrix of a rational point is its matrix under the representation `geomRep`. -/
theorem geomMat_eq_pointMatrix (g : (geomPoint (k := k)) ⟶ G.geomGroup.X) :
    G.geomMat g = Matrix.GeneralLinearGroup.map (specRingEquiv k (AlgebraicClosure k)).toRingHom
      (G.geomRep.pointMatrix _ g) := by
  rw [MatrixRepresentation.pointMatrix_apply, geomRep, Grp.comp_hom_hom, ← Category.assoc,
    GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp, geomMat_apply,
    baseChangeBasePointsEquiv_eq, Category.assoc]
  change Matrix.GeneralLinearGroup.map (specRingEquiv k (AlgebraicClosure k)).toRingHom
    (GeneralLinear.pointsEquiv _ _ _ (_ ≫ _)) = _
  rw [GeneralLinear.pointsEquiv_naturality]
  ext c d
  simp

/-- The rational points of `Spec k̄` as `k̄`-valued points over `k̄`. -/
def geomPointIso : extPoint (k := AlgebraicClosure k) (AlgebraicClosure k) ≅ geomPoint (k := k) :=
  Over.isoMk (Iso.refl _) (by simp [extMap])

variable [Finite J] [P.IsReduced]

/-- **The geometric unipotent radical of the Chevalley group is trivial.** -/
theorem hasTrivialUnipotentRadical : HasTrivialUnipotentRadical G.geomGroup := by
  intro R i hC hS hCon hU hN
  let mat := G.geomMat.comp (postComp i geomPoint)
  have hmat : ∀ h, mat h = G.geomMat (h ≫ i.hom.hom) := fun _ => rfl
  have hNbot : mat.range = ⊥ := by
    apply D.eq_bot_of_unipotent mat.range
    · rintro _ ⟨h, rfl⟩
      exact G.geomMat_mem _
    · intro c hc
      obtain ⟨g, rfl⟩ := G.chevSub_le_range_geomMat hc
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · rintro ⟨h, rfl⟩
        obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1 (hN geomPoint g (h ≫ i.hom.hom) trivial
          (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
        refine ⟨h', ?_⟩
        rw [hmat, hmat, hh', map_mul, map_mul, map_inv]
      · rintro ⟨h, hh⟩
        obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1 (hN geomPoint g⁻¹ (h ≫ i.hom.hom) trivial
          (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
        refine ⟨h', ?_⟩
        rw [hmat, hh', map_mul, map_mul, map_inv, inv_inv, ← hmat, hh]
        group
    · rintro _ ⟨h, rfl⟩
      have hu := MatrixRepresentation.pointMatrix_sub_one_pow_eq_zero_of_isUnipotent hU
        (G.geomRep.restrict i) geomPoint h
      rw [MatrixRepresentation.pointMatrix_restrict] at hu
      rw [hmat, geomMat_eq_pointMatrix]
      set f := (specRingEquiv k (AlgebraicClosure k)).toRingHom
      have hmap : ∀ M : GL (Fin D.n) Γ((geomPoint (k := k)).left, ⊤),
          ((Matrix.GeneralLinearGroup.map f M : GL (Fin D.n) (AlgebraicClosure k)) :
            Matrix (Fin D.n) (Fin D.n) (AlgebraicClosure k)) =
            f.mapMatrix (M : Matrix (Fin D.n) (Fin D.n) Γ((geomPoint (k := k)).left, ⊤)) :=
        fun _ => rfl
      rw [hmap, ← map_one f.mapMatrix, ← map_sub, ← map_pow, hu, map_zero]
  have hpt : ∀ h : geomPoint (k := k) ⟶ R.X, h ≫ i.hom.hom = 1 := by
    intro h
    apply G.geomMat_injective
    rw [map_one, ← hmat]
    have : mat h ∈ mat.range := ⟨h, rfl⟩
    rw [hNbot] at this
    exact this
  have : Smooth R.X.hom := hS
  have : IsReduced R.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (AlgebraicClosure k) _ R.X.hom
  have : IsAffineHom G.H.X.hom := G.affine
  have : IsSeparated G.geomGroup.X.hom := by
    change IsSeparated (pullback.snd G.H.X.hom (toAlgebraicClosure k))
    infer_instance
  have hi1 : i.hom.hom = 1 := by
    apply ext_of_extPoints (k := AlgebraicClosure k) (AlgebraicClosure k)
    intro x
    rw [MonObj.comp_one]
    have hx : x = (geomPointIso (k := k)).hom ≫ ((geomPointIso (k := k)).inv ≫ x) := by
      rw [Iso.hom_inv_id_assoc]
    rw [hx, Category.assoc, hpt, MonObj.comp_one]
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [hi1, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
