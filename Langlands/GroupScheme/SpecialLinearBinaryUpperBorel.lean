import Langlands.Group.GL.OppositeRootNonsolvable
import Langlands.Group.GL.UpperTriangularSolvable
import Langlands.GroupScheme.SpecialLinearBinaryRootGroups
import Langlands.GroupScheme.SpecialLinearBinaryUpperCoordinates
import Langlands.GroupScheme.Absolute.AlgebraicClosurePoint
import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-! # The binary upper-triangular special linear Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GeneralLinear.BinaryUpperRoot

variable {K : Type u} [Field K]

/-- Eliminate the top-left entry using an upper transvection. -/
def eliminate (g : Langlands.GeneralLinear 2 K) : Langlands.GeneralLinear 2 K :=
  transvectionUnit 0 1 (by decide) (-g 0 0 / g 1 0) * g

theorem eliminate_topLeft (g : Langlands.GeneralLinear 2 K) (hg : g 1 0 ≠ 0) :
    eliminate g 0 0 = 0 := by
  change ((Matrix.transvection (0 : Fin 2) 1 (-g 0 0 / g 1 0)) * g.val) 0 0 = 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection]
  field_simp
  ring

theorem eliminate_bottomLeft (g : Langlands.GeneralLinear 2 K) :
    eliminate g 1 0 = g 1 0 := by
  change ((Matrix.transvection (0 : Fin 2) 1 (-g 0 0 / g 1 0)) * g.val) 1 0 = g 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection]

/-- An invertible binary matrix with zero top-left entry conjugates an entire upper root
onto the lower root. -/
theorem conjugate_upper (w : Langlands.GeneralLinear 2 K)
    (h00 : w 0 0 = 0) (h10 : w 1 0 ≠ 0) (s : K) :
    w * transvectionUnit 0 1 (by decide) (s * w 0 1 / w 1 0) * w⁻¹ =
      transvectionUnit 1 0 (by decide) s := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvectionUnit, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transvection, h00]
  field_simp

/-- A subgroup containing every upper transvection and a nontriangular element contains
every lower transvection. -/
theorem lower_mem_of_nonzero (H : Subgroup (Langlands.GeneralLinear 2 K))
    (hU : ∀ c : K, transvectionUnit 0 1 (by decide) c ∈ H)
    {g : Langlands.GeneralLinear 2 K} (hg : g ∈ H) (h10 : g 1 0 ≠ 0) (s : K) :
    transvectionUnit 1 0 (by decide) s ∈ H := by
  have hw : eliminate g ∈ H := H.mul_mem (hU _) hg
  have h := H.mul_mem (H.mul_mem hw (hU (s * eliminate g 0 1 / eliminate g 1 0)))
    (H.inv_mem hw)
  rwa [conjugate_upper _ (eliminate_topLeft g h10)
    (by rwa [eliminate_bottomLeft])] at h

/-- Over an infinite field, a solvable subgroup containing the upper root consists
of upper-triangular matrices. -/
theorem lowerEntry_eq_zero [Infinite K] (H : Subgroup (Langlands.GeneralLinear 2 K))
    (hU : ∀ c : K, transvectionUnit 0 1 (by decide) c ∈ H)
    (hsol : Group.IsSolvable H) {g : Langlands.GeneralLinear 2 K} (hg : g ∈ H) :
    g 1 0 = 0 := by
  by_contra h10
  exact OppositeRootNonsolvable.not_isSolvable H 0 1 (by decide) hU
    (lower_mem_of_nonzero H hU hg h10) hsol

end Langlands.GeneralLinear.BinaryUpperRoot

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section Matrices

variable {K : Type u} [Field K] [Infinite K]

/-- The same obstruction for determinant-one binary matrices. -/
theorem lowerEntry_eq_zero_of_solvable
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (hU : ∀ c : K, Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c ∈ H)
    (hsol : Group.IsSolvable H) {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : g ∈ H) :
    g 1 0 = 0 := by
  let φ : Matrix.SpecialLinearGroup (Fin 2) K →* Langlands.GeneralLinear 2 K :=
    Matrix.SpecialLinearGroup.toGL
  have hU' : ∀ c : K, Langlands.GeneralLinear.transvectionUnit 0 1 (by decide) c ∈
      H.map φ := by
    intro c
    refine ⟨Matrix.SpecialLinearGroup.transvection (by decide) c, hU c, ?_⟩
    apply Units.ext
    rfl
  have hsol' : Group.IsSolvable (H.map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective H)
  exact Langlands.GeneralLinear.BinaryUpperRoot.lowerEntry_eq_zero (H.map φ)
    hU' hsol' ⟨g, hg, rfl⟩

end Matrices

section RingEquivalence

variable {A F : Type u} [CommRing A] [Field F] [Infinite F]

/-- The solvability obstruction also holds over any ring isomorphic to an infinite field. -/
theorem lowerEntry_eq_zero_of_ringEquiv (ψ : A ≃+* F)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) A))
    (hU : ∀ c : A, Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c ∈ H)
    (hsol : Group.IsSolvable H) {g : Matrix.SpecialLinearGroup (Fin 2) A} (hg : g ∈ H) :
    g 1 0 = 0 := by
  let Φ := (BinaryRoot.matrixRingEquiv ψ).toMonoidHom
  have hsol' : Group.IsSolvable (H.map Φ) :=
    Group.isSolvable_of_surjective (Φ.subgroupMap_surjective H)
  have hU' : ∀ c : F, Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c ∈ H.map Φ := by
    intro c
    refine ⟨Matrix.SpecialLinearGroup.transvection (by decide) (ψ.symm c), hU _, ?_⟩
    change Matrix.SpecialLinearGroup.map ψ.toRingHom _ = _
    rw [BinaryRoot.map_transvection]
    exact congrArg (Matrix.SpecialLinearGroup.transvection _) (ψ.apply_symm_apply c)
  have h0 := lowerEntry_eq_zero_of_solvable (H.map Φ) hU' hsol' ⟨g, hg, rfl⟩
  exact ψ.injective (by simpa [Φ, BinaryRoot.matrixRingEquiv] using h0)

end RingEquivalence

section Points

variable (R : CommRingCat.{u})

/-- The binary triangular point group is solvable on every relative test scheme. -/
theorem isSolvable_points (T : Over (Spec R)) :
    Group.IsSolvable (T ⟶ (groupScheme R).X) := by
  let φ₀ : (T ⟶ (groupScheme R).X) →*
      Langlands.GeneralLinear 2 Γ(T.left, ⊤) :=
    Matrix.SpecialLinearGroup.toGL.comp
      ((subgroup Γ(T.left, ⊤)).subtype.comp (pointsEquiv R T).toMonoidHom)
  have hφ : ∀ x, φ₀ x ∈ Langlands.GeneralLinear.upperTriangularSubgroup 2 Γ(T.left, ⊤) := by
    intro x i j hji
    fin_cases i <;> fin_cases j
    · exact (not_lt_of_ge le_rfl hji).elim
    · norm_num at hji
    · exact (pointsEquiv R T x).property
    · exact (not_lt_of_ge le_rfl hji).elim
  let φ := φ₀.codRestrict _ hφ
  have : Group.IsSolvable
      (Langlands.GeneralLinear.upperTriangularSubgroup 2 Γ(T.left, ⊤)) :=
    Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable 2 _
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y h => ?_
  apply (pointsEquiv R T).injective
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h)

end Points

section Field

variable (k : Type u) [Field k]

/-- Solvability of the actual binary triangular group scheme. -/
theorem isSolvableGroupScheme_groupScheme :
    IsSolvableGroupScheme (groupScheme (CommRingCat.of k)) := by
  have := isSolvable_points (CommRingCat.of k)
    ((Over.map (toAlgebraicClosure k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))
  exact Group.isSolvable_of_isSolvable_injective
    (f := (baseChangePointsEquiv (toAlgebraicClosure k) _
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).toMonoidHom)
    (baseChangePointsEquiv (toAlgebraicClosure k) _ _).injective

variable {k} {B' : GroupScheme (Spec (CommRingCat.of k))}
  (i' : B' ⟶ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
  (f : groupScheme (CommRingCat.of k) ⟶ B')

/-- Every geometric point of a solvable overgroup of the binary triangular group is triangular. -/
theorem closurePoint_lowerEntry (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = inclusion (CommRingCat.of k))
    (x : algebraicClosurePoint k ⟶ B'.X) :
    SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) (algebraicClosurePoint k)
      (x ≫ i'.hom.hom) 1 0 = 0 := by
  let T := algebraicClosurePoint k
  let ρ : (T ⟶ B'.X) →* Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤) :=
    (SpecialLinear.pointsEquiv (Fin 2) _ T).toMonoidHom.comp
      ((yonedaGrp.map i').app (op T)).hom
  have hsolv : Group.IsSolvable ρ.range := by
    have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj B').X) := hsol
    have : Group.IsSolvable (T ⟶ B'.X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (baseChangePointsEquiv (toAlgebraicClosure k) B'
          (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).symm.toMonoidHom)
        (baseChangePointsEquiv (toAlgebraicClosure k) B' _).symm.injective
    exact Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hfi : f.hom.hom ≫ i'.hom.hom = (inclusion (CommRingCat.of k)).hom.hom := by
    rw [← hf]
    rfl
  have hU : ∀ c : Γ(T.left, ⊤), Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) c ∈ ρ.range := by
    intro c
    let g : subgroup Γ(T.left, ⊤) :=
      ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c, by
        simp [mem_subgroup, Matrix.SpecialLinearGroup.transvection_coe]⟩
    let y := (pointsEquiv (CommRingCat.of k) T).symm g
    refine ⟨y ≫ f.hom.hom, ?_⟩
    change SpecialLinear.pointsEquiv (Fin 2) _ T ((y ≫ f.hom.hom) ≫ i'.hom.hom) = _
    rw [Category.assoc, hfi, pointsEquiv_inclusion]
    exact congrArg Subtype.val ((pointsEquiv (CommRingCat.of k) T).apply_symm_apply g)
  exact lowerEntry_eq_zero_of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).commRingCatIsoToRingEquiv
    ρ.range hU hsolv ⟨x, rfl⟩

/-- Smoothness upgrades triangularity of geometric points to the universal point. -/
theorem universal_mem_range (hsm : Smooth B'.X.hom)
    (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = inclusion (CommRingCat.of k)) :
    i'.hom.hom ∈ (SubgroupFunctor.range (inclusion (CommRingCat.of k))).carrier B'.X := by
  rw [mem_range_inclusion]
  set s := SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) B'.X i'.hom.hom 1 0
  have : IsReduced B'.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k B'.X.left
      B'.X.hom
  have : IsSeparated (AffineLine.scheme (Spec (CommRingCat.of k))).hom := by
    change IsSeparated (𝔸(PUnit; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    infer_instance
  let φ : NeronModelInfra.SchemeHomOver B'.X.hom (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv B'.X).symm s).left, Over.w _⟩
  let ψ : NeronModelInfra.SchemeHomOver B'.X.hom (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv B'.X).symm 0).left, Over.w _⟩
  have hφψ : φ = ψ := by
    refine SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat (R := k) k
      (AlgebraicClosure k) φ ψ fun x => ?_
    let x' : algebraicClosurePoint k ⟶ B'.X := Over.homMk x.1 (by simpa using x.2)
    have h0 := closurePoint_lowerEntry i' f hsol hf x'
    rw [SpecialLinear.pointsEquiv_naturality] at h0
    have hx : x' ≫ (AffineLine.homEquiv B'.X).symm s =
        x' ≫ (AffineLine.homEquiv B'.X).symm 0 := by
      apply AffineLine.hom_ext
      rw [AffineLine.homEquiv_comp, AffineLine.homEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, map_zero]
      exact h0
    exact congrArg (fun m => m.left) hx
  have h : ((AffineLine.homEquiv B'.X).symm s).left =
      ((AffineLine.homEquiv B'.X).symm 0).left := congrArg Subtype.val hφψ
  have h' : (AffineLine.homEquiv B'.X).symm s = (AffineLine.homEquiv B'.X).symm 0 :=
    Over.OverMorphism.ext h
  exact (AffineLine.homEquiv B'.X).symm.injective h'

/-- A smooth solvable closed overgroup of the binary triangular group equals that group. -/
theorem isIso_of_comp_eq_inclusion (hcl : IsClosedSubgroup i')
    (hsm : Smooth B'.X.hom) (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = inclusion (CommRingCat.of k)) : IsIso f := by
  have hi : (SubgroupFunctor.range (inclusion (CommRingCat.of k))).IsRepresentedBy
      (inclusion (CommRingCat.of k)) :=
    ⟨Corepresented.mono_cutHom (isCutOutBy (CommRingCat.of k)), rfl⟩
  have hmono : Mono i'.hom.hom := by
    have : SurjectiveOnStalks i'.hom.hom.left := hcl.toSurjectiveOnStalks
    have : Mono i'.hom.hom.left :=
      SurjectiveOnStalks.mono_of_injective hcl.isClosedEmbedding.injective
    exact Over.mono_of_mono_left _
  have hi' : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨hmono, rfl⟩
  have hu := universal_mem_range i' f hsm hsol hf
  have hle : ∀ T, (SubgroupFunctor.range i').carrier T ≤
      (SubgroupFunctor.range (inclusion (CommRingCat.of k))).carrier T := by
    rintro T _ ⟨y, rfl⟩
    exact (SubgroupFunctor.range (inclusion (CommRingCat.of k))).comp_mem y hu
  let g := SubgroupFunctor.IsRepresentedBy.lift hi' hi
    (fun T => Subgroup.inclusion (hle T)) (fun _ _ => rfl)
  have hg : g ≫ inclusion (CommRingCat.of k) = i' :=
    SubgroupFunctor.IsRepresentedBy.lift_comp_eq hi' hi _ (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi'
    rw [Category.assoc, hf, hg, Category.id_comp]

variable (k) in
/-- The actual upper-triangular binary special linear group is a Borel subgroup over every field. -/
theorem isBorelSubgroup_inclusion :
    IsBorelSubgroup (inclusion (CommRingCat.of k)) where
  isClosedSubgroup := isClosedSubgroup_inclusion _
  smooth := Coordinates.smooth_groupScheme _
  connectedSpace := Coordinates.connectedSpace_groupScheme _
  isSolvableGroupScheme := isSolvableGroupScheme_groupScheme k
  maximal _ i' f hcl hsm _ hsol hf := isIso_of_comp_eq_inclusion i' f hcl hsm hsol hf

variable (k) in
/-- The explicit triangular inclusion, packaged with its proved Borel property. -/
def borelRepresentative :
    {i : groupScheme (CommRingCat.of k) ⟶ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) //
      IsBorelSubgroup i} :=
  ⟨inclusion (CommRingCat.of k), isBorelSubgroup_inclusion k⟩

end Field

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
