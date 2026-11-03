import Langlands.GroupScheme.Absolute.AlgebraicClosurePoint
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.GeneralLinearBorelCoordinates
import Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Reductive.GeneralLinearMaximal
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.Group.GL.UpperTriangularSolvable
import Langlands.Group.GL.UpperTriangularMaximalSolvable
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-! # The upper triangular Borel subgroup of `GL_N`

For a field `k` and a strictly decreasing weight vector `e : Fin N → ℤ`, the block parabolic
subgroup scheme of `e` (the invertible upper triangular matrices) is a Borel subgroup of `GL_N`
over `k`, it contains the diagonal torus, it represents `P(λ)` for the diagonal cocharacter `λ`
of `e`, and this cocharacter is regular.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear.UpperTriangular

open Langlands.GeneralLinear (upperTriangularSubgroup mem_upperTriangularSubgroup_iff)

section Points

variable {N : ℕ} {R : CommRingCat.{u}} {e : Fin N → ℤ}

/-- For a strictly decreasing weight vector, the points of the block parabolic subgroup functor
have upper triangular matrices. -/
theorem pointsEquiv_mem_upperTriangularSubgroup (he : StrictAnti e) {T : Over (Spec R)}
    {x : T ⟶ (groupScheme (Fin N) R).X} (hx : x ∈ (blockParabolic (Fin N) R e).carrier T) :
    pointsEquiv (Fin N) R T x ∈ upperTriangularSubgroup N Γ(T.left, ⊤) :=
  (mem_upperTriangularSubgroup_iff _).2 fun a b hba => (mem_blockParabolic e).1 hx a b (he hba)

/-- For a strictly decreasing weight vector, the points of `GL_N` with upper triangular matrices
lie in the block parabolic subgroup functor. -/
theorem mem_blockParabolic_of_mem_upperTriangularSubgroup (he : StrictAnti e) {T : Over (Spec R)}
    {x : T ⟶ (groupScheme (Fin N) R).X}
    (hx : pointsEquiv (Fin N) R T x ∈ upperTriangularSubgroup N Γ(T.left, ⊤)) :
    x ∈ (blockParabolic (Fin N) R e).carrier T :=
  (mem_blockParabolic e).2 fun a b hab =>
    (mem_upperTriangularSubgroup_iff _).1 hx a b (he.lt_iff_gt.mp hab)

/-- For a strictly decreasing weight vector, the group of points of the block parabolic subgroup
scheme over any test scheme is solvable. -/
theorem isSolvable_points (he : StrictAnti e) (T : Over (Spec R)) :
    Group.IsSolvable (T ⟶ (blockParabolicScheme (Fin N) R e).X) := by
  have hi := isRepresentedBy_blockParabolic (Fin N) R e
  let φ : (T ⟶ (blockParabolicScheme (Fin N) R e).X) →* upperTriangularSubgroup N Γ(T.left, ⊤) :=
    ((pointsEquiv (Fin N) R T).toMonoidHom.comp
        (((blockParabolic (Fin N) R e).carrier T).subtype.comp
          (SubgroupFunctor.IsRepresentedBy.pointsEquiv hi T).toMonoidHom)).codRestrict _
      fun x => pointsEquiv_mem_upperTriangularSubgroup he (SubgroupFunctor.IsRepresentedBy.pointsEquiv hi T x).2
  have : Group.IsSolvable (upperTriangularSubgroup N Γ(T.left, ⊤)) :=
    Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable N _
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y h => ?_
  apply (SubgroupFunctor.IsRepresentedBy.pointsEquiv hi T).injective
  apply Subtype.ext
  exact (pointsEquiv (Fin N) R T).injective (congrArg Subtype.val h)

variable (N R e) in
/-- The diagonal torus of `GL_N` factors through the block parabolic subgroup scheme. -/
theorem exists_diagonalTorus_factor :
    ∃ f : (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin N))).toGrp ⟶
        blockParabolicScheme (Fin N) R e,
      f ≫ blockParabolicHom (Fin N) R e = diagonalTorus (Fin N) R := by
  have hi := isRepresentedBy_blockParabolic (Fin N) R e
  have hd : (SubgroupFunctor.range (diagonalTorus (Fin N) R)).IsRepresentedBy
      (diagonalTorus (Fin N) R) := ⟨inferInstance, rfl⟩
  have hle : ∀ T, (SubgroupFunctor.range (diagonalTorus (Fin N) R)).carrier T ≤
      (blockParabolic (Fin N) R e).carrier T := by
    rintro T _ ⟨x, rfl⟩
    refine (mem_blockParabolic e).2 fun a b hab => ?_
    change (pointsEquiv (Fin N) R T (x ≫ (diagonalTorus (Fin N) R).hom.hom) :
      Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) a b = 0
    rw [pointsEquiv_diagonalTorus_val
      (x := (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (Fin N))).X))]
    exact Matrix.diagonal_apply_ne _ (ne_of_apply_ne e hab.ne)
  exact ⟨SubgroupFunctor.IsRepresentedBy.lift hd hi (fun T => Subgroup.inclusion (hle T))
      (fun _ _ => rfl),
    SubgroupFunctor.IsRepresentedBy.lift_comp_eq hd hi _ (fun _ _ => rfl) (fun _ _ => rfl)⟩

end Points

/-- A solvable subgroup of `GL_N(A)` containing the upper triangular matrices, for a ring `A`
isomorphic to an infinite field, consists of upper triangular matrices. -/
theorem le_upperTriangularSubgroup_of_ringEquiv {N : ℕ} {A F : Type u} [CommRing A] [Field F]
    [Infinite F] (ψ : A ≃+* F) (H : Subgroup (GL (Fin N) A))
    (hUH : upperTriangularSubgroup N A ≤ H) (hH : Group.IsSolvable H) :
    H ≤ upperTriangularSubgroup N A := by
  let Φ : GL (Fin N) A →* GL (Fin N) F := Matrix.GeneralLinearGroup.map ψ.toRingHom
  let Ψ : GL (Fin N) F →* GL (Fin N) A := Matrix.GeneralLinearGroup.map ψ.symm.toRingHom
  have hΦΨ : ∀ g, Φ (Ψ g) = g := fun g => by
    ext i j
    simp [Φ, Ψ]
  have hsol : Group.IsSolvable (H.map Φ) :=
    Group.isSolvable_of_surjective (Φ.subgroupMap_surjective H)
  have hle : upperTriangularSubgroup N F ≤ H.map Φ := by
    intro g hg
    refine ⟨Ψ g, hUH ?_, hΦΨ g⟩
    rw [mem_upperTriangularSubgroup_iff] at hg ⊢
    intro i j hji
    simp [Ψ, hg i j hji]
  have heq := Langlands.GeneralLinear.UpperTriangularMaximalSolvable.eq_upper_of_isSolvable
    (H.map Φ) hle hsol
  intro h hh
  have hΦ : Φ h ∈ upperTriangularSubgroup N F := heq ▸ ⟨h, hh, rfl⟩
  rw [mem_upperTriangularSubgroup_iff] at hΦ ⊢
  intro i j hji
  have h0 := hΦ i j hji
  simpa [Φ] using h0

section Field

variable (k : Type u) [Field k] {N : ℕ} {e : Fin N → ℤ}

/-- For a strictly decreasing weight vector, the block parabolic subgroup scheme over a field is
solvable. -/
theorem isSolvableGroupScheme_blockParabolicScheme (he : StrictAnti e) :
    IsSolvableGroupScheme (blockParabolicScheme (Fin N) (CommRingCat.of k) e) := by
  have := isSolvable_points he ((Over.map (toAlgebraicClosure k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))
  exact Group.isSolvable_of_isSolvable_injective
    (f := (baseChangePointsEquiv (toAlgebraicClosure k)
      (blockParabolicScheme (Fin N) (CommRingCat.of k) e)
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).toMonoidHom)
    (baseChangePointsEquiv (toAlgebraicClosure k) _ _).injective

/-- The cocharacter of the diagonal torus with weights `e` is regular when `e` is strictly
decreasing: it pairs with the root `eᵢ - eⱼ` to `e i - e j ≠ 0`. -/
theorem isRegularCocharacter_diagonalTorus (he : StrictAnti e) :
    IsRegularCocharacter (diagonalTorus (Fin N) (CommRingCat.of k))
      ((splitTorus.cocharacterLatticeEquiv k (ULift.{u} (Fin N))).symm fun i => e i.down) := by
  intro α hα
  rw [roots_diagonalTorus] at hα
  obtain ⟨a, b, hab, hα⟩ := hα
  rw [splitTorus.latticePairing_eq_sum, hα, AddEquiv.apply_symm_apply]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sub_ne_zero.mpr (he.injective.ne hab)

/-- The algebraic closure `Spec k̄ ⟶ Spec k` as a test scheme over `Spec k`. -/
abbrev closurePoint : Over (Spec (CommRingCat.of k)) :=
  algebraicClosurePoint k

variable {k} {B' : GroupScheme (Spec (CommRingCat.of k))}
  (i' : B' ⟶ groupScheme (Fin N) (CommRingCat.of k))
  (f : blockParabolicScheme (Fin N) (CommRingCat.of k) e ⟶ B')

/-- If `B'` is solvable and the upper triangular subgroup factors through `i' : B' ⟶ GL_N`, then
the `k̄`-points of `B'` have upper triangular matrices. -/
theorem closurePoint_mem (he : StrictAnti e) (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = blockParabolicHom (Fin N) (CommRingCat.of k) e)
    (x : closurePoint k ⟶ B'.X) :
    x ≫ i'.hom.hom ∈ (blockParabolic (Fin N) (CommRingCat.of k) e).carrier (closurePoint k) := by
  let ρ : (closurePoint k ⟶ B'.X) →* GL (Fin N) Γ((closurePoint k).left, ⊤) :=
    (pointsEquiv (Fin N) _ (closurePoint k)).toMonoidHom.comp
      ((yonedaGrp.map i').app (op (closurePoint k))).hom
  have hsolv : Group.IsSolvable ρ.range := by
    have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj B').X) := hsol
    have : Group.IsSolvable (closurePoint k ⟶ B'.X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (baseChangePointsEquiv (toAlgebraicClosure k) B'
          (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).symm.toMonoidHom)
        (baseChangePointsEquiv (toAlgebraicClosure k) B' _).symm.injective
    exact Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hfi : f.hom.hom ≫ i'.hom.hom = (blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom := by
    rw [← hf]
    rfl
  have hUT : upperTriangularSubgroup N Γ((closurePoint k).left, ⊤) ≤ ρ.range := by
    intro g hg
    have hp : (pointsEquiv (Fin N) _ (closurePoint k)).symm g ∈
        (blockParabolic (Fin N) (CommRingCat.of k) e).carrier (closurePoint k) :=
      mem_blockParabolic_of_mem_upperTriangularSubgroup he (by rwa [MulEquiv.apply_symm_apply])
    rw [← (isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) e).2] at hp
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hp
    refine ⟨y ≫ f.hom.hom, ?_⟩
    change pointsEquiv (Fin N) _ (closurePoint k) ((y ≫ f.hom.hom) ≫ i'.hom.hom) = g
    rw [Category.assoc, hfi, hy, MulEquiv.apply_symm_apply]
  have hle := le_upperTriangularSubgroup_of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).commRingCatIsoToRingEquiv
    ρ.range hUT hsolv
  exact mem_blockParabolic_of_mem_upperTriangularSubgroup he (hle ⟨x, rfl⟩)

/-- If `B'` is smooth and solvable and the upper triangular subgroup factors through
`i' : B' ⟶ GL_N`, then the universal point of `B'` has upper triangular matrix. -/
theorem universal_mem (he : StrictAnti e) (hsm : Smooth B'.X.hom)
    (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = blockParabolicHom (Fin N) (CommRingCat.of k) e) :
    i'.hom.hom ∈ (blockParabolic (Fin N) (CommRingCat.of k) e).carrier B'.X := by
  refine (mem_blockParabolic e).2 fun a b hab => ?_
  set s := pointsEquiv (Fin N) (CommRingCat.of k) B'.X i'.hom.hom a b
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
    let x' : closurePoint k ⟶ B'.X := Over.homMk x.1 (by simpa using x.2)
    have h0 := (mem_blockParabolic e).1 (closurePoint_mem i' f he hsol hf x') a b hab
    rw [pointsEquiv_comp_apply] at h0
    have hx : x' ≫ (AffineLine.homEquiv B'.X).symm s = x' ≫ (AffineLine.homEquiv B'.X).symm 0 := by
      apply AffineLine.hom_ext
      rw [AffineLine.homEquiv_comp, AffineLine.homEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, map_zero]
      exact h0
    exact congrArg (fun m => m.left) hx
  have h : ((AffineLine.homEquiv B'.X).symm s).left = ((AffineLine.homEquiv B'.X).symm 0).left :=
    congrArg Subtype.val hφψ
  have h' : (AffineLine.homEquiv B'.X).symm s = (AffineLine.homEquiv B'.X).symm 0 :=
    Over.OverMorphism.ext h
  exact (AffineLine.homEquiv B'.X).symm.injective h'

/-- Maximality: a smooth solvable closed subgroup of `GL_N` containing the upper triangular
subgroup is the upper triangular subgroup. -/
theorem isIso_of_comp_eq_blockParabolicHom (he : StrictAnti e) (hcl : IsClosedSubgroup i')
    (hsm : Smooth B'.X.hom) (hsol : IsSolvableGroupScheme B')
    (hf : f ≫ i' = blockParabolicHom (Fin N) (CommRingCat.of k) e) : IsIso f := by
  have hi := isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) e
  have hmono : Mono i'.hom.hom := by
    have : IsClosedImmersion i'.hom.hom.left := hcl
    exact Over.mono_of_mono_left _
  have hi' : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨hmono, rfl⟩
  have hu := universal_mem i' f he hsm hsol hf
  have hle : ∀ T, (SubgroupFunctor.range i').carrier T ≤
      (blockParabolic (Fin N) (CommRingCat.of k) e).carrier T := by
    rintro T _ ⟨y, rfl⟩
    exact (blockParabolic (Fin N) (CommRingCat.of k) e).comp_mem y hu
  let g := SubgroupFunctor.IsRepresentedBy.lift hi' hi (fun T => Subgroup.inclusion (hle T))
    (fun _ _ => rfl)
  have hg : g ≫ blockParabolicHom (Fin N) (CommRingCat.of k) e = i' :=
    SubgroupFunctor.IsRepresentedBy.lift_comp_eq hi' hi _ (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply SubgroupFunctor.IsRepresentedBy.hom_ext hi'
    rw [Category.assoc, hf, hg, Category.id_comp]

variable (k) in
/-- For a strictly decreasing weight vector, the block parabolic subgroup scheme of `GL_N` over
a field is a Borel subgroup. -/
theorem isBorelSubgroup_blockParabolicHom (he : StrictAnti e) :
    IsBorelSubgroup (blockParabolicHom (Fin N) (CommRingCat.of k) e) where
  isClosedSubgroup := isClosedSubgroup_blockParabolicHom (Fin N) _ e
  smooth := smooth_blockParabolicScheme _ he
  connectedSpace := connectedSpace_blockParabolicScheme _ he
  isSolvableGroupScheme := isSolvableGroupScheme_blockParabolicScheme k he
  maximal _ i' f hcl hsm _ hsol hf := isIso_of_comp_eq_blockParabolicHom i' f he hcl hsm hsol hf

end Field

end Langlands.GroupScheme.GeneralLinear.UpperTriangular

namespace Langlands.GroupScheme

open Langlands.GroupScheme.GeneralLinear Langlands.GroupScheme.GeneralLinear.UpperTriangular in
/-- The `GL_N` case of the structure theory of Borel subgroups. -/
theorem generalLinearBorel : GeneralLinearBorelStatement.{u} := by
  intro k _ N e he
  have hB := isBorelSubgroup_blockParabolicHom k he
  exact ⟨hB, ⟨hB, isMaximalTorus_diagonalTorus (n := Fin N) k,
      exists_diagonalTorus_factor N (CommRingCat.of k) e⟩,
    isRepresentedBy_parabolic_diagonalCocharacter (Fin N) _ e,
    isRegularCocharacter_diagonalTorus k he⟩

end Langlands.GroupScheme
