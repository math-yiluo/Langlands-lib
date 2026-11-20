import Langlands.GroupScheme.Trigonalizable.StableLines
import Langlands.GroupScheme.Absolute.TriangularDiagonalImageReduction
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition

/-! # Trigonalizable groups and unipotent quotients (Milne 16.2, (c) ⇒ (d) ⇒ (a))

A closed subgroup `G` of the upper triangular group `T_N` maps to the diagonal torus. The image
of this map is a closed diagonalizable subgroup `D(Λ)`, and `G ⟶ D(Λ)` is an fppf quotient by
the kernel. The kernel is a closed subgroup of the unitriangular group, hence unipotent.

Conversely, let `U` be a normal unipotent closed subgroup of `G` with an fppf quotient
`G ⟶ D(Λ)`. For a nonzero representation of `G`, the vectors fixed by `U` form a nonzero
subrepresentation on which `U` acts trivially. That subrepresentation descends to `D(Λ)`, whose
representations are spanned by character spaces. A nonzero vector of a character space spans a
stable line.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace Trigonalizable

variable {k : Type u} [Field k]

section TriangularToUnipotent

/-- The kernel of the diagonal projection of a closed subgroup of the upper triangular group
is unipotent, once the kernel inclusion is closed: it is a closed subgroup of the unitriangular
group. -/
theorem isUnipotent_kernel_diagonal {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
    (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hj : IsClosedSubgroup j)
    (hker : IsClosedSubgroup (kernelι (j ≫
      GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) (fun i => -(i.val : ℤ))))) :
    IsUnipotent (kernel (j ≫
      GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) (fun i => -(i.val : ℤ)))) := by
  let weights : Fin N → ℤ := fun i => -(i.val : ℤ)
  let d := GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) weights
  let f := j ≫ d
  let a : kernel f ⟶ kernel d :=
    pullback.lift (kernelι f ≫ j) (pullback.snd f (kernelUnit _)) (by
      change (pullback.fst f (kernelUnit _) ≫ j) ≫ d = _
      rw [Category.assoc, pullback.condition]
      rfl)
  have ha : a ≫ kernelι d = kernelι f ≫ j := pullback.lift_fst _ _ _
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion (kernelι f).hom.hom.left := hker
  have ha_closed : IsClosedImmersion a.hom.hom.left := by
    have : IsClosedImmersion (a.hom.hom.left ≫ (kernelι d).hom.hom.left) := by
      change IsClosedImmersion ((a ≫ kernelι d).hom.hom.left)
      rw [ha]
      change IsClosedImmersion ((kernelι f).hom.hom.left ≫ j.hom.hom.left)
      infer_instance
    exact IsClosedImmersion.of_comp a.hom.hom.left (kernelι d).hom.hom.left
  let e := GeneralLinear.blockUnipotentIsoKernel (Fin N) (CommRingCat.of k) weights
  let w := a ≫ e.inv
  have hw : IsClosedSubgroup w := by
    have : IsClosedImmersion a.hom.hom.left := ha_closed
    have : IsIso e.inv.hom.hom.left :=
      ((Grp.forget (Over _)) ⋙ Over.forget _).map_isIso e.inv
    change IsClosedImmersion (a.hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  have : IsClosedImmersion (GeneralLinear.blockUnipotentHom
      (Fin N) (CommRingCat.of k) weights).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockUnipotentHom _ _ _
  have : IsAffineHom (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  have : IsAffineHom
      (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) weights).X.hom := by
    have h : IsAffineHom ((GeneralLinear.blockUnipotentHom
        (Fin N) (CommRingCat.of k) weights).hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  have : LocallyOfFiniteType
      (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) weights).X.hom := by
    have : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
      GeneralLinear.smoothStatement _ _
    have h : LocallyOfFiniteType ((GeneralLinear.blockUnipotentHom
        (Fin N) (CommRingCat.of k) weights).hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  exact unipotentClosedSubgroup k _ (kernel f) w hw (unitriangularUnipotent k N)

/-- Milne 16.2, (c) ⇒ (d): a closed subgroup of the upper triangular group has a normal
unipotent closed subgroup, the kernel of the diagonal projection, with an fppf quotient onto
a diagonalizable group. -/
theorem exists_unipotent_diagonalizable_quotient_of_closed_triangular
    {G : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G.X.hom] {N : ℕ}
    (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))
    (hj : IsClosedSubgroup j) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
      (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ)
      (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      IsClosedSubgroup i ∧ IsUnipotent U ∧ (SubgroupFunctor.range i).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  let weights : Fin N → ℤ := fun i => -(i.val : ℤ)
  obtain ⟨Λ, hΛ, hΛfg, d, q, -, -, hq⟩ :=
    DiagonalImageReduction.exists_triangular_diagonalizable_factorization
      affineHomImage Diagonalizable.closedSubgroupPresentation k G N j
  let f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) weights
  have he : Function.Injective weights := by
    intro i l h
    apply Fin.ext
    exact Int.ofNat_inj.mp (neg_injective h)
  have hT : IsSplitTorus
      (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) weights) :=
    ⟨ULift.{u} (Fin N), inferInstance,
      ⟨(GeneralLinear.diagonalTorusIso weights he (CommRingCat.of k)).symm⟩⟩
  have : IsAffineHom
      (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) weights).X.hom :=
    hT.isAffineHom
  have hker : IsClosedSubgroup (kernelι f) := by
    change IsClosedImmersion (kernelι f).hom.hom.left
    infer_instance
  exact ⟨kernel f, kernelι f, Λ, hΛ, hΛfg, q, hker, isUnipotent_kernel_diagonal j hj hker,
    HopfPrimitive.isNormal_range_kernelι f, hq⟩

end TriangularToUnipotent

section UnipotentToTrigonalizable

/-- A nonzero vector of a character space spans a stable subspace. -/
theorem isStableSubspace_span_of_mem_characterSpace
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n] {ρ : MatrixRepresentation G n}
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ) :
    ρ.IsStableSubspace (k ∙ v) := by
  intro A x w hw ℓ
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hc := characterSpace_affine hv A x
  set c : A := (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A)
  have hs (t : k) (b : A) : ℓ (algebraMap k A t * b) = t * ℓ b := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hav : (fun i => algebraMap k A ((a • v) i)) =
      algebraMap k A a • fun i => algebraMap k A (v i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [hav, Matrix.mulVec_smul, hc]
  refine Submodule.mem_span_singleton.mpr ⟨a * ℓ c, ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show algebraMap k A a * (c * algebraMap k A (v i)) =
      algebraMap k A (a * v i) * c by rw [map_mul]; ring, hs]
  ring

/-- Every nonzero representation of a diagonalizable group has a stable line, spanned by a
nonzero vector of one of its character spaces. -/
theorem exists_stableLine_diagonalizable (Λ : Type u) [AddCommGroup Λ]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (τ : MatrixRepresentation (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp n) :
    ∃ v : n → k, v ≠ 0 ∧ τ.IsStableLine v := by
  have hχ : ∃ χ, τ.characterSpace χ ≠ ⊥ := by
    by_contra h
    push Not at h
    have htop := iSup_characterSpace_eq_top_diagonalizable Λ τ
    simp only [h, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨χ, hχ⟩ := hχ
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  exact ⟨v, hv0, isStableLine_of_isStableSubspace
    (isStableSubspace_span_of_mem_characterSpace hv)⟩

/-- Milne 16.2, (d) ⇒ (a): a group with a normal unipotent closed subgroup whose fppf
quotient is diagonalizable is trigonalizable. -/
theorem isTrigonalizable_of_unipotent_diagonalizable_quotient
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G)
    {Λ : Type u} [AddCommGroup Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    IsTrigonalizable G := by
  intro n _ _ _ ρ
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom U.X.hom := by
    have h : IsAffineHom (i.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  let D := normalFixedSubrepresentation ρ i hN
  obtain ⟨v₀, hv₀, hfix⟩ := hU n (ρ.restrict i)
  have hd : D.dimension ≠ 0 := by
    intro h0
    have : IsEmpty (Fin D.dimension) := by
      rw [h0]
      infer_instance
    apply hv₀
    rw [← D.projection v₀ hfix]
    funext r
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have : Nonempty (Fin D.dimension) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hk : kernelι q ≫ D.representation = 0 := by
    apply Grp.hom_ext
    change (kernelι q).hom.hom ≫ D.representation.hom.hom = 1
    obtain ⟨h, hh⟩ : (kernelι q).hom.hom ∈ (SubgroupFunctor.range i).carrier (kernel q).X := by
      rw [← hq.2.2.2]
      exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    have hh' : h ≫ i.hom.hom = (kernelι q).hom.hom := hh
    have h1 := D.kills_subgroup (kernel q).X h
    rw [hh', pointMatrix_apply, ← map_one (GeneralLinear.pointsEquiv _ _ (kernel q).X)] at h1
    exact (GeneralLinear.pointsEquiv _ _ _).injective h1
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact q.hom.hom.left := by
    have : QuasiCompact (q.hom.hom.left ≫
        (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _
      (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X.hom
  let τ : MatrixRepresentation (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
      (Fin D.dimension) := FpqcHomDescent.hom q D.representation hk
  obtain ⟨w, hw0, hw⟩ := exists_stableLine_diagonalizable Λ τ
  have hwD : D.representation.IsStableLine w := by
    have h := hw.restrict q
    rwa [restrict, FpqcHomDescent.fac] at h
  refine ⟨D.inclusion *ᵥ w, fun h0 => hw0 ?_, hwD.of_intertwines D.intertwines⟩
  have h := congrArg (fun u => D.retraction *ᵥ u) h0
  simpa only [Matrix.mulVec_mulVec, D.left_inverse, Matrix.one_mulVec,
    Matrix.mulVec_zero] using h

end UnipotentToTrigonalizable

end Trigonalizable

end Langlands.GroupScheme
