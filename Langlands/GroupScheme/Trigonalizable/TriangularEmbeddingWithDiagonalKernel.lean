import Langlands.GroupScheme.Trigonalizable.StableFlag
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Absolute.TriangularCoordinateSeries
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Absolute.SolvableUnipotentAdapters

/-! # Closed triangular embeddings with diagonal kernel a given unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableFlag

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed linear embedding whose matrix at the universal point is upper triangular factors as
a closed subgroup of the upper triangular group scheme. -/
theorem exists_closed_blockParabolic_factor {N : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (h : ∀ a b : Fin N, b < a →
      (ρ.pointMatrix G.X (𝟙 G.X) : Matrix (Fin N) (Fin N) Γ(G.X.left, ⊤)) a b = 0) :
    ∃ j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
        (fun a => -(a.val : ℤ)),
      IsClosedSubgroup j ∧
        j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
          (fun a => -(a.val : ℤ)) = ρ := by
  let e : Fin N → ℤ := fun a => -(a.val : ℤ)
  have hu : ρ.hom.hom ∈
      (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).carrier G.X := by
    refine (GeneralLinear.mem_blockParabolic _).2 fun a b hab => ?_
    have hba : b < a := by
      change b.val < a.val
      simp only [e] at hab
      omega
    simpa only [pointMatrix_apply, Category.id_comp] using h a b hba
  have hmono : Mono ρ.hom.hom := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    exact Over.mono_of_mono_left _
  have hiρ : (SubgroupFunctor.range ρ).IsRepresentedBy ρ := ⟨hmono, rfl⟩
  have hi := GeneralLinear.isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) e
  have hle : ∀ T, (SubgroupFunctor.range ρ).carrier T ≤
      (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).carrier T := by
    rintro T _ ⟨x, rfl⟩
    exact (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).comp_mem x hu
  let f := SubgroupFunctor.IsRepresentedBy.lift hiρ hi
    (fun T => Subgroup.inclusion (hle T)) (fun _ _ => rfl)
  have hf : f ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e = ρ :=
    SubgroupFunctor.IsRepresentedBy.lift_comp_eq hiρ hi _ (fun _ _ => rfl)
      (fun _ _ => rfl)
  refine ⟨f, ?_, hf⟩
  have : IsClosedImmersion
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockParabolicHom (Fin N) (CommRingCat.of k) e
  have hcomp : f.hom.hom.left ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left =
      ρ.hom.hom.left := congrArg (fun a => a.hom.hom.left) hf
  have : IsClosedImmersion (f.hom.hom.left ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left) := by
    rw [hcomp]
    exact hρ
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left
    (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left

/-- Points of the actual diagonal kernel of a triangular subgroup: their matrices agree with the
identity matrix on and below the diagonal. -/
theorem mem_range_kernelι_diagonal_iff {N : ℕ}
    (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun a => -(a.val : ℤ)))
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range (kernelι (j ≫ GeneralLinear.blockLimitHom (Fin N)
        (CommRingCat.of k) (fun a => -(a.val : ℤ))))).carrier T ↔
      ∀ a b : Fin N, b ≤ a →
        (MatrixRepresentation.pointMatrix (j ≫ GeneralLinear.blockParabolicHom (Fin N)
          (CommRingCat.of k) (fun a => -(a.val : ℤ))) T x :
            Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) a b =
          (1 : Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) a b := by
  rw [← TriangularLayer.filtration_zero_eq_diagonal_kernel, TriangularLayer.mem_range_filtrationHom,
    TriangularLayer.refinedW_zero, TriangularLayer.W_zero_eq_blockUnipotentSubgroup,
    GeneralLinear.mem_blockUnipotentSubgroup]
  constructor
  · intro h a b hba
    exact h a b (by have : b.val ≤ a.val := hba; change -(a.val : ℤ) ≤ -(b.val : ℤ); omega)
  · intro h a b hab
    exact h a b (by change b.val ≤ a.val; change -(a.val : ℤ) ≤ -(b.val : ℤ) at hab; omega)


variable {U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G)
  {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
  (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- **Triangular embedding (Milne 16.2(d) ⇒ (c)).** Let `G` be an affine algebraic group over a
field, `U` a normal unipotent subgroup and `q : G ⟶ D(Λ)` an fppf quotient by `U`. Then `G` has
a closed embedding into an upper triangular group whose actual diagonal kernel is exactly `U`. -/
theorem exists_triangular_embedding [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [IsAffineHom U.X.hom] (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    ∃ (N : ℕ) (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
        (fun a => -(a.val : ℤ))),
      IsClosedSubgroup j ∧
        SubgroupFunctor.range (kernelι (j ≫ GeneralLinear.blockLimitHom (Fin N)
          (CommRingCat.of k) (fun a => -(a.val : ℤ)))) = SubgroupFunctor.range i := by
  obtain ⟨N, ρ₀, hρ₀⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨g, htri, hdiag⟩ := exists_triangular i q hU hN hq N ρ₀
  set ρ := ρ₀.conjugate (basePoint (R := CommRingCat.of k) g) with hρdef
  have hρ : IsClosedSubgroup ρ := by
    have : IsClosedImmersion ρ₀.hom.hom.left := hρ₀
    have : IsIso ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso
        (basePoint (R := CommRingCat.of k) g)).hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso _).hom.hom.hom))
    change IsClosedImmersion (ρ₀.hom.hom.left ≫ _)
    infer_instance
  obtain ⟨j, hj, hjρ⟩ := exists_closed_blockParabolic_factor ρ hρ
    (fun a b hba => htri G.X (𝟙 G.X) a b hba)
  refine ⟨N, j, hj, ?_⟩
  let e : Fin N → ℤ := fun a => -(a.val : ℤ)
  let lim := GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) e
  have : IsAffineHom (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) e).X.hom :=
    GeneralLinear.isAffineHom_blockUnipotentScheme _ _ _
  have : LocallyOfFiniteType
      (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k) e).X.hom :=
    GeneralLinear.locallyOfFiniteType_blockUnipotentScheme _ _ _
  have : IsAffineHom (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  have : IsClosedImmersion
      (GeneralLinear.blockLeviHom (Fin N) (CommRingCat.of k) e).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockLeviHom _ _ _
  have : IsAffineHom (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k) e).X.hom := by
    rw [← Over.w (GeneralLinear.blockLeviHom (Fin N) (CommRingCat.of k) e).hom.hom]
    infer_instance
  have hKu : IsUnipotent (kernel (j ≫ lim)) :=
    isUnipotent_kernel_comp_of_closedSubgroup unipotentClosedSubgroup j lim
      (GeneralLinear.blockUnipotentIsoKernel (Fin N) (CommRingCat.of k) e) hj
      (unitriangularUnipotent k N)
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom (GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k) e).X.hom := by
    have : IsClosedImmersion
        (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left :=
      GeneralLinear.isClosedSubgroup_blockParabolicHom _ _ _
    rw [← Over.w (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom]
    infer_instance
  have : IsAffineHom (kernel (j ≫ lim)).X.hom := by
    rw [← Over.w (kernelι (j ≫ lim)).hom.hom]
    infer_instance
  have : LocallyOfFiniteType (kernel (j ≫ lim)).X.hom := by
    rw [← Over.w (kernelι (j ≫ lim)).hom.hom]
    infer_instance
  have hD : IsMultiplicativeType (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp :=
    ⟨k, inferInstance, inferInstance, Λ, inferInstance, inferInstance,
      ⟨Diagonalizable.baseChangeIso _ Λ⟩⟩
  have htriv := ((unipotentMultiplicativeTriviality.{u} k).2.2 (kernel (j ≫ lim))
    (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp hKu hD).1 (kernelι (j ≫ lim) ≫ q)
  ext T x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ (kernelι (j ≫ lim) ≫ q).hom.hom ∈
        (SubgroupFunctor.range (kernelι (j ≫ lim) ≫ q)).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    rw [htriv, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
    rw [← hq.2.2.2, mem_range_kernelι_iff]
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine (mem_range_kernelι_diagonal_iff j _).2 fun a b hba => ?_
    rw [hjρ]
    rcases eq_or_lt_of_le hba with hab | hlt
    · subst hab
      rw [Matrix.one_apply_eq]
      exact hdiag T h b
    · rw [htri T _ a b hlt, Matrix.one_apply_ne (ne_of_lt hlt).symm]

end Langlands.GroupScheme.TrigonalizableFlag
