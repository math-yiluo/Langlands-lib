import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingStatement
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularizationStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.SolvablePoints
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-! # Scheme-theoretic passage from rational triangularization to a closed embedding -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom]
  {N : ℕ}

/-- An entry of a smooth group's matrix representation that vanishes on every rational
point vanishes on the universal point. -/
theorem universal_entry_eq_zero_of_rational
    (ρ : MatrixRepresentation H (Fin N)) (i j : Fin N)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X,
      ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x i j = 0) :
    (ρ.pointMatrix H.X (𝟙 H.X) :
      Matrix (Fin N) (Fin N) Γ(H.X.left, ⊤)) i j = 0 := by
  set s := (ρ.pointMatrix H.X (𝟙 H.X) :
    Matrix (Fin N) (Fin N) Γ(H.X.left, ⊤)) i j
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      H.X.left H.X.hom
  have : IsSeparated (AffineLine.scheme (Spec (CommRingCat.of k))).hom := by
    change IsSeparated (𝔸(PUnit; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    infer_instance
  let φ : NeronModelInfra.SchemeHomOver H.X.hom
      (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv H.X).symm s).left, Over.w _⟩
  let ψ : NeronModelInfra.SchemeHomOver H.X.hom
      (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv H.X).symm 0).left, Over.w _⟩
  have hφψ : φ = ψ := by
    refine SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := k) k k φ ψ fun x => ?_
    let x' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
      Over.homMk x.1 (by simpa using x.2)
    have h0 : x'.left.appTop s = 0 := by
      have hx := h x'
      simpa only [s, pointMatrix_apply, Category.id_comp,
        ← Category.assoc, GeneralLinear.pointsEquiv_comp_apply] using hx
    have hx : x' ≫ (AffineLine.homEquiv H.X).symm s =
        x' ≫ (AffineLine.homEquiv H.X).symm 0 := by
      apply AffineLine.hom_ext
      rw [AffineLine.homEquiv_comp, AffineLine.homEquiv_comp,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply, map_zero]
      exact h0
    exact congrArg (fun m => m.left) hx
  have heq : ((AffineLine.homEquiv H.X).symm s).left =
      ((AffineLine.homEquiv H.X).symm 0).left :=
    congrArg Subtype.val hφψ
  exact (AffineLine.homEquiv H.X).symm.injective (Over.OverMorphism.ext heq)

/-- Rational upper triangular matrices give all-test membership in the concrete
upper triangular subgroup. -/
theorem universal_mem_blockParabolic_of_rational
    (ρ : MatrixRepresentation H (Fin N))
    (h : ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (i j : Fin N), j < i →
        ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x i j = 0) :
    ρ.hom.hom ∈
      (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))).carrier H.X := by
  refine (GeneralLinear.mem_blockParabolic _).2 fun i j hij => ?_
  have hji : j < i := by
    change j.val < i.val
    omega
  have hz := universal_entry_eq_zero_of_rational ρ i j (fun x => h x i j hji)
  simpa only [pointMatrix_apply, Category.id_comp] using hz

/-- A closed linear embedding whose rational matrices are upper triangular factors as
a closed immersion into the existing concrete upper triangular scheme. -/
theorem exists_closed_blockParabolic_factor_of_rational
    (ρ : MatrixRepresentation H (Fin N)) (hρ : IsClosedSubgroup ρ)
    (h : ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (i j : Fin N), j < i →
        ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x i j = 0) :
    ∃ j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ)),
      IsClosedSubgroup j ∧
        j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
          (fun i => -(i.val : ℤ)) = ρ := by
  let e : Fin N → ℤ := fun i => -(i.val : ℤ)
  have hu := universal_mem_blockParabolic_of_rational ρ h
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

end MatrixRepresentation

/-- The exact embedding target follows from rational-point Lie–Kolchin triangularization. -/
theorem solvableTriangularEmbedding_of_rationalTriangularization
    (hLie : LieKolchinRationalTriangularizationStatement.{u}) :
    SolvableTriangularEmbeddingStatement.{u} := by
  intro k _ _ H _ _ _ hsol
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k H inferInstance inferInstance
  obtain ⟨g, hg⟩ := hLie k H hsol.rationalPoints N ρ
  have hρg : IsClosedSubgroup (ρ.conjugate g) := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    have : IsIso
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom))
    change IsClosedImmersion (ρ.hom.hom.left ≫ _)
    infer_instance
  obtain ⟨j, hj, -⟩ :=
    MatrixRepresentation.exists_closed_blockParabolic_factor_of_rational
      (ρ.conjugate g) hρg hg
  exact ⟨N, j, hj⟩

end Langlands.GroupScheme
