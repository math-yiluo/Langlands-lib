import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Dimension transfer through flat unramified algebras -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory Module TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar induction using the actual algebra tensor module. -/
noncomputable def algebraInductionFunctor (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp f.hom g.hom

instance algebraInductionFunctor_additive : (algebraInductionFunctor R S).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add (A := S) (f := f.hom) (g := g.hom)

instance algebraInductionFunctor_preservesProjectiveObjects :
    (algebraInductionFunctor R S).PreservesProjectiveObjects where
  projective_obj M {proj} := by
    have : Module.Projective R M := ModuleCat.projective_of_module_projective M
    have : Module.Projective S (S ⊗[R] M) := inferInstance
    exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of S (S ⊗[R] M))

/-- Flat scalar induction preserves the actual short exact sequence. -/
theorem algebraInductionFunctor_shortExact [Module.Flat R S]
    {T : ShortComplex (ModuleCat.{u} R)} (hT : T.ShortExact) :
    (T.map (algebraInductionFunctor R S)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact Module.Flat.lTensor_exact S
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).1 hT.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap T.f.hom hT.moduleCat_injective_f
  · exact LinearMap.lTensor_surjective S hT.moduleCat_surjective_g

/-- Flat scalar induction preserves any finite projective-dimension bound. -/
theorem algebraInduction_hasProjectiveDimensionLE [Module.Flat R S] (n : ℕ)
    (M : ModuleCat.{u} R) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((algebraInductionFunctor R S).obj M) n := by
  induction n generalizing M with
  | zero =>
    have h : Projective M := projective_iff_hasProjectiveDimensionLT_one.2 ‹_›
    have : Projective ((algebraInductionFunctor R S).obj M) :=
      (algebraInductionFunctor R S).projective_obj_of_projective h
    infer_instance
  | succ n ih =>
    obtain ⟨⟨P, f⟩⟩ := ModuleCat.enoughProjectives.1 M
    let T := ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    have hTS := algebraInductionFunctor_shortExact (S := S) hT
    have hP : Projective (T.map (algebraInductionFunctor R S)).X₂ :=
      (algebraInductionFunctor R S).projective_obj _
    have := (hT.hasProjectiveDimensionLT_X₃_iff n ‹_›).1 ‹_›
    exact (hTS.hasProjectiveDimensionLT_X₃_iff n hP).2 (ih (Limits.kernel f))

/-- The complementary diagonal idempotent has multiplication one and equal
left and right scalar actions. -/
theorem exists_unramifiedDiagonal [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    ∃ e : S ⊗[R] S, Algebra.TensorProduct.lmul' R e = (1 : S) ∧
      ∀ s : S, ((1 : S) ⊗ₜ[R] s) * e = (s ⊗ₜ[R] (1 : S)) * e := by
  obtain ⟨d, hd, hI⟩ : ∃ d, IsIdempotentElem d ∧
      KaehlerDifferential.ideal R S = S ⊗[R] S ∙ d :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[S⁄R]
  have hdI : d ∈ KaehlerDifferential.ideal R S := by
    rw [hI]
    exact Submodule.mem_span_singleton_self d
  have hd0 : Algebra.TensorProduct.lmul' R d = (0 : S) := hdI
  have hkill (x : S ⊗[R] S) (hx : x ∈ KaehlerDifferential.ideal R S) :
      x * (1 - d) = 0 := by
    rw [hI, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    calc
      d * a * (1 - d) = a * (d - d * d) := by ring
      _ = 0 := by rw [hd]; ring
  refine ⟨1 - d, by simp [hd0], fun s => ?_⟩
  have h := hkill _ (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s)
  exact sub_eq_zero.1 (by simpa only [sub_mul] using h)

section ModuleSection

variable (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- A diagonal tensor acts on a vector by `a ⊗ b ↦ (m ↦ a ⊗ b • m)`. -/
noncomputable def diagonalTensorMap : S ⊗[R] S →ₗ[S] (M →ₗ[R] S ⊗[R] M) :=
  AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun b =>
            (TensorProduct.mk R S M a).comp (Algebra.lsmul R R M b)
          map_add' := by intro b c; ext m; simp [tmul_add]
          map_smul' := by
            intro r b
            ext m
            simp }
      map_add' := by intro a b; ext c m; simp
      map_smul' := by intro a b; ext c m; simp [smul_tmul'] }

@[simp]
theorem diagonalTensorMap_tmul (a b : S) (m : M) :
    diagonalTensorMap M (a ⊗ₜ[R] b) m = a ⊗ₜ[R] (b • m) := rfl

theorem diagonalTensorMap_left (s : S) (x : S ⊗[R] S) (m : M) :
    diagonalTensorMap M ((s ⊗ₜ[R] (1 : S)) * x) m =
      s • diagonalTensorMap M x m := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [mul_add, hx, hy, smul_add]

theorem diagonalTensorMap_right (s : S) (x : S ⊗[R] S) (m : M) :
    diagonalTensorMap M (((1 : S) ⊗ₜ[R] s) * x) m =
      diagonalTensorMap M x (s • m) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_smul, smul_comm s b]
  | add x y hx hy => simp [mul_add, hx, hy]

/-- The actual multiplication map on the induced module. -/
noncomputable def algebraInductionCounit : S ⊗[R] M →ₗ[S] M :=
  (LinearMap.id (R := R) (M := M)).liftBaseChange S

theorem algebraInductionCounit_diagonal (x : S ⊗[R] S) (m : M) :
    algebraInductionCounit M (diagonalTensorMap M x m) =
      Algebra.TensorProduct.lmul' R x • m := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [algebraInductionCounit, mul_smul]
  | add x y hx hy => simp [hx, hy, add_smul]

/-- A tensor with equal diagonal actions defines an `S`-linear section. -/
noncomputable def diagonalModuleSection (e : S ⊗[R] S)
    (hc : ∀ s : S, ((1 : S) ⊗ₜ[R] s) * e = (s ⊗ₜ[R] (1 : S)) * e) :
    M →ₗ[S] S ⊗[R] M where
  toFun := diagonalTensorMap M e
  map_add' := (diagonalTensorMap M e).map_add
  map_smul' s m := by
    change diagonalTensorMap M e (s • m) = s • diagonalTensorMap M e m
    rw [← diagonalTensorMap_right M s e m, hc s, diagonalTensorMap_left]

/-- Every module over an essentially finite-type unramified algebra is a
retract, over that algebra, of its scalar induction from the coefficient ring. -/
theorem exists_algebraInduction_retract [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    Nonempty (Retract (ModuleCat.of S M) (ModuleCat.of S (S ⊗[R] M))) := by
  obtain ⟨e, he, hc⟩ := exists_unramifiedDiagonal (R := R) (S := S)
  refine ⟨{ i := ModuleCat.ofHom (diagonalModuleSection M e hc)
            r := ModuleCat.ofHom (algebraInductionCounit M)
            retract := ?_ }⟩
  ext m
  change algebraInductionCounit M (diagonalTensorMap M e m) = m
  rw [algebraInductionCounit_diagonal, he, one_smul]

end ModuleSection

/-- Flat, essentially finite-type unramified scalar extension does not increase
the projective dimension of a module with its specified algebra action. -/
theorem hasProjectiveDimensionLE_of_flat_unramified [Module.Flat R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasProjectiveDimensionLE (ModuleCat.of S M) n := by
  have : HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) n :=
    algebraInduction_hasProjectiveDimensionLE (S := S) n (ModuleCat.of R M)
  obtain ⟨h⟩ := exists_algebraInduction_retract (R := R) (S := S) M
  exact h.hasProjectiveDimensionLT (n + 1)

end Langlands.CommutativeAlgebra
