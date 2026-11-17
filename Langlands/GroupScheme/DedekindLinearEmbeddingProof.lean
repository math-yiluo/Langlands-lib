import Langlands.GroupScheme.DedekindLinearEmbeddingStatement
import Langlands.GroupScheme.IntegralLinearEmbedding.ClosedEmbedding
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.Projective
import Langlands.Algebra.HopfPointWeightWindow

/-! # Closed linear embeddings over Dedekind domains

Extend a finite projective subcomodule of the coordinate bialgebra to a finite free
comodule, and use its matrix coefficients in the published affine embedding construction.
-/

noncomputable section

universe u

open TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.DedekindLinearEmbedding

open Langlands.Algebra.HopfPointWeightWindow

variable {R B V F : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
  [AddCommGroup V] [Module R V] [AddCommGroup F] [Module R F]

/-- Contraction of a right coaction with the counit. -/
def contractCounit : V ⊗[R] B →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ (counit (R := R) (A := B)).lTensor V

@[simp] theorem contractCounit_tmul (v : V) (b : B) :
    contractCounit (v ⊗ₜ[R] b) = counit (R := R) b • v := rfl

theorem contractCounit_natural (f : V →ₗ[R] F) (w : V ⊗[R] B) :
    contractCounit (f.rTensor B w) = f (contractCounit w) := by
  induction w with
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Extend a coaction across a split inclusion by the trivial coaction on its complement. -/
def extendedCoaction (δ : V →ₗ[R] V ⊗[R] B) (p : F →ₗ[R] V) (i : V →ₗ[R] F) :
    F →ₗ[R] F ⊗[R] B :=
  i.rTensor B ∘ₗ δ ∘ₗ p +
    (TensorProduct.mk R F B).flip (1 : B) ∘ₗ (LinearMap.id - i ∘ₗ p)

theorem extendedCoaction_apply (δ : V →ₗ[R] V ⊗[R] B)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (x : F) :
    extendedCoaction δ p i x = i.rTensor B (δ (p x)) + (x - i (p x)) ⊗ₜ[R] (1 : B) := rfl

theorem extendedCoaction_inclusion (δ : V →ₗ[R] V ⊗[R] B)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (hpi : p ∘ₗ i = LinearMap.id) (v : V) :
    extendedCoaction δ p i (i v) = i.rTensor B (δ v) := by
  have h : p (i v) = v := LinearMap.congr_fun hpi v
  simp [extendedCoaction_apply, h]

theorem extendedCoaction_complement (δ : V →ₗ[R] V ⊗[R] B)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (hpi : p ∘ₗ i = LinearMap.id) (x : F) :
    extendedCoaction δ p i (x - i (p x)) = (x - i (p x)) ⊗ₜ[R] (1 : B) := by
  have h : p (x - i (p x)) = 0 := by
    have hsplit : p (i (p x)) = p x := LinearMap.congr_fun hpi (p x)
    simp [hsplit]
  simp [extendedCoaction_apply, h]

theorem extendedCoaction_projection (δ : V →ₗ[R] V ⊗[R] B)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (hpi : p ∘ₗ i = LinearMap.id) (x : F) :
    p.rTensor B (extendedCoaction δ p i x) = δ (p x) := by
  have hsplit : p (i (p x)) = p x := LinearMap.congr_fun hpi (p x)
  rw [extendedCoaction_apply, map_add, ← LinearMap.comp_apply,
    ← LinearMap.rTensor_comp, hpi]
  simp [hsplit]

theorem extendedCoaction_counit (δ : V →ₗ[R] V ⊗[R] B)
    (hδ : ∀ v, contractCounit (δ v) = v)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (x : F) :
    contractCounit (extendedCoaction δ p i x) = x := by
  rw [extendedCoaction_apply, map_add, contractCounit_natural, hδ, contractCounit_tmul]
  simp

theorem extendedCoaction_coassoc (δ : V →ₗ[R] V ⊗[R] B) (hδ : IsCoassoc δ)
    (p : F →ₗ[R] V) (i : V →ₗ[R] F) (hpi : p ∘ₗ i = LinearMap.id) :
    IsCoassoc (extendedCoaction δ p i) := by
  let D := extendedCoaction δ p i
  let L := (TensorProduct.assoc R F B B).toLinearMap ∘ₗ D.rTensor B ∘ₗ D
  let K := (comul (R := R) (A := B)).lTensor F ∘ₗ D
  have hnat (w : V ⊗[R] B) (b : B) :
      TensorProduct.assoc R F B B (i.rTensor B w ⊗ₜ[R] b) =
        i.rTensor (B ⊗[R] B) (TensorProduct.assoc R V B B (w ⊗ₜ[R] b)) := by
    induction w with
    | tmul v a => rfl
    | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  have hleft (w : V ⊗[R] B) :
      TensorProduct.assoc R F B B (D.rTensor B (i.rTensor B w)) =
        i.rTensor (B ⊗[R] B) (TensorProduct.assoc R V B B (δ.rTensor B w)) := by
    induction w with
    | tmul v b =>
      simp only [LinearMap.rTensor_tmul]
      rw [show D (i v) = i.rTensor B (δ v) from
        extendedCoaction_inclusion δ p i hpi v, hnat]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hright (w : V ⊗[R] B) :
      (comul (R := R) (A := B)).lTensor F (i.rTensor B w) =
        i.rTensor (B ⊗[R] B) ((comul (R := R) (A := B)).lTensor V w) := by
    induction w with
    | tmul v b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hi (v : V) : L (i v) = K (i v) := by
    change TensorProduct.assoc R F B B (D.rTensor B (D (i v))) =
      (comul (R := R) (A := B)).lTensor F (D (i v))
    rw [show D (i v) = i.rTensor B (δ v) from
      extendedCoaction_inclusion δ p i hpi v, hleft, hright]
    exact congrArg (i.rTensor (B ⊗[R] B)) (LinearMap.congr_fun hδ v)
  have hq (x : F) : L (x - i (p x)) = K (x - i (p x)) := by
    change TensorProduct.assoc R F B B (D.rTensor B (D (x - i (p x)))) =
      (comul (R := R) (A := B)).lTensor F (D (x - i (p x)))
    rw [show D (x - i (p x)) = (x - i (p x)) ⊗ₜ[R] (1 : B) from
      extendedCoaction_complement δ p i hpi x, LinearMap.rTensor_tmul]
    rw [show D (x - i (p x)) = (x - i (p x)) ⊗ₜ[R] (1 : B) from
      extendedCoaction_complement δ p i hpi x]
    simp [Algebra.TensorProduct.one_def]
  apply LinearMap.ext
  intro x
  change L x = K x
  have hx : x = i (p x) + (x - i (p x)) := by abel
  calc
    L x = L (i (p x) + (x - i (p x))) := congrArg L hx
    _ = K (i (p x) + (x - i (p x))) := by rw [map_add, map_add, hi, hq]
    _ = K x := congrArg K hx.symm

section Matrix

variable {N : ℕ} (e : Basis (Fin N) R F) (D : F →ₗ[R] F ⊗[R] B)

/-- Coefficients of a right coaction in a finite basis. -/
def coefficientMatrix : Matrix (Fin N) (Fin N) B := fun i j =>
  TensorProduct.equivFinsuppOfBasisLeft e (D (e j)) i

theorem coaction_basis (j : Fin N) :
    D (e j) = ∑ i, e i ⊗ₜ[R] coefficientMatrix e D i j := by
  conv_lhs =>
    rw [← (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply (D (e j))]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
    Finsupp.sum_fintype _ _ (fun i => by simp)]
  rfl

include e in
theorem sum_basis_tmul_inj {X : Type*} [AddCommGroup X] [Module R X]
    {x y : Fin N → X} (h : ∑ i, e i ⊗ₜ[R] x i = ∑ i, e i ⊗ₜ[R] y i) : x = y := by
  classical
  funext j
  have := congrArg (fun t => TensorProduct.equivFinsuppOfBasisLeft e t j) h
  simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Finsupp.single_apply]
    using this

theorem counit_coefficientMatrix (hε : ∀ x, contractCounit (D x) = x) (i j : Fin N) :
    counit (R := R) (coefficientMatrix e D i j) =
      (1 : Matrix (Fin N) (Fin N) R) i j := by
  classical
  rw [coefficientMatrix, ← IntegralLinearEmbedding.repr_rid_lTensor e counit (D (e j)) i]
  change e.repr (contractCounit (D (e j))) i = _
  rw [hε]
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

theorem comul_coefficientMatrix (hD : IsCoassoc D) (i j : Fin N) :
    comul (R := R) (coefficientMatrix e D i j) =
      ∑ l, coefficientMatrix e D i l ⊗ₜ[R] coefficientMatrix e D l j := by
  have h := LinearMap.congr_fun hD (e j)
  change TensorProduct.assoc R F B B (D.rTensor B (D (e j))) =
    (comul (R := R) (A := B)).lTensor F (D (e j)) at h
  rw [coaction_basis e D j, map_sum, map_sum, map_sum] at h
  simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, coaction_basis e D,
    TensorProduct.sum_tmul, map_sum, TensorProduct.assoc_tmul] at h
  rw [Finset.sum_comm] at h
  simp only [← TensorProduct.tmul_sum] at h
  exact (congrFun (sum_basis_tmul_inj e h) i).symm

theorem basis_image_mem_span_coefficientMatrix (f : F →ₗ[R] B)
    (hf : (comul (R := R) (A := B)) ∘ₗ f = f.rTensor B ∘ₗ D) (j : Fin N) :
    f (e j) ∈ Submodule.span R
      (Set.range fun p : Fin N × Fin N => coefficientMatrix e D p.1 p.2) := by
  have hf' : comul (R := R) (f (e j)) = f.rTensor B (D (e j)) :=
    LinearMap.congr_fun hf (e j)
  have h := rTensor_counit_comul (R := R) (f (e j))
  rw [hf', coaction_basis e D j, map_sum, map_sum] at h
  have h' := congrArg (TensorProduct.lid R B) h
  simp only [LinearMap.rTensor_tmul, map_sum, TensorProduct.lid_tmul, one_smul] at h'
  rw [← h']
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

theorem image_mem_span_coefficientMatrix (f : F →ₗ[R] B)
    (hf : (comul (R := R) (A := B)) ∘ₗ f = f.rTensor B ∘ₗ D) (x : F) :
    f x ∈ Submodule.span R
      (Set.range fun p : Fin N × Fin N => coefficientMatrix e D p.1 p.2) := by
  have h := congrArg f (e.sum_repr x)
  rw [← h, map_sum]
  simp only [map_smul]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (basis_image_mem_span_coefficientMatrix e D f hf j)

end Matrix

/-- Over a Dedekind domain, any finite subset of a flat bialgebra is in the span of
the entries of a finite coaction matrix. -/
theorem exists_matrix_coefficients [IsDedekindDomain R] [Module.Flat R B] (S : Finset B) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) B),
      (∀ i j, comul (R := R) (M i j) = ∑ l, M i l ⊗ₜ[R] M l j) ∧
      (∀ i j, counit (R := R) (M i j) = (1 : Matrix (Fin N) (Fin N) R) i j) ∧
      (S : Set B) ⊆ Submodule.span R (Set.range fun p : Fin N × Fin N => M p.1 p.2) := by
  classical
  let Λ := IntegralLinearEmbedding.finiteSubcomodule (R := R) S
  obtain ⟨hfg, hS, hΛ⟩ := IntegralLinearEmbedding.finiteSubcomodule_spec (R := R) S
  have : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  have : IsTorsionFree R Λ :=
    Function.Injective.moduleIsTorsionFree Λ.subtype Subtype.val_injective (fun _ _ => rfl)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  have : Module.Projective R Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, p, i, hp, hi, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R Λ
  let e := Pi.basisFun R (Fin N)
  obtain ⟨δ, hδ, hcompat⟩ := exists_coaction Λ hΛ
  have hε (v : Λ) : contractCounit (δ v) = v := by
    apply Subtype.val_injective
    change Λ.subtype (contractCounit (δ v)) = (v : B)
    rw [← contractCounit_natural]
    rw [← show comul (R := R) (v : B) = Λ.subtype.rTensor B (δ v) from
      LinearMap.congr_fun hcompat v]
    simp [contractCounit]
  let D := extendedCoaction δ p i
  have hD : IsCoassoc D := extendedCoaction_coassoc δ hδ p i hpi
  have hDε : ∀ x, contractCounit (D x) = x := extendedCoaction_counit δ hε p i
  let f : (Fin N → R) →ₗ[R] B := Λ.subtype ∘ₗ p
  have hf : (comul (R := R) (A := B)) ∘ₗ f = f.rTensor B ∘ₗ D := by
    apply LinearMap.ext
    intro x
    change comul (R := R) (p x : B) = f.rTensor B (D x)
    calc
      comul (R := R) (p x : B) = Λ.subtype.rTensor B (δ (p x)) :=
        LinearMap.congr_fun hcompat (p x)
      _ = Λ.subtype.rTensor B (p.rTensor B (D x)) := by
        rw [extendedCoaction_projection δ p i hpi]
      _ = f.rTensor B (D x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  refine ⟨N, coefficientMatrix e D, comul_coefficientMatrix e D hD,
    counit_coefficientMatrix e D hDε, fun a ha => ?_⟩
  obtain ⟨x, hx⟩ := hp (⟨a, hS ha⟩ : Λ)
  have hfx : f x = a := congrArg Subtype.val hx
  rw [← hfx]
  exact image_mem_span_coefficientMatrix e D f hf x

open CategoryTheory Opposite AlgebraicGeometry
open AffineLinearEmbedding

/-- A flat algebra of finite type corepresenting a group functor over a Dedekind
domain gives a closed linear embedding. -/
theorem exists_corepresented_closedEmbedding {R : CommRingCat.{u}} [IsDedekindDomain R]
    {H : CommAlgCat.{u} R ⥤ GrpCat.{u}} {A : CommAlgCat.{u} R}
    (e : (H ⋙ forget GrpCat).CorepresentableBy A)
    [Module.Flat R A] [Algebra.FiniteType R A] :
    Nonempty (IntegralLinearEmbedding.ClosedEmbedding (Corepresented.groupScheme H e)) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  let := bialgebra e
  obtain ⟨N, M, hcomul, hcounit, hspan⟩ := exists_matrix_coefficients (R := R) (B := A) s
  have hgen : Algebra.adjoin R
      (Set.range fun p : Fin N × Fin N => M p.1 p.2) = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Algebra.adjoin_le fun b hb => Algebra.span_le_adjoin _ _ (hspan hb)
  exact ⟨⟨N, toGLHom e M hcomul hcounit,
    isClosedSubgroup_toGLHom e M hcomul hcounit hgen⟩⟩

/-- Every flat affine group scheme of finite type over a Dedekind domain has a
closed linear embedding. -/
theorem exists_closedEmbedding {R : CommRingCat.{u}} [IsDedekindDomain R]
    (G : GroupScheme (Spec R)) [Flat G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Nonempty (IntegralLinearEmbedding.ClosedEmbedding G) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨W, ⟨ψ⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  have : Algebra.FiniteType R W.unop := AffineCorepresentation.finiteType_of_iso W ψ
  have : Module.Flat R W.unop := IntegralLinearEmbedding.flat_of_iso W ψ
  obtain ⟨D⟩ := exists_corepresented_closedEmbedding (AffineCorepresentation.corep G ψ)
  refine ⟨⟨D.rank, AffineCorepresentation.toModel G ψ ≫ D.representation, ?_⟩⟩
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  have hψ : IsClosedImmersion ψ.inv.left := inferInstance
  exact @IsClosedImmersion.comp _ _ _ ψ.inv.left D.representation.hom.hom.left hψ D.closed

end Langlands.GroupScheme.DedekindLinearEmbedding

namespace Langlands.GroupScheme

/-- Conrad, Exercise 5.5.7(ii), with the exact published hypotheses. -/
theorem dedekindLinearEmbeddingStatement : DedekindLinearEmbeddingStatement.{u} := by
  intro R _ _ G hflat haffine hfinite
  let := hflat
  let := haffine
  let := hfinite
  obtain ⟨D⟩ := DedekindLinearEmbedding.exists_closedEmbedding G
  exact ⟨D.rank, D.representation, D.closed⟩

end Langlands.GroupScheme
