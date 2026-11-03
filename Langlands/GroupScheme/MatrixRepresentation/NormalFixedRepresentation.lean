import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Actual representations on the fixed space of a normal subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section SplitCoordinates

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]

/-- Every subspace of a finite coordinate space has finite split matrix coordinates. -/
theorem exists_subspace_split_coordinates (V : Submodule k (n → k)) :
    ∃ (d : ℕ) (B : Matrix n (Fin d) k) (C : Matrix (Fin d) n k),
      C * B = 1 ∧
      (∀ j, (fun r => B r j) ∈ V) ∧
      ∀ v, v ∈ V → (B * C) *ᵥ v = v := by
  classical
  obtain ⟨p, hp⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  let b := Module.finBasis k V
  let f : (Fin (Module.finrank k V) → k) →ₗ[k] (n → k) :=
    V.subtype.comp b.equivFun.symm.toLinearMap
  let r : (n → k) →ₗ[k] (Fin (Module.finrank k V) → k) :=
    b.equivFun.toLinearMap.comp p
  have hrf : r.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change b.equivFun (p (V.subtype (b.equivFun.symm x))) = x
    have h := LinearMap.congr_fun hp (b.equivFun.symm x)
    change p (V.subtype (b.equivFun.symm x)) = b.equivFun.symm x at h
    rw [h, b.equivFun.apply_symm_apply]
  refine ⟨_, LinearMap.toMatrix' f, LinearMap.toMatrix' r, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hrf, LinearMap.toMatrix'_id]
  · intro j
    change (fun a => f (Pi.single j 1) a) ∈ V
    exact (b.equivFun.symm (Pi.single j 1)).property
  · intro v hv
    rw [← LinearMap.toMatrix'_comp, LinearMap.toMatrix'_mulVec]
    change V.subtype (b.equivFun.symm (b.equivFun (p v))) = v
    rw [b.equivFun.symm_apply_apply]
    have h := LinearMap.congr_fun hp (⟨v, hv⟩ : V)
    exact congrArg Subtype.val h

end SplitCoordinates

section FixedSubrepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- An actual representation on the entire subgroup-fixed space, with its split
inclusion, projection, intertwining law, and trivial subgroup action. -/
structure FixedSubrepresentation (ρ : MatrixRepresentation G n) (i : H ⟶ G) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  inclusion : Matrix n (Fin dimension) k
  retraction : Matrix (Fin dimension) n k
  left_inverse : retraction * inclusion = 1
  columns_fixed : ∀ j, (ρ.restrict i).IsFixedVector (fun r => inclusion r j)
  projection : ∀ v, (ρ.restrict i).IsFixedVector v →
    (inclusion * retraction) *ᵥ v = v
  intertwines : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * inclusion.map (scalarMap T) =
      inclusion.map (scalarMap T) *
        (representation.pointMatrix T x :
          Matrix (Fin dimension) (Fin dimension) Γ(T.left, ⊤))
  kills_subgroup : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
    representation.pointMatrix T (h ≫ i.hom.hom) = 1

/-- Finite split coordinates of the full fixed space give the actual restricted
representation whenever the subgroup is normal and both groups are affine. -/
theorem nonempty_normalFixedSubrepresentation
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal) :
    Nonempty (FixedSubrepresentation ρ i) := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    exists_subspace_split_coordinates (ρ.restrict i).fixedSubmodule
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨⟨A⟩, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  obtain ⟨⟨D⟩, ⟨jH⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  have hstable : ρ.IsStableCoordinates B C :=
    isStableCoordinates_of_affine_model ρ jG B C
      (normal_fixed_coordinates_affine ρ i hN jH B C hcols hproj A jG.hom)
  let σ := restrictCoordinates ρ B C hCB hstable
  refine ⟨⟨d, σ, B, C, hCB, hcols, hproj,
    restrictCoordinates_intertwines ρ B C hCB hstable, ?_⟩⟩
  intro T h
  apply Units.ext
  change (σ.pointMatrix T (h ≫ i.hom.hom) :
    Matrix (Fin d) (Fin d) Γ(T.left, ⊤)) = 1
  rw [restrictCoordinates_pointMatrix]
  change C.map (scalarMap T) *
    (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *
      B.map (scalarMap T) = 1
  have hB : (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *
      B.map (scalarMap T) = B.map (scalarMap T) := by
    ext r s
    exact congrFun (hcols s T h) r
  rw [Matrix.mul_assoc, hB, ← Matrix.map_mul, hCB,
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- The actual finite matrix representation on the entire normal-subgroup-fixed space. -/
def normalFixedSubrepresentation
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal) :
    FixedSubrepresentation ρ i :=
  Classical.choice (nonempty_normalFixedSubrepresentation ρ i hN)

namespace FixedSubrepresentation

variable {ρ : MatrixRepresentation G n} {i : H ⟶ G}
  (D : FixedSubrepresentation ρ i)

/-- The split coordinates span every fixed vector after any scheme test. -/
theorem inclusion_retraction_vector
    {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (T : Over (Spec (CommRingCat.of k))) :
    D.inclusion.map (scalarMap T) *ᵥ
        (fun j => scalarMap T ((D.retraction *ᵥ v) j)) =
      fun r => scalarMap T (v r) := by
  funext r
  calc
    _ = scalarMap T ((D.inclusion *ᵥ (D.retraction *ᵥ v)) r) :=
      ((scalarMap T).map_mulVec _ _ _).symm
    _ = scalarMap T (v r) := by
      rw [Matrix.mulVec_mulVec, D.projection v hv]

/-- A point acting trivially on the entire fixed space fixes each original fixed vector. -/
theorem fixes_of_pointMatrix_eq_one
    {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X)
    (hx : D.representation.pointMatrix T x = 1) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (fun r => scalarMap T (v r)) = fun r => scalarMap T (v r) := by
  have he := D.intertwines T x
  rw [hx, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] at he
  have h := congrArg
    (fun M => M *ᵥ (fun j => scalarMap T ((D.retraction *ᵥ v) j))) he
  rw [← Matrix.mulVec_mulVec, D.inclusion_retraction_vector hv T] at h
  exact h

/-- A fixed vector whose stabilizer is contained in the subgroup detects exactly
the kernel of the representation on the full fixed space, on every scheme test. -/
theorem pointMatrix_eq_one_iff_mem_range
    {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (hstab : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (v r)) = (fun r => scalarMap T (v r)) →
        x ∈ (SubgroupFunctor.range i).carrier T)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    D.representation.pointMatrix T x = 1 ↔ x ∈ (SubgroupFunctor.range i).carrier T := by
  constructor
  · intro hx
    exact hstab T x (D.fixes_of_pointMatrix_eq_one hv T x hx)
  · rintro ⟨h, rfl⟩
    exact D.kills_subgroup T h

/-- The represented scheme-theoretic kernel has exactly the prescribed range functor.
The stabilizer hypothesis is explicit and is not supplied by normality alone here. -/
theorem range_kernel_eq
    {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (hstab : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (v r)) = (fun r => scalarMap T (v r)) →
        x ∈ (SubgroupFunctor.range i).carrier T) :
    SubgroupFunctor.range (kernelι D.representation) = SubgroupFunctor.range i := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  rw [← D.pointMatrix_eq_one_iff_mem_range hv hstab T x]
  change x ≫ D.representation.hom.hom = 1 ↔
    GeneralLinear.pointsEquiv _ _ T (x ≫ D.representation.hom.hom) = 1
  rw [← map_one (GeneralLinear.pointsEquiv _ _ T), EmbeddingLike.apply_eq_iff_eq]

end FixedSubrepresentation

end FixedSubrepresentation

end Langlands.GroupScheme.MatrixRepresentation
