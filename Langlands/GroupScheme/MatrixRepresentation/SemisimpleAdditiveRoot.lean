import Langlands.GroupScheme.SpecialLinearRootGroups
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Semisimplicity excludes nontrivial additive root actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The standard two-dimensional representation induced by an additive character. -/
def additiveRootRepresentation
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) :
    MatrixRepresentation G (Fin 2) :=
  f ≫ SpecialLinear.Root.rootMap (n := Fin 2) (CommRingCat.of k)
    (show (0 : Fin 2) ≠ 1 by decide) ≫
      SpecialLinear.inclusion (Fin 2) (CommRingCat.of k)

/-- On every scheme test the additive root representation is a transvection. -/
theorem additiveRootRepresentation_pointMatrix
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (additiveRootRepresentation f).pointMatrix T x =
      Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 2) ≠ 1 by decide)
          ((VectorGroup.coordinates (CommRingCat.of k) 1 T
            (x ≫ f.hom.hom)).toAdd 0)) := by
  simp only [pointMatrix_apply, additiveRootRepresentation, Grp.comp_hom_hom]
  rw [← Category.assoc, ← Category.assoc, SpecialLinear.pointsEquiv_inclusion,
    SpecialLinear.Root.pointsEquiv_rootMap]

/-- Its affine matrices have the original additive coordinate in the upper-right entry. -/
theorem additiveRootRepresentation_affineMatrix_eq
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    ((additiveRootRepresentation f).affineMatrix A x :
      Matrix (Fin 2) (Fin 2) A) =
        !![1, (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) 1)
          (VectorGroup.corepresentableBy (CommRingCat.of k) 1) A
            (x ≫ f.hom.hom)).toAdd 0; 0, 1] := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
  have hcoord := congrArg (fun z : Multiplicative (Fin 1 → A) => z.toAdd 0)
    (Corepresented.map_affineSectionsIso_pointsEquiv
      (VectorGroup.functor (CommRingCat.of k) 1)
      (VectorGroup.corepresentableBy (CommRingCat.of k) 1) A (x ≫ f.hom.hom))
  change (Corepresented.affineSectionsIso A).hom.hom.toRingHom
    ((VectorGroup.coordinates (CommRingCat.of k) 1
      ((algSpec (CommRingCat.of k)).obj (op A)) (x ≫ f.hom.hom)).toAdd 0) = _ at hcoord
  rw [Corepresented.affineSectionsIso_hom_ringHom] at hcoord
  suffices hm : ((additiveRootRepresentation f).affineMatrix A x :
      Matrix (Fin 2) (Fin 2) A) =
        !![1, e ((VectorGroup.coordinates (CommRingCat.of k) 1
          ((algSpec (CommRingCat.of k)).obj (op A)) (x ≫ f.hom.hom)).toAdd 0); 0, 1] by
    exact hm.trans (congrArg (fun a : A => !![1, a; 0, 1]) hcoord)
  have he (z : A) : e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom z) = z :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id z
  have he1 : e (1 : Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) = 1 :=
    e.map_one
  have he0 : e (0 : Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) = 0 :=
    e.map_zero
  have h := additiveRootRepresentation_pointMatrix f _ x
  rw [pointMatrix_eq_affineMatrix, Corepresented.affineSectionsIso_inv_ringHom] at h
  ext i j
  have hij := congrArg
    (fun M : GL (Fin 2) Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) =>
      e (M.val i j)) h
  change e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (((additiveRootRepresentation f).affineMatrix A x).val i j)) =
      e ((1 + Matrix.single 0 1
        ((VectorGroup.coordinates (CommRingCat.of k) 1
          ((algSpec (CommRingCat.of k)).obj (op A))
            (x ≫ f.hom.hom)).toAdd 0)) i j) at hij
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.single_apply, Matrix.one_apply, he, he1, he0, e] using hij

/-- Its affine matrices are upper unitriangular on every test algebra. -/
theorem additiveRootRepresentation_affineMatrix
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    ∃ a : A, ((additiveRootRepresentation f).affineMatrix A x :
      Matrix (Fin 2) (Fin 2) A) = !![1, a; 0, 1] :=
  ⟨_, additiveRootRepresentation_affineMatrix_eq f A x⟩

/-- An upper unitriangular two-dimensional action that is a sum of simple stable
subspaces has zero upper-right coefficient on every affine test. -/
theorem upperUnipotent_coefficient_eq_zero
    (ρ : MatrixRepresentation G (Fin 2))
    (hρ : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      ∃ a : A, (ρ.affineMatrix A x : Matrix (Fin 2) (Fin 2) A) = !![1, a; 0, 1])
    (hss : sSup {W : Submodule k (Fin 2 → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (Fin 2 → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (a : A) (ha : (ρ.affineMatrix A x : Matrix (Fin 2) (Fin 2) A) = !![1, a; 0, 1]) :
    a = 0 := by
  classical
  let e₀ : Fin 2 → k := ![1, 0]
  let L : Submodule k (Fin 2 → k) := Submodule.span k {e₀}
  have hLmem (v : Fin 2 → k) : v ∈ L ↔ v 1 = 0 := by
    constructor
    · intro hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp [e₀]
    · intro hv
      apply Submodule.mem_span_singleton.mpr
      refine ⟨v 0, ?_⟩
      ext i
      fin_cases i <;> simp [e₀, hv]
  have heL : e₀ ∈ L := Submodule.subset_span (Set.mem_singleton e₀)
  have hL0 : L ≠ ⊥ := by
    intro hz
    have he := heL
    rw [hz, Submodule.mem_bot] at he
    have := congrFun he 0
    simp [e₀] at this
  have hL : ρ.IsStableSubspace L := by
    intro B y v hv ℓ
    obtain ⟨b, hb⟩ := hρ B y
    apply (hLmem _).mpr
    have hv1 := (hLmem v).mp hv
    simp [hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1]
  apply (Module.forall_dual_apply_eq_zero_iff k a).mp
  intro ℓ
  by_contra hc
  have hsimple : ∀ W ∈ {W : Submodule k (Fin 2 → k) |
      ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin 2 → k), ρ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W}, W ≤ L := by
    intro W hW
    by_cases hLW : L ≤ W
    · rcases hW.2.2 L hL hLW with hz | he
      · exact (hL0 hz).elim
      · exact he.symm.le
    · intro v hv
      apply (hLmem v).mpr
      by_contra hv1
      have hcoef := hW.1 A x v hv ℓ
      have hdiff := W.sub_mem hcoef (W.smul_mem (ℓ 1) hv)
      have heq :
          (fun i => ℓ (((ρ.affineMatrix A x : Matrix (Fin 2) (Fin 2) A) *ᵥ
            (fun j => algebraMap k A (v j))) i)) - (ℓ 1) • v =
          (ℓ a * v 1) • e₀ := by
        have hmul (c : k) (b : A) :
            ℓ (b * algebraMap k A c) = c * ℓ b := by
          rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
        have halg (c : k) : ℓ (algebraMap k A c) = c * ℓ 1 := by
          simpa using hmul c 1
        ext i
        fin_cases i <;>
          simp [ha, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add,
            hmul, halg, e₀, mul_comm]
      rw [heq] at hdiff
      have heW : e₀ ∈ W := by
        have hm := W.smul_mem (ℓ a * v 1)⁻¹ hdiff
        rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hv1), one_smul] at hm
        exact hm
      exact hLW (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heW))
  have htop : (⊤ : Submodule k (Fin 2 → k)) ≤ L := by
    rw [← hss]
    exact sSup_le hsimple
  have hz := (hLmem ![0, 1]).mp (htop (by trivial))
  change (1 : k) = 0 at hz
  exact one_ne_zero hz

/-- Semisimplicity of the induced root representation kills the original additive
coordinate on every affine test algebra. -/
theorem additiveRootRepresentation_affineCoordinates_eq_zero
    (f : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (hss : sSup {W : Submodule k (Fin 2 → k) |
      (additiveRootRepresentation f).IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin 2 → k),
          (additiveRootRepresentation f).IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} = ⊤)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) 1)
      (VectorGroup.corepresentableBy (CommRingCat.of k) 1) A
        (x ≫ f.hom.hom)).toAdd 0 = 0 :=
  upperUnipotent_coefficient_eq_zero (additiveRootRepresentation f)
    (additiveRootRepresentation_affineMatrix f) hss A x _
    (additiveRootRepresentation_affineMatrix_eq f A x)

end Langlands.GroupScheme.MatrixRepresentation
