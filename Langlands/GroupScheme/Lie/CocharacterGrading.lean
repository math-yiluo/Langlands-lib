import Langlands.GroupScheme.Lie.CocharacterTangent
import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.Algebra.BaseChangeEigenvectors
import Langlands.GroupScheme.Lie.FieldAlgebraLie

/-! # The grading of the Lie algebra defined by a cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The `n`-th power character takes the value `1 + n ε` at the multiplicative tangent point
`1 + ε`. -/
theorem characterValue_powerHom_gmInfinitesimal (n : ℤ) :
    characterValue (Gm.powerHom (Spec (CommRingCat.of k)) n) (gmInfinitesimal (k := k) 1).val =
      splitTorus.infinitesimalUnit k (n : k) := by
  change Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k (DualNumber k))
    ((gmInfinitesimal (k := k) 1).val ≫
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) n)).hom.hom) = _
  rw [Gm.powerHom_apply, Gm.comp_zsmul_id, map_zpow, gmInfinitesimal_value,
    splitTorus.infinitesimalUnit_zpow, mul_one]


open scoped FieldLie

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The tangent vector `dχ(1)` of a cocharacter `χ`: the image of the multiplicative tangent
point `1 + ε` under `χ`. -/
def cocharacterLieVector (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Additive (lieKernel G k) :=
  Additive.ofMul (targetMap χ k (gmInfinitesimal 1))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- The bracket with `dχ(1)` acts on the weight space of the `n`-th power character by `n`. -/
theorem lie_cocharacterLieVector_of_mem_weightSpace [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (n : ℤ) {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n)) :
    ⁅cocharacterLieVector χ, X⁆ = (n : k) • X := by
  let c := finiteCoordinates G
  let A : CommAlgCat.{u} (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) (DualNumber k)
  let R := CommRingCat.of k
  let f : CommAlgCat.of R k ⟶ A := CommAlgCat.ofHom (Algebra.ofId R (DualNumber k))
  have hw := hX (DualNumber k) (gmInfinitesimal 1).val
  rw [characterValue_powerHom_gmInfinitesimal] at hw
  set XA := lieKernelMapLinear G (Algebra.ofId R (DualNumber k)) X with hXA
  set g := (gmInfinitesimal (k := k) 1).val ≫ χ.hom.hom with hg
  set u : DualNumber k := (splitTorus.infinitesimalUnit k (n : k) : DualNumber k) with hu
  have h1 : c.equiv A (adjoint G (DualNumber k) g XA) = c.equiv A (u • XA) := congrArg _ hw
  have h2 : c.equiv A (adjoint G (DualNumber k) g XA) =
      (adjointRepresentation c).affineAction A g (c.equiv A XA) :=
    (adjointRepresentation_affineAction c A _ _).symm
  have h3 : c.equiv A XA = fun i => f.hom (c.equiv (CommAlgCat.of R k) X i) :=
    c.naturality f X
  have h4 : c.equiv A (u • XA) = u • c.equiv A XA := (c.equiv A).map_smul u XA
  have key := (h2.symm.trans h1).trans h4
  rw [h3] at key
  set v := c.equiv (CommAlgCat.of R k) X with hv
  have hs := (c.equiv (CommAlgCat.of R k)).map_smul (n : k) X
  apply (c.equiv (CommAlgCat.of R k)).injective
  have hbr := adjointDifferentialLieHom_apply_bracket c (cocharacterLieVector χ) X
  refine hbr.symm.trans (Eq.trans ?_ hs.symm)
  funext i
  have hi : ((((adjointRepresentation c).affineMatrix A g : Matrix _ _ (DualNumber k)) *ᵥ
      (fun j => (TrivSqZeroExt.inl (v j) : DualNumber k))) i).snd =
      (u * TrivSqZeroExt.inl (v i)).snd := by
    have := congrArg (fun w : Fin _ → DualNumber k => (w i).snd) key
    exact this
  have ht (a b : Fin (Module.finrank k (Additive (lieKernel G k)))) :
      (adjointRepresentation c).tangentMatrix k (targetMap χ k (gmInfinitesimal 1)) a b =
      (((adjointRepresentation c).affineMatrix A g : Matrix _ _ (DualNumber k)) a b).snd := rfl
  change (∑ j, ((adjointRepresentation c).tangentMatrix k
      (targetMap χ k (gmInfinitesimal 1)) i j) * v j) = (n : k) * v i
  simp_rw [ht]
  simp only [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, mul_zero, zero_add,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul] at hi
  refine hi.trans ?_
  simp [u, splitTorus.infinitesimalUnit]

/-- The weight spaces of the power characters of `Gm` span the Lie algebra. -/
theorem iSup_weightSpace_powerHom_eq_top [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ⨆ n : ℤ, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n) = ⊤ := by
  classical
  rw [← (isInternal_weightSpace_of_isSplitTorus k G (Gm (Spec (CommRingCat.of k)))
    isSplitTorus_gm χ).submodule_iSup_eq_top]
  refine le_antisymm (iSup_le fun n => le_iSup _ _) (iSup_le fun α => ?_)
  obtain ⟨n, rfl⟩ := Gm.powerHom_surjective k α
  exact le_iSup (fun n : ℤ => weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n)) n

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- In characteristic zero, the weight space of the `n`-th power character is exactly the
`n`-eigenspace of the bracket with `dχ(1)`. -/
theorem mem_weightSpace_powerHom_iff [CharZero k] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (n : ℤ) (Y : Additive (lieKernel G k)) :
    Y ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) n) ↔
      ⁅cocharacterLieVector χ, Y⁆ = (n : k) • Y := by
  refine ⟨lie_cocharacterLieVector_of_mem_weightSpace χ n, fun h => ?_⟩
  let T : Module.End k (Additive (lieKernel G k)) := LieAlgebra.ad k _ (cocharacterLieVector χ)
  let W : ℤ → Submodule k (Additive (lieKernel G k)) := fun m =>
    { carrier := {Z | Z ∈ weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) m)}
      add_mem' := fun ha hb => (weightSpace χ _).add_mem ha hb
      zero_mem' := (weightSpace χ _).zero_mem
      smul_mem' := fun c _ hx => (weightSpace χ _).smul_mem c hx }
  have hμ : Function.Injective (fun m : ℤ => (m : k)) := Int.cast_injective
  have hW : ∀ m, ∀ x ∈ W m, T x = (m : k) • x := fun m x hx =>
    lie_cocharacterLieVector_of_mem_weightSpace χ m hx
  have htop : ⨆ m, W m = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    have hY : Y ∈ ⨆ m : ℤ, weightSpace χ (Gm.powerHom (Spec (CommRingCat.of k)) m) := by
      rw [iSup_weightSpace_powerHom_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun x => x ∈ ⨆ m, W m) hY ?_ ?_ ?_
    · exact fun m x hx => Submodule.mem_iSup_of_mem m hx
    · exact Submodule.zero_mem _
    · exact fun x y hx hy => Submodule.add_mem _ hx hy
  have heq := Langlands.Algebra.BaseChangeEigenvectors.eq_eigenspace_of_iSup_eq_top
    T W _ hμ hW htop n
  have hmem : Y ∈ T.eigenspace (n : k) := Module.End.mem_eigenspace_iff.mpr h
  rw [← heq] at hmem
  exact hmem

end Langlands.GroupScheme.Lie
