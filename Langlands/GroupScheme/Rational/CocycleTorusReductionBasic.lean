import Langlands.GroupScheme.Rational.CocycleTorusReduction
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Basic constructions of torus reductions of cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle.TorusReduction

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {U V : Over (Spec (CommRingCat.of K))}

/-- A torus reduction of a refined cocycle is a torus reduction of the original cocycle:
compose the refinements and keep the cochain and the torus. -/
def ofRefine {ξ : Cocycle G U} (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left]
    (R : (ξ.refine r).TorusReduction) : ξ.TorusReduction where
  carrier := R.carrier
  refinement := R.refinement ≫ r
  quasiCompact_refinement := by
    have := R.quasiCompact_refinement
    rw [Over.comp_left]
    infer_instance
  flat_refinement := by
    have := R.flat_refinement
    rw [Over.comp_left]
    infer_instance
  surjective_refinement := by
    have := R.surjective_refinement
    rw [Over.comp_left]
    infer_instance
  cochain := R.cochain
  torus := R.torus
  isTorus := R.isTorus
  inclusion := R.inclusion
  isClosedSubgroup := R.isClosedSubgroup
  factorization a b := by
    obtain ⟨t, ht⟩ := R.factorization a b
    refine ⟨t, ht.trans ?_⟩
    simp only [refine_toFun, Category.assoc]

/-- A torus reduction of the twist `(a, b) ↦ f(a)⁻¹ ξ(a, b) f(b)` is a torus reduction of
`ξ`: multiply the cochain on the left by the refined twisting point. -/
def ofTwist {ξ : Cocycle G U} (f : U ⟶ G.X) (R : (ξ.twist f).TorusReduction) :
    ξ.TorusReduction where
  carrier := R.carrier
  refinement := R.refinement
  quasiCompact_refinement := R.quasiCompact_refinement
  flat_refinement := R.flat_refinement
  surjective_refinement := R.surjective_refinement
  cochain := (R.refinement ≫ f) * R.cochain
  torus := R.torus
  isTorus := R.isTorus
  inclusion := R.inclusion
  isClosedSubgroup := R.isClosedSubgroup
  factorization a b := by
    obtain ⟨t, ht⟩ := R.factorization a b
    refine ⟨t, ht.trans ?_⟩
    change (a ≫ R.cochain)⁻¹ * ((a ≫ R.refinement ≫ f)⁻¹ *
        ξ.toFun (a ≫ R.refinement) (b ≫ R.refinement) * (b ≫ R.refinement ≫ f)) *
        (b ≫ R.cochain) = _
    simp only [MonObj.comp_mul]
    group

/-- A torus reduction of `ξ` is a torus reduction of each of its twists: multiply the
cochain on the left by the inverse of the refined twisting point. -/
def twist {ξ : Cocycle G U} (f : U ⟶ G.X) (R : ξ.TorusReduction) :
    (ξ.twist f).TorusReduction where
  carrier := R.carrier
  refinement := R.refinement
  quasiCompact_refinement := R.quasiCompact_refinement
  flat_refinement := R.flat_refinement
  surjective_refinement := R.surjective_refinement
  cochain := (R.refinement ≫ f)⁻¹ * R.cochain
  torus := R.torus
  isTorus := R.isTorus
  inclusion := R.inclusion
  isClosedSubgroup := R.isClosedSubgroup
  factorization a b := by
    obtain ⟨t, ht⟩ := R.factorization a b
    refine ⟨t, ht.trans ?_⟩
    change _ = (a ≫ ((R.refinement ≫ f)⁻¹ * R.cochain))⁻¹ * ((a ≫ R.refinement ≫ f)⁻¹ *
        ξ.toFun (a ≫ R.refinement) (b ≫ R.refinement) * (b ≫ R.refinement ≫ f)) *
        (b ≫ ((R.refinement ≫ f)⁻¹ * R.cochain))
    simp only [MonObj.comp_mul, GrpObj.comp_inv]
    group

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A cocycle on a finite Galois cover that is the coboundary of a cochain `f` reduces to
any closed torus, with the identity refinement, the cochain `f` and unit torus values. -/
def ofCoboundary {ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))}
    (f : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X)
    (hf : ∀ {Z : Over (Spec (CommRingCat.of K))}
      (a b : Z ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
      ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹)
    (T : GroupScheme (Spec (CommRingCat.of K))) (hT : IsTorus T) (i : T ⟶ G)
    (hi : IsClosedSubgroup i) : ξ.TorusReduction where
  carrier := L
  refinement := 𝟙 _
  quasiCompact_refinement := by
    rw [Over.id_left]
    infer_instance
  flat_refinement := by
    rw [Over.id_left]
    infer_instance
  surjective_refinement := by
    rw [Over.id_left]
    infer_instance
  cochain := f
  torus := T
  isTorus := hT
  inclusion := i
  isClosedSubgroup := hi
  factorization a b := ⟨1, by
    rw [MonObj.one_comp, Category.comp_id, Category.comp_id, hf]
    group⟩

/-- A trivial cocycle on a finite Galois cover of a separated group scheme has a torus
reduction, through the trivial torus embedded as the identity section. -/
theorem nonempty_of_isTrivial [IsSeparated G.X.hom]
    {ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))}
    (hξ : ξ.IsTrivial) : Nonempty ξ.TorusReduction := by
  obtain ⟨f, hf⟩ := hξ
  exact ⟨ofCoboundary f hf _ (TorusExistence.isTorus_trivialTorus K)
    (TorusExistence.trivialTorusHom G) (TorusExistence.isClosedSubgroup_trivialTorusHom G)⟩

end Langlands.GroupScheme.Cocycle.TorusReduction
