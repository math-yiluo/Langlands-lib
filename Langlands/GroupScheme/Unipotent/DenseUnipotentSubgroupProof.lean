import Langlands.GroupScheme.Unipotent.DenseUnipotentSubgroupStatement
import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence
import Langlands.Algebra.SandwichDimensionBoundProof
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Unipotence from a schematically dense subgroup of unipotent points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

section FixedVectors

variable {K : Type u} [Field K] [IsAlgClosed K] {D : Type v} [Group D]

/-- A simple module for the group algebra on which group elements act unipotently
has trivial group action. -/
private theorem simple_action_eq_one {W : Type*} [AddCommGroup W] [Module K W]
    [Module (MonoidAlgebra K D) W] [IsScalarTower K (MonoidAlgebra K D) W]
    [IsSimpleModule (MonoidAlgebra K D) W] [FiniteDimensional K W]
    (hnil : ∀ g : D, IsNilpotent
      (SandwichDimensionBound.actionAlgHom K (MonoidAlgebra K D) W
        (MonoidAlgebra.of K D g) - 1))
    (g : D) : SandwichDimensionBound.actionAlgHom K (MonoidAlgebra K D) W
      (MonoidAlgebra.of K D g) = 1 := by
  classical
  let ofGroup := MonoidAlgebra.of K D
  let action := SandwichDimensionBound.actionAlgHom K (MonoidAlgebra K D) W
  let b := Module.finBasis K W
  let f := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp action
  have hsurj : Function.Surjective f :=
    (LinearMap.toMatrixAlgEquiv b).surjective.comp
      (SandwichDimensionBound.action_surjective K (MonoidAlgebra K D) W)
  have htrace (h : D) : (f (ofGroup h)).trace =
      (1 : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).trace := by
    have hn := (hnil h).map (LinearMap.toMatrixAlgEquiv b).toAlgHom
    change IsNilpotent ((LinearMap.toMatrixAlgEquiv b) (action (ofGroup h) - 1)) at hn
    rw [map_sub, map_one] at hn
    have ht := (Matrix.isNilpotent_trace_of_isNilpotent hn).eq_zero
    change ((LinearMap.toMatrixAlgEquiv b) (action (ofGroup h))).trace = _
    exact sub_eq_zero.mp (by simpa only [Matrix.trace_sub] using ht)
  have hpair (a : MonoidAlgebra K D) : (f a * f (ofGroup g)).trace = (f a).trace := by
    induction a using MonoidAlgebra.induction_on with
    | of h =>
      change (f (ofGroup h) * f (ofGroup g)).trace = (f (ofGroup h)).trace
      calc
        _ = (f (ofGroup (h * g))).trace := by rw [map_mul, map_mul]
        _ = _ := (htrace (h * g)).trans (htrace h).symm
    | add a b ha hb => simp only [map_add, add_mul, Matrix.trace_add, ha, hb]
    | smul c a ha => simp only [map_smul, smul_mul_assoc, Matrix.trace_smul, ha]
  have heq : f (ofGroup g) = 1 := Matrix.ext_iff_trace_mul_left.mpr (fun C => by
    obtain ⟨a, rfl⟩ := hsurj C
    rw [mul_one]
    exact hpair a)
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [map_one]
  exact heq

/-- Milne 14.1 over an algebraically closed field. -/
private theorem exists_fixed_of_unipotent_over_algClosed {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (r : Representation K D V)
    (hnil : ∀ g : D, IsNilpotent (r g - 1)) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : D, r g w = w := by
  let A := MonoidAlgebra K D
  have : Nontrivial r.asModule := r.asModuleEquiv.symm.injective.nontrivial
  have : IsArtinian A r.asModule := isArtinian_of_tower K inferInstance
  obtain ⟨W, hW⟩ := IsAtomic.exists_atom (α := Submodule A r.asModule)
  let : IsSimpleModule A W := isSimpleModule_iff_isAtom.mpr hW
  let : FiniteDimensional K W := inferInstanceAs (FiniteDimensional K (W.restrictScalars K))
  let action := SandwichDimensionBound.actionAlgHom K A W
  let ofGroup := MonoidAlgebra.of K D
  have hrestrict (g : D) : IsNilpotent (action (ofGroup g) - 1) := by
    obtain ⟨d, hd⟩ := hnil g
    refine ⟨d, ?_⟩
    suffices action ((ofGroup g - 1) ^ d) = 0 by
      simpa only [map_pow, map_sub, map_one] using this
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply r.asModuleEquiv.injective
    change r.asModuleEquiv (((ofGroup g - 1) ^ d) • (x : r.asModule)) = r.asModuleEquiv 0
    rw [r.asModuleEquiv_map_smul, map_pow, map_sub, r.asAlgebraHom_of, map_one, hd]
    simp
  have : Nontrivial W := IsSimpleModule.nontrivial A W
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨r.asModuleEquiv w, fun hz => hw (Subtype.ext (r.asModuleEquiv.map_eq_zero_iff.mp hz)), ?_⟩
  intro g
  have he : action (ofGroup g) = 1 := simple_action_eq_one hrestrict g
  have hw' : r.asModuleEquiv (ofGroup g • (w : r.asModule)) = r.asModuleEquiv w :=
    congrArg (fun y : W => r.asModuleEquiv y) (DFunLike.congr_fun he w)
  rwa [r.asModuleEquiv_map_smul, r.asAlgebraHom_of] at hw'

/-- Over any field, an abstract group acting by unipotent matrices has a nonzero fixed vector. -/
private theorem exists_fixed_of_unipotent {k : Type u} [Field k] {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (r : D →* Matrix n n k)
    (hnil : ∀ g : D, IsNilpotent (r g - 1)) :
    ∃ w : n → k, w ≠ 0 ∧ ∀ g : D, r g *ᵥ w = w := by
  classical
  let L := AlgebraicClosure k
  let lift : Matrix n n k →+* Module.End L (n → L) :=
    (Matrix.toLinAlgEquiv' : Matrix n n L ≃ₐ[L] Module.End L (n → L)).toRingHom.comp
      (algebraMap k L).mapMatrix
  let extended : Representation L D (n → L) := lift.toMonoidHom.comp r
  have hextended (g : D) : IsNilpotent (extended g - 1) := by
    change IsNilpotent (lift (r g) - 1)
    simpa only [map_sub, map_one] using (hnil g).map lift
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_unipotent_over_algClosed extended hextended
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hz
    exact hw0 (funext hz)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k hi
  refine ⟨fun j => ℓ (w j), fun hz => hℓ (congrFun hz i), ?_⟩
  intro g
  have hg : (r g).map (algebraMap k L) *ᵥ w = w := hw g
  funext j
  have hj := congrArg ℓ (congrFun hg j)
  change ℓ (∑ a, algebraMap k L (r g j a) * w a) = ℓ (w j) at hj
  simpa only [Matrix.mulVec, dotProduct, map_sum, ← Algebra.smul_def,
    map_smul, smul_eq_mul] using hj

end FixedVectors

open scoped CategoryTheory.MonObj

section SchematicDensity

open CentralIntersection MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A function on an affine scheme vanishes if it vanishes on a schematically dense
family of rational points. Its zero scheme is the spectrum of the principal quotient. -/
private theorem eq_zero_of_dense_evaluations [IsAffine G.X.left]
    (S : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hdense : ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
      (∀ g ∈ S, ∃ s : Spec (CommRingCat.of k) ⟶ Z, s ≫ z = g.left) → IsIso z)
    (f : Γ(G.X.left, ⊤)) (hf : ∀ g ∈ S, CentralIntersection.evalPoint g f = 0) : f = 0 := by
  let I : Ideal Γ(G.X.left, ⊤) := Ideal.span {f}
  let q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let z := Spec.map q ≫ G.X.left.isoSpec.inv
  have hclosed : IsClosedImmersion z := by dsimp [z, q]; infer_instance
  have hz : IsIso z := hdense _ z hclosed fun g hg => by
    let e := g.left.appTop.hom
    have he : e f = 0 :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
        (((CentralIntersection.evalPoint_apply g f).symm.trans (hf g hg)).trans (map_zero _).symm)
    have hI : I ≤ RingHom.ker e := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr he)
    let e' := CommRingCat.ofHom (Ideal.Quotient.lift I e (fun a ha => hI ha))
    have hcomp : q ≫ e' = g.left.appTop :=
      CommRingCat.hom_ext (Ideal.Quotient.lift_comp_mk I e (fun a ha => hI ha))
    refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map e', ?_⟩
    dsimp only [z]
    rw [Category.assoc, ← Spec.map_comp_assoc, hcomp,
      Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have hspec : IsIso (Spec.map q) := by
    rw [show Spec.map q = z ≫ G.X.left.isoSpec.hom by simp [z]]
    infer_instance
  apply (isIso_SpecMap_iff.mp hspec).1
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))

/-- A point acting unipotently in a closed embedding acts unipotently in every
representation if the same holds for its inverse. -/
private theorem isNilpotent_other_rationalMatrix [IsAffine G.X.left]
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (ρ : MatrixRepresentation G n) [IsClosedImmersion ρ.hom.hom.left]
    (σ : MatrixRepresentation G m) (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hh : IsNilpotent ((ρ.rationalMatrix h : Matrix n n k) - 1))
    (hinv : IsNilpotent ((ρ.rationalMatrix h⁻¹ : Matrix n n k) - 1)) :
    IsNilpotent ((σ.rationalMatrix h : Matrix m m k) - 1) := by
  have hscalar (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (hx : IsNilpotent ((ρ.rationalMatrix x : Matrix n n k) - 1)) :
      IsNilpotent ((scalarMap G.X).mapMatrix (ρ.rationalMatrix x : Matrix n n k) - 1) := by
    simpa only [map_sub, map_one] using hx.map (scalarMap G.X).mapMatrix
  have hL : ∀ f, f ∈ locallyUnipotent (translationMap h) :=
    mem_of_isClosedImmersion ρ (locallyUnipotent (translationMap h))
      (fun c => mem_locallyUnipotent_of_fixed _ (translationMap_scalarMap h c))
      (mem_locallyUnipotent_of_mapMatrix_eq_mul _ _ _ (translationMap_mapMatrix_scalarMap h _)
        (translationMap_mapMatrix_pointMatrix ρ h) (hscalar h hh))
      (mem_locallyUnipotent_of_mapMatrix_eq_mul_left _ _ _
        (translationMap_mapMatrix_scalarMap h _)
        (translationMap_mapMatrix_pointMatrix_inv ρ h) (hscalar h⁻¹ hinv))
  have hB := isNilpotent_sub_one_of_mapMatrix_eq_mul (translationMap h) _ _
    (σ.pointMatrix G.X (𝟙 G.X)).isUnit (translationMap_mapMatrix_scalarMap h _)
    (translationMap_mapMatrix_pointMatrix σ h) (fun _ _ => hL _)
  have := hB.map
    (CentralIntersection.evalPoint (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).mapMatrix
  rwa [map_sub, map_one, evalPoint_mapMatrix_scalarMap] at this

end SchematicDensity

/-- Milne 2017, Corollary 14.11, over an arbitrary field. -/
theorem generalLinearDenseUnipotentSubgroup : GeneralLinearDenseUnipotentSubgroupStatement.{u} := by
  intro k _ G n _ _ ρ hρ S hdense hS m _ _ _ σ
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of k)).X.left :=
    inferInstanceAs (IsAffine (Spec _))
  let : IsAffine G.X.left := isAffine_of_isAffineHom ρ.hom.hom.left
  let r : S →* Matrix m m k := (Units.coeHom _).comp (σ.rationalMatrix.comp S.subtype)
  obtain ⟨v, hv, hfix⟩ := exists_fixed_of_unipotent r fun g =>
    isNilpotent_other_rationalMatrix ρ σ g.1 (hS g.1 g.2) (hS g.1⁻¹ (S.inv_mem g.2))
  refine ⟨v, hv, (σ.isFixedVector_iff_universal v).mpr ?_⟩
  funext i
  rw [← sub_eq_zero]
  refine eq_zero_of_dense_evaluations S hdense _ fun g hg => ?_
  have hscalar : (CentralIntersection.evalPoint g ∘ fun j => scalarMap G.X (v j)) = v :=
    funext fun j => CentralIntersection.evalPoint_scalarMap g (v j)
  rw [map_sub, RingHom.map_mulVec, CentralIntersection.evalPoint_mapMatrix_pointMatrix,
    hscalar, show (σ.rationalMatrix g : Matrix m m k) *ᵥ v = v from hfix ⟨g, hg⟩,
    CentralIntersection.evalPoint_scalarMap, sub_self]

end Langlands.GroupScheme
