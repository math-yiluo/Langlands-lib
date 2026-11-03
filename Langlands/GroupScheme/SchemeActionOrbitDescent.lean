import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Descent of a subgroup-fixed orbit through an fppf quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {S : Scheme.{u}} {H N V : GroupScheme S} {X : Over S}

/-- The orbit of a subgroup-fixed section is constant on the right cosets. -/
theorem comp_orbitMap_eq_of_inv_mul_mem_range
    (a : SchemeAction H X) (j : N ⟶ H)
    (x : Over.mk (𝟙 S) ⟶ X) (hx : (a.restrict j).IsFixed x)
    {T : Over S} (g h : T ⟶ H.X)
    (hgh : g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T) :
    g ≫ a.orbitMap x = h ≫ a.orbitMap x := by
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp hgh
  have hnx := hx T (toUnit T) n
  rw [restrict_act] at hnx
  have hh : g * (n ≫ j.hom.hom) = h := by
    rw [hn, mul_inv_cancel_left]
  rw [comp_orbitMap, comp_orbitMap, ← hh, act_mul, hnx]

/-- Equal quotient images differ by a point of the specified full scheme kernel. -/
theorem inv_mul_mem_range_of_fppf_quotient
    (j : N ⟶ H) (q : H ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    {T : Over S} (g h : T ⟶ H.X)
    (he : g ≫ q.hom.hom = h ≫ q.hom.hom) :
    g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T := by
  rw [← hq.2.2.2]
  have hd : (g⁻¹ * h) ≫ q.hom.hom = toUnit T ≫ η[V.X] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, he, inv_mul_cancel]
    rfl
  exact SubgroupFunctor.mem_range.mpr
    ⟨(kernel_isPullback q).lift (g⁻¹ * h) (toUnit T) hd,
      (kernel_isPullback q).lift_fst _ _ _⟩

variable {k : Type u} [Field k]
    {H N V : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))}

/-- An affine source makes any represented fppf group quotient quasi-compact. -/
theorem quasiCompact_quotient (q : H ⟶ V) [IsAffineHom H.X.hom] :
    QuasiCompact q.hom.hom.left := by
  let : IsSeparated V.X.hom := fieldSeparated k V
  have : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
    rw [Over.w]
    infer_instance
  exact QuasiCompact.of_comp q.hom.hom.left V.X.hom

/-- A subgroup-fixed rational orbit factors through the actual fpqc quotient. -/
theorem exists_orbitMap_factor (a : SchemeAction H X) (j : N ⟶ H) (q : H ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    [QuasiCompact q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) :
    ∃ ρ : V.X ⟶ X, q.hom.hom ≫ ρ = a.orbitMap x := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  exact FiniteIndexTransfer.exists_factor j (a.orbitMap x) q.hom.hom
    (fun _ g h he => inv_mul_mem_range_of_fppf_quotient j q hq g h he)
    (fun _ g h he => a.comp_orbitMap_eq_of_inv_mul_mem_range j x hx g h he)

/-- The actual morphism descended from the orbit of a subgroup-fixed section. -/
def descendedOrbitMap (a : SchemeAction H X) (j : N ⟶ H) (q : H ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    [QuasiCompact q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) : V.X ⟶ X :=
  (a.exists_orbitMap_factor j q hq x hx).choose

/-- Pulling back the descended orbit recovers the original orbit morphism. -/
theorem quotient_comp_descendedOrbitMap (a : SchemeAction H X) (j : N ⟶ H) (q : H ⟶ V)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    [QuasiCompact q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (hx : (a.restrict j).IsFixed x) :
    q.hom.hom ≫ a.descendedOrbitMap j q hq x hx = a.orbitMap x :=
  (a.exists_orbitMap_factor j q hq x hx).choose_spec

/-- Every fpqc factor of an orbit morphism is equivariant on all scheme tests. -/
theorem equivariant_of_orbitMap_factor (a : SchemeAction H X) (q : H ⟶ V)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (ρ : V.X ⟶ X) (hρ : q.hom.hom ≫ ρ = a.orbitMap x)
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X) :
    a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ := by
  apply Dynamic.flagQuotient_hom_ext_of_local_lift H q.hom.hom v
  intro T' b g hg
  rw [a.naturality, ← Category.assoc, hg, Category.assoc, hρ, a.comp_orbitMap,
    ← a.act_mul]
  rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hg,
    ← MonObj.mul_comp, Category.assoc, hρ, a.comp_orbitMap]

end SchemeAction

end Langlands.GroupScheme
