import Langlands.GroupScheme.Torus.Lattice
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Tori and arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace TorusBaseChange

/-- A field receiving compatible embeddings of two extensions of the same field. -/
structure CommonExtension (k K L : Type u)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] where
  carrier : Type u
  [field : Field carrier]
  leftHom : K →+* carrier
  rightHom : L →+* carrier
  compatible : leftHom.comp (algebraMap k K) = rightHom.comp (algebraMap k L)

/-- A common extension obtained from a maximal-ideal quotient of the tensor product. -/
def commonExtension (k K L : Type u)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] :
    CommonExtension k K L := by
  let A := K ⊗[k] L
  let : Nontrivial A :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K L
      (algebraMap k K).injective (algebraMap k L).injective
  let m := (Ideal.exists_maximal (α := A)).choose
  let : m.IsMaximal := (Ideal.exists_maximal (α := A)).choose_spec
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →+* A ⧸ m := Ideal.Quotient.mk m
  refine {
    carrier := A ⧸ m
    field := inferInstance
    leftHom := q.comp Algebra.TensorProduct.includeLeftRingHom
    rightHom := q.comp Algebra.TensorProduct.includeRight.toRingHom
    compatible := ?_ }
  rw [RingHom.comp_assoc, RingHom.comp_assoc,
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]

end TorusBaseChange

private theorem split_baseChange_comp {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (T : GroupScheme S) :
    IsSplitTorus ((GroupScheme.baseChange (c ≫ b)).obj T) ↔
      IsSplitTorus ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj T)) :=
  IsSplitTorus.iso_iff
    ((Functor.mapGrpNatIso (Over.pullbackComp c b)).app T ≪≫
      Functor.mapGrpCompIso.app T)

private theorem split_baseChange_ringHom_comp {k K L : Type u}
    [CommRing k] [CommRing K] [CommRing L] (a : k →+* K) (b : K →+* L)
    (T : GroupScheme (Spec (CommRingCat.of k))) :
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (b.comp a)))).obj T) ↔
      IsSplitTorus ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom b))).obj
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom a))).obj T)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact split_baseChange_comp _ _ T

private theorem exists_common_extension (k K L : Type u)
    [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] :
    ∃ (E : Type u) (_ : Field E) (f : K →+* E) (g : L →+* E),
      f.comp (algebraMap k K) = g.comp (algebraMap k L) := by
  let E := TorusBaseChange.commonExtension k K L
  exact ⟨E.carrier, E.field, E.leftHom, E.rightHom, E.compatible⟩

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {T : GroupScheme (Spec (CommRingCat.of k))}

/-- A torus remains a torus after arbitrary extension of its ground field. -/
theorem IsTorus.baseChange (hT : IsTorus T) :
    IsTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) := by
  obtain ⟨L, hL, aL, hs⟩ := hT
  let : Field L := hL
  let : Algebra k L := aL
  obtain ⟨E, hE, f, g, hfg⟩ := exists_common_extension k L K
  let : Field E := hE
  let : Algebra K E := g.toAlgebra
  refine ⟨E, inferInstance, inferInstance, ?_⟩
  apply (split_baseChange_ringHom_comp (algebraMap k K) g T).mp
  rw [← hfg]
  exact (split_baseChange_ringHom_comp (algebraMap k L) f T).mpr
    (hs.baseChange (Spec.map (CommRingCat.ofHom f)))

/-- If a group scheme becomes a torus over an extension field, it was already a torus. -/
theorem IsTorus.of_baseChange
    (hT : IsTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)) : IsTorus T := by
  obtain ⟨L, hL, aL, hs⟩ := hT
  let : Field L := hL
  let : Algebra K L := aL
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  exact (split_baseChange_ringHom_comp (algebraMap k K) (algebraMap K L) T).mpr hs

/-- The torus predicate is invariant under arbitrary extension of the ground field. -/
theorem isTorus_baseChange_iff :
    IsTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) ↔ IsTorus T :=
  ⟨IsTorus.of_baseChange, IsTorus.baseChange⟩

end Langlands.GroupScheme
