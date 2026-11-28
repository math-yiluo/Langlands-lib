import Langlands.Algebra.DivisionReducedCharpoly
import Langlands.BaseChange.OrdinaryWeylDifferential
import Langlands.HarmonicAnalysis.FiniteDimensionalQuotient
import Langlands.JacquetLanglands.DivisionMatching
import Mathlib.FieldTheory.PrimitiveElement

/-! # Centralizers of matching regular elements -/

noncomputable section

namespace Langlands.JacquetLanglands

open Langlands.BaseChange (glCentralizer glCentralizer_eq_centralizer adjointDefect
  mem_ker_adjointDefect_iff finrank_ker_adjointDefect)
open Langlands.CentralSimple
open _root_.Polynomial _root_.Topology
open scoped IsMulCommutative

universe u

section Algebra

variable {F : Type u} [Field F]

private theorem aeval_adjoin_singleton {R : Type u} [Ring R] [Algebra F R]
    (p : F[X]) (x : R) (hx : aeval x p = 0) :
    aeval (⟨x, Algebra.self_mem_adjoin_singleton F x⟩ :
      Algebra.adjoin F ({x} : Set R)) p = 0 := by
  apply (show Function.Injective (Algebra.adjoin F ({x} : Set R)).val from Subtype.val_injective)
  rw [← aeval_algHom_apply, map_zero]
  exact hx

private def adjoinRootEquivSingleton {R : Type u} [Ring R] [Algebra F R] [Nontrivial R]
    (p : F[X]) [Fact (Irreducible p)] (x : R) (hx : aeval x p = 0) :
    AdjoinRoot p ≃ₐ[F] Algebra.adjoin F {x} := by
  let A := Algebra.adjoin F ({x} : Set R)
  let xA : A := ⟨x, Algebra.self_mem_adjoin_singleton F x⟩
  let f : AdjoinRoot p →ₐ[F] A :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F A) xA (aeval_adjoin_singleton p x hx)
  refine AlgEquiv.ofBijective f ⟨f.injective, ?_⟩
  rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← Algebra.adjoin_adjoin_coe_preimage]
  apply Algebra.adjoin_le
  intro z hz
  have he : z = xA := Subtype.ext (Set.mem_singleton_iff.mp hz)
  subst z
  exact ⟨AdjoinRoot.root p, AdjoinRoot.liftAlgHom_root _ _ _ _⟩

private theorem adjoinRootEquivSingleton_root {R : Type u} [Ring R] [Algebra F R] [Nontrivial R]
    (p : F[X]) [Fact (Irreducible p)] (x : R) (hx : aeval x p = 0) :
    (adjoinRootEquivSingleton p x hx (AdjoinRoot.root p)).val = x := by
  let A := Algebra.adjoin F ({x} : Set R)
  let xA : A := ⟨x, Algebra.self_mem_adjoin_singleton F x⟩
  exact congrArg Subtype.val
    (AdjoinRoot.liftAlgHom_root p (Algebra.ofId F A) xA (aeval_adjoin_singleton p x hx))

private theorem adjoin_singleton_le_centralizer {R : Type u} [Ring R] [Algebra F R]
    (x : R) : Algebra.adjoin F {x} ≤ Subalgebra.centralizer F {x} := by
  apply Algebra.adjoin_le
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  apply (Subalgebra.mem_centralizer_iff F).mpr
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]

private theorem nonempty_fin_of_regularElliptic {n : ℕ} {g : GeneralLinear n F}
    (hg : IsRegularElliptic g) : Nonempty (Fin n) := by
  have hn := natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hg.2)
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hn
  exact ⟨⟨0, hn⟩⟩

private theorem split_adjoin_eq_centralizer {n : ℕ} (g : GeneralLinear n F)
    (hg : IsRegularElliptic g) :
    Algebra.adjoin F {g.val} = Subalgebra.centralizer F {g.val} := by
  let : Nonempty (Fin n) := nonempty_fin_of_regularElliptic hg
  let p := g.val.charpoly
  let : Fact (Irreducible p) := ⟨hg.2⟩
  let e := adjoinRootEquivSingleton p g.val (Matrix.aeval_self_charpoly g.val)
  have hdim : Module.finrank F (Algebra.adjoin F {g.val}) = n := by
    rw [← e.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis' (Matrix.charpoly_monic g.val)).finrank]
    change g.val.charpoly.natDegree = n
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hker : (Subalgebra.centralizer F {g.val}).toSubmodule = (adjointDefect g).ker := by
    ext x
    simp only [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, mem_ker_adjointDefect_iff, commute_iff_eq, eq_comm]
  apply Subalgebra.eq_of_le_of_finrank_eq (adjoin_singleton_le_centralizer g.val)
  rw [hdim, ← (Subalgebra.centralizer F {g.val}).toSubmoduleEquiv.finrank_eq, hker,
    finrank_ker_adjointDefect g hg.1]

variable {D : Type u} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D]

private theorem commutative_subalgebra_finrank_le [CharZero F] (A : Subalgebra F D)
    [IsMulCommutative A] : Module.finrank F A ≤ reducedDegree F D := by
  let : Field A := fieldOfFiniteDimensional F A
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F A
  have htop := Algebra.adjoin_eq_top_of_primitive_element (Algebra.IsAlgebraic.isAlgebraic a) ha
  have hmap := congrArg (Subalgebra.map A.val) htop
  rw [AlgHom.map_adjoin_singleton, Algebra.map_top] at hmap
  have hrange : A.val.range = A := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange] at hmap
  rw [← hmap]
  exact Langlands.CentralDivision.residueGeneratorSubalgebra_finrank_le_reducedDegree F D a.val

private theorem division_adjoin_eq_centralizer [CharZero F] (a : D)
    (ha : (reducedCharpoly F D a).Separable) :
    Algebra.adjoin F {a} = Subalgebra.centralizer F {a} := by
  refine le_antisymm (adjoin_singleton_le_centralizer a) ?_
  intro b hb
  have hab : Commute a b :=
    (Subalgebra.mem_centralizer_iff F).mp hb a (Set.mem_singleton _)
  let B := Algebra.adjoin F ({a, b} : Set D)
  let : IsMulCommutative B := Algebra.isMulCommutative_adjoin F (by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact Commute.refl _ | exact hab | exact hab.symm)
  have hdegree : Module.finrank F (Algebra.adjoin F {a}) = reducedDegree F D := by
    change Module.finrank F (Langlands.CentralDivision.residueGeneratorSubalgebra F D a) = _
    rw [Langlands.CentralDivision.residueGeneratorSubalgebra_finrank,
      ← reducedCharpoly_eq_minpoly_of_separable F D a ha, reducedCharpoly_natDegree]
  have hle : Algebra.adjoin F {a} ≤ B :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have he := Subalgebra.eq_of_le_of_finrank_le hle
    ((commutative_subalgebra_finrank_le B).trans_eq hdegree.symm)
  rw [he]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable {n : ℕ} {g : GeneralLinear n F} {g' : Dˣ}

private def splitRootEquiv (h : Corresponds F D g g') :
    letI : Fact (Irreducible g.val.charpoly) := ⟨h.1.2⟩
    AdjoinRoot g.val.charpoly ≃ₐ[F] Subalgebra.centralizer F {g.val} := by
  let : Nonempty (Fin n) := nonempty_fin_of_regularElliptic h.1
  let : Fact (Irreducible g.val.charpoly) := ⟨h.1.2⟩
  exact (adjoinRootEquivSingleton g.val.charpoly g.val (Matrix.aeval_self_charpoly g.val)).trans
    (Subalgebra.equivOfEq _ _ (split_adjoin_eq_centralizer g h.1))

private theorem division_aeval_charpoly (h : Corresponds F D g g') :
    aeval g'.val g.val.charpoly = 0 := by
  rw [h.2.2]
  exact Langlands.CentralDivision.aeval_reducedCharpoly F D g'.val

variable [CharZero F]

private def divisionRootEquiv (h : Corresponds F D g g') :
    letI : Fact (Irreducible g.val.charpoly) := ⟨h.1.2⟩
    AdjoinRoot g.val.charpoly ≃ₐ[F] Subalgebra.centralizer F {g'.val} :=
  letI : Fact (Irreducible g.val.charpoly) := ⟨h.1.2⟩
  (adjoinRootEquivSingleton g.val.charpoly g'.val (division_aeval_charpoly h)).trans
    (Subalgebra.equivOfEq _ _ (division_adjoin_eq_centralizer g'.val h.2.1))

/-- Matching regular elements have isomorphic centralizer algebras over the base field. -/
def Corresponds.centralizerAlgebraEquiv (h : Corresponds F D g g') :
    Subalgebra.centralizer F {g.val} ≃ₐ[F] Subalgebra.centralizer F {g'.val} :=
  (splitRootEquiv h).symm.trans (divisionRootEquiv h)

/-- The algebra isomorphism sends the matched matrix to the matched division element. -/
theorem Corresponds.centralizerAlgebraEquiv_apply_of_val_eq (h : Corresponds F D g g')
    (x : Subalgebra.centralizer F {g.val}) (hx : x.val = g.val) :
    (h.centralizerAlgebraEquiv x).val = g'.val := by
  let : Nonempty (Fin n) := nonempty_fin_of_regularElliptic h.1
  let : Fact (Irreducible g.val.charpoly) := ⟨h.1.2⟩
  let z := AdjoinRoot.root g.val.charpoly
  have he : splitRootEquiv h z = x := by
    apply Subtype.ext
    change (adjoinRootEquivSingleton g.val.charpoly g.val
      (Matrix.aeval_self_charpoly g.val) z).val = x.val
    rw [adjoinRootEquivSingleton_root, hx]
  unfold Corresponds.centralizerAlgebraEquiv
  rw [AlgEquiv.trans_apply, ← he, AlgEquiv.symm_apply_apply]
  change (adjoinRootEquivSingleton g.val.charpoly g'.val
    (division_aeval_charpoly h) z).val = g'.val
  exact adjoinRootEquivSingleton_root _ _ _

end Algebra

section Topology

variable {F : Type u} [Field F]

private def centralizerUnitsEquiv {R : Type u} [Ring R] [Algebra F R] [TopologicalSpace R]
    (g : Rˣ) (C : Subgroup Rˣ) (hC : C = Subgroup.centralizer {g}) :
    (Subalgebra.centralizer F {g.val})ˣ ≃ₜ* C := by
  let A := Subalgebra.centralizer F {g.val}
  let f : Aˣ →* Rˣ := Units.map A.val.toMonoidHom
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.units_map
  have hmem (x : Aˣ) : f x ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Units.ext ((Subalgebra.mem_centralizer_iff F).mp x.val.property g.val (Set.mem_singleton _))
  let e := f.codRestrict C hmem
  have he : IsEmbedding e := IsEmbedding.subtypeVal.of_comp_iff.mp hf
  have hA (x : C) : x.val.val ∈ A := by
    have hx : x.val ∈ Subgroup.centralizer {g} := hC ▸ x.property
    refine (Subalgebra.mem_centralizer_iff F).mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact congrArg Units.val ((Subgroup.mem_centralizer_iff.mp hx) g (Set.mem_singleton _))
  let e' : Aˣ ≃* C :=
    { toFun := e
      invFun := fun x => ⟨⟨x.val.val, hA x⟩, ⟨(x⁻¹ : C).val.val, hA x⁻¹⟩,
        Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
      left_inv := fun x => Units.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext (Units.ext rfl)
      map_mul' := e.map_mul }
  let t := e'.toEquiv.toHomeomorphOfIsInducing he.isInducing
  exact { e' with continuous_toFun := t.continuous, continuous_invFun := t.symm.continuous }

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  {D : Type u} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D]
  {n : ℕ} {g : GeneralLinear n F} {g' : Dˣ}

/-- The algebra isomorphism induces a topological isomorphism of the matched centralizers. -/
def Corresponds.centralizerEquiv (h : Corresponds F D g g') :
    glCentralizer g ≃ₜ* divisionCentralizer g' := by
  let : IsModuleTopology F (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (IsModuleTopology F (Fin n → Fin n → F))
  let A := Subalgebra.centralizer F {g.val}
  let B := Subalgebra.centralizer F {g'.val}
  let : IsModuleTopology F A := Langlands.HarmonicAnalysis.isModuleTopology_submodule A.toSubmodule
  let : IsModuleTopology F B := Langlands.HarmonicAnalysis.isModuleTopology_submodule B.toSubmodule
  let e := h.centralizerAlgebraEquiv
  let t : A ≃ₜ* B :=
    { e.toMulEquiv with
      continuous_toFun := Langlands.HarmonicAnalysis.continuous_of_linearMap' e.toLinearEquiv.toLinearMap
      continuous_invFun :=
        Langlands.HarmonicAnalysis.continuous_of_linearMap' e.symm.toLinearEquiv.toLinearMap }
  exact (centralizerUnitsEquiv g _ (glCentralizer_eq_centralizer g)).symm.trans
    ((Units.mapContinuousMulEquiv t).trans
      (centralizerUnitsEquiv g' _ (divisionCentralizer_eq_centralizer g')))

/-- The centralizer isomorphism sends `g` to its match `g'`. -/
theorem Corresponds.centralizerEquiv_apply_self (h : Corresponds F D g g') :
    (h.centralizerEquiv ⟨g, self_mem_glCentralizer g⟩).val = g' := by
  apply Units.ext
  exact h.centralizerAlgebraEquiv_apply_of_val_eq _ rfl

/-- The centralizer isomorphism identifies the scalar units from the common base field. -/
theorem Corresponds.centralizerEquiv_apply_scalar (h : Corresponds F D g g') (a : Fˣ) :
    (h.centralizerEquiv ⟨GeneralLinear.scalar a,
      (glCentralizer_eq_centralizer g).symm ▸ Subgroup.mem_centralizer_iff.mpr (by
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (Matrix.GeneralLinearGroup.scalar_commute a g).symm)⟩).val =
      Units.map (algebraMap F D) a := by
  apply Units.ext
  exact congrArg Subtype.val (h.centralizerAlgebraEquiv.commutes a.val)

end Topology

end Langlands.JacquetLanglands
