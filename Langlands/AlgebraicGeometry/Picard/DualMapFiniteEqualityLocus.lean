import Langlands.AlgebraicGeometry.Picard.DualMapEqualityLocus
import Mathlib.Data.Fintype.Basic

/-! # Finite closed equality loci for actual maps into a chosen dual -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

namespace DualMapEquality

variable {S : Scheme.{u}}

/-- The intersection of two objects over the base, using their actual fibre product. -/
def intersection (X Y : Over S) : Over S :=
  Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)

instance intersection_isClosedImmersion (X Y : Over S)
    [IsClosedImmersion X.hom] [IsClosedImmersion Y.hom] :
    IsClosedImmersion (intersection X Y).hom := by
  change IsClosedImmersion (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

/-- A map to the intersection is a pair of maps over the same base. -/
lemma intersection_nonempty_iff (X Y T : Over S) :
    Nonempty (T ⟶ intersection X Y) ↔ Nonempty (T ⟶ X) ∧ Nonempty (T ⟶ Y) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨h ≫ Over.homMk (pullback.fst X.hom Y.hom)⟩,
      ⟨h ≫ Over.homMk (pullback.snd X.hom Y.hom)
        (by simp [intersection, pullback.condition])⟩⟩
  · rintro ⟨⟨f⟩, ⟨g⟩⟩
    exact ⟨Over.homMk (pullback.lift f.left g.left (f.w.trans g.w.symm))
      (by simp [intersection, pullback.lift_fst_assoc, f.w])⟩

/-- Every finite collection of closed objects has a closed intersection with an all-test
factorization property. The empty collection is represented by the whole base. -/
theorem exists_closed_finiteIntersection {I : Type v} [Finite I]
    (Z : I → Over S) (hZ : ∀ i, IsClosedImmersion (Z i).hom) :
    ∃ W : Over S, IsClosedImmersion W.hom ∧ ∀ T : Over S,
      Nonempty (T ⟶ W) ↔ ∀ i, Nonempty (T ⟶ Z i) := by
  classical
  let := Fintype.ofFinite I
  have hfin : ∀ J : Finset I, ∃ W : Over S, IsClosedImmersion W.hom ∧
      ∀ T : Over S, Nonempty (T ⟶ W) ↔ ∀ i ∈ J, Nonempty (T ⟶ Z i) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      refine ⟨Over.mk (𝟙 S), ?_, fun T ↦ ?_⟩
      · change IsClosedImmersion (𝟙 S)
        infer_instance
      · constructor
        · intro _ i hi
          simp at hi
        · intro _
          exact ⟨Over.mkIdTerminal.from T⟩
    | @insert i J hi hJ =>
      obtain ⟨W, hW, hWT⟩ := hJ
      let := hW
      let := hZ i
      refine ⟨intersection (Z i) W, inferInstance, fun T ↦ ?_⟩
      rw [intersection_nonempty_iff, hWT]
      simp only [Finset.mem_insert, forall_eq_or_imp]
  simpa only [Finset.mem_univ, forall_true_left] using hfin Finset.univ

variable (B : AbelianScheme S) (hB : HasDualScheme B)

/-- A finite family of actual map equations is represented by a closed object of the base. -/
theorem exists_closed_finiteLocus {I : Type v} [Finite I]
    (f g : I → (B.X ⟶ dualScheme B hB)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧ ∀ T : Over S,
      Nonempty (T ⟶ Z) ↔
        ∀ i, (Over.pullback T.hom).map (f i) = (Over.pullback T.hom).map (g i) := by
  obtain ⟨Z, hZ, hZT⟩ := exists_closed_finiteIntersection
    (fun i ↦ locus B hB (f i) (g i)) (fun _ ↦ inferInstance)
  refine ⟨Z, hZ, fun T ↦ ?_⟩
  simp only [hZT, locus_nonempty_iff]

/-- The chosen finite-family equality locus, fixed before every test scheme. -/
def finiteLocus {I : Type v} [Finite I]
    (f g : I → (B.X ⟶ dualScheme B hB)) : Over S :=
  Classical.choose (exists_closed_finiteLocus B hB f g)

instance finiteLocus_isClosedImmersion {I : Type v} [Finite I]
    (f g : I → (B.X ⟶ dualScheme B hB)) :
    IsClosedImmersion (finiteLocus B hB f g).hom :=
  (Classical.choose_spec (exists_closed_finiteLocus B hB f g)).1

/-- The universal property includes every scheme test, in particular nonreduced tests. -/
theorem finiteLocus_nonempty_iff {I : Type v} [Finite I]
    (f g : I → (B.X ⟶ dualScheme B hB)) (T : Over S) :
    Nonempty (T ⟶ finiteLocus B hB f g) ↔
      ∀ i, (Over.pullback T.hom).map (f i) = (Over.pullback T.hom).map (g i) :=
  (Classical.choose_spec (exists_closed_finiteLocus B hB f g)).2 T

end DualMapEquality

end Langlands.AbelianScheme
