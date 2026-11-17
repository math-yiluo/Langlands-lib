import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityStatement

/-! # From local central equality to local triviality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralRigidity

variable {S T : Scheme.{u}} {H G : GroupScheme S}

/-- The local central-equality property for a fixed pair of group schemes. -/
def LocalCentralEquality (H G : GroupScheme S) : Prop :=
  ∀ (a b : H ⟶ G) (s : S),
    (baseChange (S.fromSpecResidueField s)).map a =
        (baseChange (S.fromSpecResidueField s)).map b →
    IsCentral ((baseChange (S.fromSpecResidueField s)).map a) →
    ∃ U : S.Opens, s ∈ U ∧
      (baseChange U.ι).map a = (baseChange U.ι).map b

/-- The local triviality property for a fixed pair of group schemes. -/
def LocalTriviality (H G : GroupScheme S) : Prop :=
  ∀ (a : H ⟶ G) (s : S),
    ((baseChange (S.fromSpecResidueField s)).map a).hom.hom = 1 →
    ∃ U : S.Opens, s ∈ U ∧ ((baseChange U.ι).map a).hom.hom = 1

/-- The zero homomorphism has the unit as its underlying morphism of schemes over the base. -/
@[simp] theorem zero_hom_hom : (0 : H ⟶ G).hom.hom = 1 := rfl

/-- Triviality of the underlying morphism is equality to the zero homomorphism. -/
theorem hom_eq_one_iff_eq_zero (a : H ⟶ G) : a.hom.hom = 1 ↔ a = 0 := by
  constructor
  · exact fun h => Grp.hom_ext _ _ h
  · rintro rfl
    rfl

/-- Base change preserves the trivial homomorphism without a commutative-target hypothesis. -/
@[simp] theorem baseChange_map_zero (b : T ⟶ S) :
    (baseChange b).map (0 : H ⟶ G) = 0 := by
  apply Grp.hom_ext
  exact (Over.pullback b).map_one (X := H.X) (M := G.X)

/-- The trivial homomorphism is central on every test scheme. -/
theorem isCentral_zero : IsCentral (0 : H ⟶ G) := by
  intro V x
  rw [zero_hom_hom, MonObj.comp_one]
  exact (center G).carrier V |>.one_mem

/-- SGA 3 IX, Corollary 5.2 follows from the local central-equality assertion of
Theorem 5.1 by comparing with the trivial homomorphism. -/
theorem local_triviality_of_local_central_equality
    (hlocal : LocalCentralEquality H G) : LocalTriviality H G := by
  intro a s ha
  have hzero := (hom_eq_one_iff_eq_zero _).mp ha
  have heq : (baseChange (S.fromSpecResidueField s)).map a =
      (baseChange (S.fromSpecResidueField s)).map (0 : H ⟶ G) := by
    rw [hzero, baseChange_map_zero]
  have hcentral : IsCentral ((baseChange (S.fromSpecResidueField s)).map a) := by
    rw [hzero]
    exact isCentral_zero
  obtain ⟨U, hs, hU⟩ := hlocal a 0 s heq hcentral
  refine ⟨U, hs, ?_⟩
  rw [hU, baseChange_map_zero, zero_hom_hom]

end Langlands.GroupScheme.CentralRigidity
