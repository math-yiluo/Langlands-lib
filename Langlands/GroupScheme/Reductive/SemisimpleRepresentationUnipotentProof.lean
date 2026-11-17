import Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentStatement
import Langlands.GroupScheme.MatrixRepresentation.UnipotentCyclicIrreducibility

/-! # Normal unipotent subgroups and semisimple representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The all-test fixed space of a normal affine subgroup is a stable subspace. -/
theorem isStableSubspace_fixedSubmodule_of_normal [IsAffineHom H.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal) :
    ρ.IsStableSubspace (ρ.restrict i).fixedSubmodule := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨⟨D⟩, ⟨j⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  intro A x v hv ℓ
  exact ρ.normal_fixed_coefficient i hN hv j A x ℓ

/-- If every ground-field vector is fixed on all scheme tests, the representation
is the trivial group-scheme morphism. -/
theorem eq_trivial_of_fixedSubmodule_eq_top
    (ρ : MatrixRepresentation G n) (hfix : ρ.fixedSubmodule = ⊤) :
    ρ = trivial G n := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) T).injective
  change ρ.pointMatrix T x = (trivial G n).pointMatrix T x
  rw [trivial_pointMatrix]
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have hj : ρ.IsFixedVector (Pi.single j (1 : k)) := by
    change Pi.single j (1 : k) ∈ ρ.fixedSubmodule
    rw [hfix]
    exact Submodule.mem_top
  have hs : (fun a => scalarMap T ((Pi.single j (1 : k) : n → k) a)) =
      Pi.single j 1 := by
    funext a
    by_cases ha : a = j <;> simp [ha]
  simpa only [hs, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using hj T x

/-- A normal unipotent closed subgroup fixes each simple stable subspace.
The fixed-space intersection is stable and contains a nonzero vector. -/
theorem le_fixedSubmodule_of_simple [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent H)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (W : Submodule k (n → k)) (hW : ρ.IsStableSubspace W) (hW0 : W ≠ ⊥)
    (hsimple : ∀ U : Submodule k (n → k), ρ.IsStableSubspace U →
      U ≤ W → U = ⊥ ∨ U = W) :
    W ≤ (ρ.restrict i).fixedSubmodule := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let F := (ρ.restrict i).fixedSubmodule
  have hF : ρ.IsStableSubspace F :=
    ρ.isStableSubspace_fixedSubmodule_of_normal i hN
  have hWF : ρ.IsStableSubspace (W ⊓ F) := by
    intro A x v hv ℓ
    exact ⟨hW A x v hv.1 ℓ, hF A x v hv.2 ℓ⟩
  obtain ⟨w, hwW, hw0, hwF⟩ := hW.exists_nonzero_subgroup_fixedVector hW0 i hU
  have hWF0 : W ⊓ F ≠ ⊥ := by
    intro hz
    have hw : w ∈ W ⊓ F := ⟨hwW, hwF⟩
    rw [hz, Submodule.mem_bot] at hw
    exact hw0 hw
  have he : W ⊓ F = W := (hsimple _ hWF inf_le_left).resolve_left hWF0
  exact he ▸ inf_le_right

end MatrixRepresentation

/-- Milne, Lemma 19.16 and Proposition 19.17: normal unipotent subgroups
act trivially on semisimple representations, and a faithful semisimple
representation forces the unipotent radical to be trivial. -/
theorem semisimpleRepresentationUnipotent :
    SemisimpleRepresentationUnipotentStatement.{u} := by
  intro k _ G _ _
  dsimp only
  have hnormal :
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
        IsClosedSubgroup i → IsUnipotent H → (SubgroupFunctor.range i).IsNormal →
        ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
            ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
              U = ⊥ ∨ U = W} = ⊤ →
          ρ.restrict i = MatrixRepresentation.trivial H (Fin n) := by
    intro H i hi hU hN n ρ hss
    apply MatrixRepresentation.eq_trivial_of_fixedSubmodule_eq_top
    apply top_unique
    rw [← hss]
    apply sSup_le
    intro W hW
    exact ρ.le_fixedSubmodule_of_simple i hi hU hN W hW.1 hW.2.1 hW.2.2
  refine ⟨hnormal, ?_⟩
  intro _ _ n ρ hρ hss H i hi _ _ hU hN
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have htriv := hnormal H i hi hU hN n ρ hss
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rintro ⟨y, rfl⟩
    change T ⟶ H.X at y
    apply (cancel_mono ρ.hom.hom).mp
    apply (GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of k) T).injective
    change ρ.pointMatrix T (y ≫ i.hom.hom) = ρ.pointMatrix T 1
    have hp : (ρ.restrict i).pointMatrix T y = 1 := by
      rw [htriv, MatrixRepresentation.trivial_pointMatrix]
    rw [MatrixRepresentation.pointMatrix_restrict] at hp
    simpa only [map_one] using hp
  · rintro rfl
    exact Subgroup.one_mem _

end Langlands.GroupScheme
