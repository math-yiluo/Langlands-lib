import Langlands.GroupScheme.IdempotentRetract
import Langlands.GroupScheme.SmoothMonoLocalIso
import Langlands.GroupScheme.Torus.IsomorphismLocus

/-! # Opens on which an idempotent is the identity or trivial -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdempotentRetract

variable {S : Scheme.{u}} {G : GroupScheme S} {ψ : G ⟶ G}
  (P : IdempotentRetract ψ)

/-- The open on which the closed image inclusion is étale at its unit. -/
def identityOpen [Smooth G.X.hom] [Smooth P.group.X.hom] : S.Opens :=
  SmoothMonoLocalIso.unitEtaleOpen P.inclusion

private instance smooth_trivial : Smooth (Grp.trivial (Over S)).X.hom := by
  change Smooth (𝟙 S)
  infer_instance

/-- The open on which the unit inclusion into the closed image is étale. -/
def zeroOpen [Smooth P.group.X.hom] : S.Opens :=
  SmoothMonoLocalIso.unitEtaleOpen (0 : Grp.trivial (Over S) ⟶ P.group)

private theorem mono_trivial_inclusion :
    Mono (0 : Grp.trivial (Over S) ⟶ P.group).hom.hom.left := by
  let j : Grp.trivial (Over S) ⟶ P.group := 0
  let : IsSplitMono j :=
    IsSplitMono.mk' ⟨0, Subsingleton.elim _ _⟩
  exact inferInstanceAs
    (Mono (((Grp.forget _).comp (Over.forget _)).map j))

/-- On the identity open the original endomorphism is exactly the identity. -/
theorem map_eq_id_on_identityOpen [Smooth G.X.hom] [Smooth P.group.X.hom]
    [GeometricallyConnected G.X.hom] :
    (baseChange P.identityOpen.ι).map ψ =
      𝟙 ((baseChange P.identityOpen.ι).obj G) := by
  let : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  let F := baseChange P.identityOpen.ι
  let : IsIso (F.map P.inclusion).hom.hom.left :=
    SmoothMonoLocalIso.isIso_unitEtaleOpen P.inclusion
  let : IsIso (F.map P.inclusion) := TorusIsomorphismLocus.isIso_of_underlying _
  apply (cancel_epi (F.map P.inclusion)).mp
  rw [← F.map_comp, P.inclusion_comp, Category.comp_id]

/-- On the zero open the original endomorphism is exactly the trivial map. -/
theorem map_eq_zero_on_zeroOpen [Smooth P.group.X.hom]
    [GeometricallyConnected P.group.X.hom] :
    (baseChange P.zeroOpen.ι).map ψ = 0 := by
  let j : Grp.trivial (Over S) ⟶ P.group := 0
  let : Mono j.hom.hom.left := P.mono_trivial_inclusion
  let F := baseChange P.zeroOpen.ι
  let : IsIso (F.map j).hom.hom.left :=
    SmoothMonoLocalIso.isIso_unitEtaleOpen j
  let : IsIso (F.map j) := TorusIsomorphismLocus.isIso_of_underlying _
  have hi : F.map P.inclusion = 0 := by
    apply (cancel_epi (F.map j)).mp
    rw [← F.map_comp, show j ≫ P.inclusion = 0 from zero_comp, Functor.map_zero,
      comp_zero]
  calc
    F.map ψ = F.map (P.projection ≫ P.inclusion) :=
      congrArg F.map P.factorization.symm
    _ = 0 := by rw [F.map_comp, hi, comp_zero]

/-- An identity residue fibre lies in the identity open. -/
theorem mem_identityOpen_of_residue_eq_id [Smooth G.X.hom] [Smooth P.group.X.hom]
    (s : S)
    (hψ : (baseChange (S.fromSpecResidueField s)).map ψ =
      𝟙 ((baseChange (S.fromSpecResidueField s)).obj G)) :
    s ∈ P.identityOpen := by
  let : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  let F := baseChange (S.fromSpecResidueField s)
  let : IsIso (F.map P.inclusion) :=
    ⟨⟨F.map P.projection, by rw [← F.map_comp, P.retraction, F.map_id],
      by rw [← F.map_comp, P.factorization]; exact hψ⟩⟩
  exact SmoothMonoLocalIso.mem_unitEtaleOpen_of_residueFiber P.inclusion s
    (set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      inferInstanceAs (IsIso (F.map P.inclusion).hom.hom.left))

/-- A trivial residue fibre lies in the zero open. -/
theorem mem_zeroOpen_of_residue_eq_zero [Smooth P.group.X.hom]
    (s : S) (hψ : (baseChange (S.fromSpecResidueField s)).map ψ = 0) :
    s ∈ P.zeroOpen := by
  let F := baseChange (S.fromSpecResidueField s)
  have hi : F.map P.inclusion = 0 := by
    calc
      F.map P.inclusion = F.map (P.inclusion ≫ ψ) :=
        congrArg F.map P.inclusion_comp.symm
      _ = 0 := by rw [F.map_comp, hψ, comp_zero]
  have hH : 𝟙 (F.obj P.group) = 0 := by
    calc
      𝟙 (F.obj P.group) = F.map (P.inclusion ≫ P.projection) := by
        rw [P.retraction, F.map_id]
      _ = 0 := by rw [F.map_comp, hi, zero_comp]
  let j : Grp.trivial (Over S) ⟶ P.group := 0
  let : Mono j.hom.hom.left := P.mono_trivial_inclusion
  let : IsIso (F.map j) :=
    ⟨⟨F.map (0 : P.group ⟶ Grp.trivial (Over S)), by
        rw [← F.map_comp, show j ≫ 0 = 𝟙 _ from Subsingleton.elim _ _, F.map_id],
      by
        rw [← F.map_comp, show (0 : P.group ⟶ Grp.trivial (Over S)) ≫ j = 0 from
          zero_comp, Functor.map_zero]
        exact hH.symm⟩⟩
  exact SmoothMonoLocalIso.mem_unitEtaleOpen_of_residueFiber j s
    (set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      inferInstanceAs (IsIso (F.map j).hom.hom.left))

/-- A residue-fibre dichotomy gives an actual open cover by the two loci. -/
theorem identityOpen_sup_zeroOpen [Smooth G.X.hom] [Smooth P.group.X.hom]
    (hψ : ∀ s : S, (baseChange (S.fromSpecResidueField s)).map ψ = 0 ∨
      (baseChange (S.fromSpecResidueField s)).map ψ =
        𝟙 ((baseChange (S.fromSpecResidueField s)).obj G)) :
    P.identityOpen ⊔ P.zeroOpen = ⊤ := by
  apply top_unique
  intro s _
  rcases hψ s with hz | hi
  · exact Or.inr (P.mem_zeroOpen_of_residue_eq_zero s hz)
  · exact Or.inl (P.mem_identityOpen_of_residue_eq_id s hi)

end Langlands.GroupScheme.IdempotentRetract
