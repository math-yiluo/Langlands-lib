import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleDescentLift
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupReduction
import Langlands.GroupScheme.Descent.DisjointGroupGluing
import Langlands.GroupScheme.Descent.DisjointPullbackCoherence

/-! # Assembling lifted étale splitting charts -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent

variable {I : Type u} {U : I → Scheme.{u}}

private instance isIso_sigmaDesc_ι : IsIso (Sigma.desc (Sigma.ι U)) := by
  rw [Sigma.desc_ι]
  infer_instance

/-- The group over a coproduct whose given components are diagonalizable with
possibly different character groups. -/
def disjointDiagonalizable (M : I → Type u) [∀ i, AddCommGroup (M i)] : GroupScheme (∐ U) :=
  DisjointGroupGluing.group (Sigma.ι U) (fun i => diagonalizable (U i) (M i))

/-- The comparison to the diagonalizable model on a coproduct component. -/
def disjointDiagonalizableComponentIso (M : I → Type u) [∀ i, AddCommGroup (M i)] (i : I) :
    (baseChange (Sigma.ι U i)).obj (disjointDiagonalizable (U := U) M) ≅
      diagonalizable (U i) (M i) :=
  DisjointGroupGluing.componentIso (Sigma.ι U) (fun i => diagonalizable (U i) (M i)) i

private theorem component_isDiagonalizable (M : I → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, AddGroup.FG (M i)] (i : I) : IsDiagonalizable (diagonalizable (U i) (M i)) :=
  ⟨M i, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- With finitely generated characters on each component, the glued group is of
multiplicative type. -/
theorem disjointDiagonalizable_isMultiplicativeType (M : I → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, AddGroup.FG (M i)] :
    IsMultiplicativeType (disjointDiagonalizable (U := U) M) := by
  apply IsMultiplicativeType.of_openCover (sigmaOpenCover U)
  intro i
  exact IsMultiplicativeType.of_isDiagonalizable <| IsDiagonalizable.of_iso
    (disjointDiagonalizableComponentIso M i) (component_isDiagonalizable M i)

/-- A covering family of reduced splitting charts with étale cartesian lifts
produces a flat multiplicative-type lift of the original group. -/
theorem exists_lift_of_etale_splitting_charts
    {B C : Scheme.{u}} [IsAffine B] (b : C ⟶ B) [IsClosedImmersion b] [Surjective b]
    {V : I → Scheme.{u}} (pᵢ : ∀ i, U i ⟶ B) (tᵢ : ∀ i, V i ⟶ C) (qᵢ : ∀ i, V i ⟶ U i)
    (h : ∀ i, IsPullback (qᵢ i) (tᵢ i) (pᵢ i) b)
    (hp : ∀ i, Etale (pᵢ i)) (ht : ∀ c : C, ∃ i, ∃ v : V i, tᵢ i v = c)
    (H₀ : GroupScheme C) (hs : ∀ i, IsDiagonalizable ((baseChange (tᵢ i)).obj H₀)) :
    ∃ H : GroupScheme B, IsMultiplicativeType H ∧ Flat H.X.hom ∧
      Nonempty ((baseChange b).obj H ≅ H₀) := by
  classical
  let p := Sigma.desc pᵢ
  let t := pullback.snd p b
  let q := pullback.fst p b
  have : Etale p := IsZariskiLocalAtSource.sigmaDesc hp
  have : Surjective p := ⟨fun x => by
    obtain ⟨c, rfl⟩ := b.surjective x
    obtain ⟨i, v, rfl⟩ := ht c
    refine ⟨Sigma.ι U i (qᵢ i v), ?_⟩
    change (Sigma.ι U i ≫ p) (qᵢ i v) = (tᵢ i ≫ b) v
    rw [Sigma.ι_comp_desc]
    exact congrFun (congrArg (fun a : V i ⟶ B => ⇑a) (h i).w) v⟩
  choose M hM hFg e using hs
  let : ∀ i, AddCommGroup (M i) := hM
  let : ∀ i, AddGroup.FG (M i) := hFg
  let G := disjointDiagonalizable (U := U) M
  have hG : IsMultiplicativeType G := disjointDiagonalizable_isMultiplicativeType M
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have compare (i : I) :
      (baseChange (CoproductComponents.toBase q i)).obj ((baseChange t).obj H₀) ≅
      (baseChange (CoproductComponents.toBase q i)).obj ((baseChange q).obj G) := by
    let k := CoproductComponents.toBase q i
    let j := CoproductComponents.toComponent q i
    have hj : j ≫ Sigma.ι U i = k ≫ q := CoproductComponents.component_condition q i
    have hw : j ≫ pᵢ i = (k ≫ t) ≫ b := by
      rw [← Sigma.ι_comp_desc pᵢ i, ← Category.assoc, hj, Category.assoc, Category.assoc]
      rw [show q ≫ p = t ≫ b from pullback.condition]
    let a := (h i).lift j (k ≫ t) hw
    have ha : a ≫ tᵢ i = k ≫ t := (h i).lift_snd _ _ _
    let α := pullbackComparison t k (a ≫ tᵢ i) ha.symm H₀ ≪≫
      baseChangeCompIso (tᵢ i) a H₀ ≪≫ (baseChange a).mapIso (e i).some ≪≫
      diagonalizableBaseChangeIso a (M i)
    let β := pullbackComparison q k (j ≫ Sigma.ι U i) hj.symm G ≪≫
      baseChangeCompIso (Sigma.ι U i) j G ≪≫
      (baseChange j).mapIso (disjointDiagonalizableComponentIso M i) ≪≫
      diagonalizableBaseChangeIso j (M i)
    exact α ≪≫ β.symm
  let E := DisjointComponents.groupIso (CoproductComponents.toBase q) compare
  exact exists_lift_of_etale_model (IsPullback.of_hasPullback p b) hG H₀ E

end Langlands.GroupScheme.RelativeMultiplicativeType
