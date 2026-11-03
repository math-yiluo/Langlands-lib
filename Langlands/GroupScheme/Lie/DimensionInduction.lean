import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Induction on the dimension of the actual Lie kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace Lie

/-- The dimension of the original dual-number Lie kernel over the ground field. -/
def dimension (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] : ℕ :=
  Module.finrank k (Additive (lieKernel G k))

/-- A smooth closed subgroup with surjective tangent map is an isomorphic presentation
of the connected ambient smooth affine group. -/
theorem isIso_of_surjective_targetMapLinear
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hsurj : Function.Surjective (targetMapLinear j k)) : IsIso j := by
  have hrange : SubgroupFunctor.range j = ⊤ := by
    apply lieSubgroupEquality k G H j hj
    intro X
    obtain ⟨Y, hY⟩ := hsurj (Additive.ofMul X)
    exact ⟨Y.toMul, congrArg (fun Z => Z.toMul.val) hY⟩
  have : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (⊤ : SubgroupFunctor G).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, hrange⟩
  have hidrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨x, Category.comp_id x⟩
  let e : H ≅ G := hjrep.isoOfIsRepresentedBy hidrep
  have he : e.hom = j := by
    simpa using hjrep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

/-- A proper smooth closed subgroup has strictly smaller Lie dimension when the
smooth affine ambient group is connected. The subgroup need not be connected. -/
theorem dimension_lt_of_proper_closedSubgroup
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j) (hproper : ¬ IsIso j) :
    dimension H < dimension G := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hinj := targetMapLinear_injective j k
  have hle : dimension H ≤ dimension G :=
    LinearMap.finrank_le_finrank_of_injective hinj
  apply lt_of_le_of_ne hle
  intro heq
  apply hproper
  apply isIso_of_surjective_targetMapLinear j hj
  exact (LinearEquiv.ofInjectiveOfFinrankEq (targetMapLinear j k) hinj heq).surjective

end Lie

/-- Strong induction on the actual Lie dimension of smooth connected affine groups.
Its induction hypothesis applies to all groups of smaller dimension, including
quotients once their dimension decrease has been proved. -/
theorem smoothConnectedAffineGroup_lieDimension_induction
    (P : GroupScheme (Spec (CommRingCat.of k)) → Prop)
    (step : ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      (∀ (H : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
        Lie.dimension H < Lie.dimension G → P H) → P G)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] : P G := by
  have h : ∀ n : ℕ, ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H = n → P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ _ hH
      apply step H
      intro K _ _ _ hK
      exact ih (Lie.dimension K) (by simpa only [hH] using hK) K rfl
  exact h (Lie.dimension G) G rfl

end Langlands.GroupScheme
