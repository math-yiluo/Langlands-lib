import Langlands.GroupScheme.Lie.TorusLieCentralizerStatements
import Langlands.GroupScheme.Lie.CommutingSemisimpleTorus
import Langlands.GroupScheme.Lie.ElementCentralizerTorus
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Lie.SplitTorusSemisimple
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties

/-! # Proof: maximal tori centralize commuting semisimple Lie elements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimple Lie elements commuting with the Lie algebra of a maximal torus.** Over an
algebraically closed field, a maximal torus `T₀` of a smooth connected affine group
centralizes, over every test scheme, each semisimple Lie element whose Lie centralizer
contains all tangent vectors of `T₀`. -/
theorem semisimpleMaximalTorusLieCentralizer :
    SemisimpleMaximalTorusLieCentralizerStatement.{u} := by
  intro k _ _ G _ _ _ T₀ j₀ hj₀ Y hY hcomm
  classical
  have : IsClosedImmersion j₀.hom.hom.left := hj₀.2.1
  have : IsAffineHom T₀.toGrp.X.hom := by
    rw [← Over.w j₀.hom.hom]
    infer_instance
  have : Mono j₀.hom.hom := Over.mono_of_mono_left _
  have hsplit : IsSplitTorus T₀.toGrp :=
    hj₀.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  let V := LinearMap.range (Lie.targetMapLinear j₀ k)
  let b := Module.finBasis k V
  let f : Fin (Module.finrank k V) → lieKernel G k := fun m =>
    Additive.toMul (b m : Additive (lieKernel G k))
  have hf : ∀ m, ∃ t : lieKernel T₀.toGrp k, Lie.targetMap j₀ k t = f m := by
    intro m
    obtain ⟨t, ht⟩ := (b m).2
    exact ⟨t.toMul, congrArg Additive.toMul ht⟩
  let l : List (lieKernel G k) := Y :: List.ofFn f
  have hsem : ∀ X ∈ l, Lie.IsSemisimpleElement G X := by
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact hY
    · obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hX
      obtain ⟨t, ht⟩ := hf m
      rw [← ht]
      exact (Lie.isSemisimpleElement_of_isSplitTorus hsplit t).map j₀
  have hpair : l.Pairwise (fun X Z => Additive.ofMul Z ∈ Lie.elementCentralizerLie G X) := by
    rw [List.pairwise_cons]
    refine ⟨?_, List.pairwise_of_forall_mem_list ?_⟩
    · intro Z hZ
      obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hZ
      obtain ⟨t, ht⟩ := hf m
      rw [← ht]
      exact hcomm t
    · intro X hX Z hZ
      obtain ⟨m, rfl⟩ := List.mem_ofFn.mp hX
      obtain ⟨m', rfl⟩ := List.mem_ofFn.mp hZ
      obtain ⟨t, ht⟩ := hf m
      obtain ⟨t', ht'⟩ := hf m'
      rw [← ht, ← ht']
      exact Lie.range_le_elementCentralizer_target j₀ t _
        (SubgroupFunctor.mem_range.mpr ⟨t'.val, rfl⟩)
  obtain ⟨S, i, hi, hS⟩ :=
    Lie.exists_isMaximalTorus_forall_tangent_of_pairwise l.length G l rfl hsem hpair
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : IsAffineHom S.toGrp.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let W := LinearMap.range (Lie.targetMapLinear i k)
  have hVW : V ≤ W := by
    have hspan : Submodule.map V.subtype (Submodule.span k (Set.range b)) ≤ W := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      obtain ⟨Z, hZ⟩ := hS (f m) (List.mem_cons_of_mem Y (List.mem_ofFn.mpr ⟨m, rfl⟩))
      exact ⟨Additive.ofMul Z, congrArg Additive.ofMul hZ⟩
    rwa [b.span_eq, Submodule.map_subtype_top] at hspan
  obtain ⟨g, φ, -⟩ := maximalTorusConjugacy k G T₀ S j₀ i hj₀ hi
  let e : T₀.toGrp ≅ S.toGrp :=
    { hom := CommGroupScheme.groupHom φ.hom
      inv := CommGroupScheme.groupHom φ.inv
      hom_inv_id := congrArg Additive.toMul φ.hom_inv_id
      inv_hom_id := congrArg Additive.toMul φ.inv_hom_id }
  have hrank : Module.finrank k V = Module.finrank k W := by
    rw [LinearMap.finrank_range_of_inj (Lie.targetMapLinear_injective j₀ k),
      LinearMap.finrank_range_of_inj (Lie.targetMapLinear_injective i k)]
    exact Lie.dimension_eq_of_iso e
  have hVeq : V = W := Submodule.eq_of_le_of_finrank_eq hVW hrank
  obtain ⟨Z, hZ⟩ := hS Y List.mem_cons_self
  have hYV : Additive.ofMul Y ∈ V := by
    rw [hVeq]
    exact ⟨Additive.ofMul Z, congrArg Additive.ofMul hZ⟩
  obtain ⟨t, ht⟩ := hYV
  exact Lie.range_le_elementCentralizer_of_tangent j₀ ⟨t.toMul, congrArg Additive.toMul ht⟩

end Langlands.GroupScheme
