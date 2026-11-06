import Langlands.GroupScheme.Reductive.SplitLeviGluingGraph
import Langlands.GroupScheme.GeneratedFamilyBaseChange
import Langlands.GroupScheme.HomScheme.GraphBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GeometricConnectedness

/-! # Actual comparison graph envelopes after field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

section AmbientIso

variable {G G' H : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a : ∀ j, A j ⟶ G} {i : H ⟶ G}

/-- Closed family generation is transported by an actual ambient isomorphism. -/
theorem IsGeneratedByFamily.comp_iso (hi : IsGeneratedByFamily A a i) (e : G ≅ G') :
    IsGeneratedByFamily A (fun j => a j ≫ e.hom) (i ≫ e.hom) := by
  refine ⟨hi.1.comp_iso e, ?_, ?_⟩
  · intro j
    obtain ⟨c, hc⟩ := hi.2.1 j
    refine ⟨c, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hc, Grp.comp_hom_hom]
  · intro Q q hq hfamily
    have hq' : IsClosedSubgroup (q ≫ e.inv) := hq.comp_iso e.symm
    have hfamily' : ∀ j, FactorsThrough (a j).hom.hom (q ≫ e.inv) := by
      intro j
      obtain ⟨c, hc⟩ := hfamily j
      refine ⟨c, ?_⟩
      have h := congrArg (fun f => f ≫ e.inv.hom.hom) hc
      simpa only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom,
        e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using h
    have hle := hi.2.2 Q (q ≫ e.inv) hq' hfamily'
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (hle W (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
    have h := congrArg (fun f => f ≫ e.hom.hom.hom) hz
    simpa only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom,
      e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using h

end AmbientIso

section PairedMaps

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
    {H G₁ G₂ : GroupScheme S}

/-- The product comparison takes the pulled-back pair to the pair of
pulled-back homomorphisms. -/
theorem baseChange_lift_pair (f : H ⟶ G₁) (g : H ⟶ G₂) :
    (GroupScheme.baseChange b).map (lift f g) ≫ (baseChangeTensorIso b G₁ G₂).hom =
      lift ((GroupScheme.baseChange b).map f) ((GroupScheme.baseChange b).map g) := by
  apply hom_ext
  · simp only [Category.assoc, baseChangeTensorIso_hom_fst,
      ← Functor.map_comp, lift_fst]
  · simp only [Category.assoc, baseChangeTensorIso_hom_snd,
      ← Functor.map_comp, lift_snd]

end PairedMaps

namespace LeviGluing

variable (K : Type u) [Field K] [Algebra k K]
    {G₁ G₂ T : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a₁ : ∀ j, A j ⟶ G₁} {a₂ : ∀ j, A j ⟶ G₂}
    {i₁ : T ⟶ G₁} {i₂ : T ⟶ G₂}

namespace GraphEnvelope

variable (D : GraphEnvelope A a₁ a₂ i₁ i₂)
    [Smooth G₁.X.hom] [IsAffineHom G₁.X.hom]
    [Smooth G₂.X.hom] [IsAffineHom G₂.X.hom]
    [Smooth T.X.hom] [IsAffineHom T.X.hom] [ConnectedSpace T.X.left]
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧ ConnectedSpace (A j).X.left)

/-- The actual pullback of a generated graph envelope, placed in the
product of the pulled-back ambient groups, is again a generated graph envelope. -/
def baseChange : GraphEnvelope (fun j => (FamilyBaseChange.bc (k := k) K).obj (A j))
    (fun j => (FamilyBaseChange.bc (k := k) K).map (a₁ j))
    (fun j => (FamilyBaseChange.bc (k := k) K).map (a₂ j))
    ((FamilyBaseChange.bc (k := k) K).map i₁) ((FamilyBaseChange.bc (k := k) K).map i₂) := by
  let b := FamilyBaseChange.extension (k := k) K
  let B := GroupScheme.baseChange b
  let e := baseChangeTensorIso b G₁ G₂
  let : Smooth (G₁ ⊗ G₂).X.hom := smooth_tensor _ _ inferInstance inferInstance
  let : IsAffineHom (G₁ ⊗ G₂).X.hom := by
    change IsAffineHom (pullback.fst G₁.X.hom G₂.X.hom ≫ G₁.X.hom)
    let : IsAffineHom (pullback.fst G₁.X.hom G₂.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom G₂.X.hom)
    infer_instance
  have hfamily : ∀ j, Smooth (graphSources (T := T) A j).X.hom ∧
      IsAffineHom (graphSources (T := T) A j).X.hom ∧
      ConnectedSpace (graphSources (T := T) A j).X.left := by
    rintro (_ | j)
    · exact ⟨inferInstance, inferInstance, inferInstance⟩
    · exact hA j
  have hgen := (IsGeneratedByFamily.baseChange K (graphSources (T := T) A)
    (graphMaps A a₁ a₂ i₁ i₂) hfamily D.generated).comp_iso e
  refine ⟨B.obj D.group, B.map D.inclusion ≫ e.hom, ?_, ?_, ?_, hgen.1, ?_, ?_⟩
  · change Smooth (pullback.snd D.group.X.hom b)
    infer_instance
  · change IsAffineHom (pullback.snd D.group.X.hom b)
    infer_instance
  · exact D.group.connectedSpace_baseChange_of_smooth_affine b
  · rintro (_ | j)
    · simpa only [graphMaps, graphSources, e, B, b, FamilyBaseChange.bc, baseChange_lift_pair] using hgen.2.1 none
    · simpa only [graphMaps, graphSources, e, B, b, FamilyBaseChange.bc, baseChange_lift_pair] using hgen.2.1 (some j)
  · intro Q q hq hf
    apply hgen.2.2 Q q hq
    rintro (_ | j)
    · simpa only [graphMaps, graphSources, e, B, b, FamilyBaseChange.bc, baseChange_lift_pair] using hf none
    · simpa only [graphMaps, graphSources, e, B, b, FamilyBaseChange.bc, baseChange_lift_pair] using hf (some j)

@[simp]
theorem baseChange_first : (D.baseChange K hA).first =
    (FamilyBaseChange.bc (k := k) K).map D.first := by
  simp only [baseChange, first, Category.assoc, baseChangeTensorIso_hom_fst,
    ← Functor.map_comp]

@[simp]
theorem baseChange_second : (D.baseChange K hA).second =
    (FamilyBaseChange.bc (k := k) K).map D.second := by
  simp only [baseChange, second, Category.assoc, baseChangeTensorIso_hom_snd,
    ← Functor.map_comp]

/-- The distinguished torus lift is the actual pullback of the original lift. -/
@[simp]
theorem baseChange_torusLift : (D.baseChange K hA).torusLift =
    (FamilyBaseChange.bc (k := k) K).map D.torusLift := by
  apply (D.baseChange K hA).hom_ext
  · rw [(D.baseChange K hA).torusLift_first, D.baseChange_first K hA]
    exact (congrArg (FamilyBaseChange.bc (k := k) K).map D.torusLift_first).symm.trans
      ((FamilyBaseChange.bc (k := k) K).map_comp D.torusLift D.first)
  · rw [(D.baseChange K hA).torusLift_second, D.baseChange_second K hA]
    exact (congrArg (FamilyBaseChange.bc (k := k) K).map D.torusLift_second).symm.trans
      ((FamilyBaseChange.bc (k := k) K).map_comp D.torusLift D.second)

/-- Each distinguished local lift is the actual pullback of the original local lift. -/
@[simp]
theorem baseChange_localLift (j : I) : (D.baseChange K hA).localLift j =
    (FamilyBaseChange.bc (k := k) K).map (D.localLift j) := by
  apply (D.baseChange K hA).hom_ext
  · rw [(D.baseChange K hA).localLift_first, D.baseChange_first K hA]
    exact (congrArg (FamilyBaseChange.bc (k := k) K).map (D.localLift_first j)).symm.trans
      ((FamilyBaseChange.bc (k := k) K).map_comp (D.localLift j) D.first)
  · rw [(D.baseChange K hA).localLift_second, D.baseChange_second K hA]
    exact (congrArg (FamilyBaseChange.bc (k := k) K).map (D.localLift_second j)).symm.trans
      ((FamilyBaseChange.bc (k := k) K).map_comp (D.localLift j) D.second)

/-- Invertibility of the extended first projection descends over a field extension. -/
theorem isIso_first_of_baseChange [IsIso (D.baseChange K hA).first] : IsIso D.first := by
  have hext : IsIso (D.baseChange K hA).first := inferInstance
  let b := FamilyBaseChange.extension (k := k) K
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : IsIso ((GroupScheme.baseChange b).map D.first) := D.baseChange_first K hA ▸ hext
  exact isIso_of_baseChange b D.first

/-- Invertibility of the extended second projection descends over a field extension. -/
theorem isIso_second_of_baseChange [IsIso (D.baseChange K hA).second] : IsIso D.second := by
  have hext : IsIso (D.baseChange K hA).second := inferInstance
  let b := FamilyBaseChange.extension (k := k) K
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : IsIso ((GroupScheme.baseChange b).map D.second) := D.baseChange_second K hA ▸ hext
  exact isIso_of_baseChange b D.second

/-- Invertibility of the two extended actual graph projections descends
along any field extension to the actual torus-compatible comparison. -/
def comparisonIsoOfBaseChange [IsIso (D.baseChange K hA).first]
    [IsIso (D.baseChange K hA).second] : G₁ ≅ G₂ := by
  let : IsIso D.first := D.isIso_first_of_baseChange K hA
  let : IsIso D.second := D.isIso_second_of_baseChange K hA
  exact D.comparisonIso

/-- The descended actual comparison preserves the supplied common torus. -/
theorem torus_comparisonIsoOfBaseChange [IsIso (D.baseChange K hA).first]
    [IsIso (D.baseChange K hA).second] :
    i₁ ≫ (D.comparisonIsoOfBaseChange K hA).hom = i₂ := by
  let : IsIso D.first := D.isIso_first_of_baseChange K hA
  let : IsIso D.second := D.isIso_second_of_baseChange K hA
  exact D.torus_comparisonIso

end GraphEnvelope
end LeviGluing

end Langlands.GroupScheme
