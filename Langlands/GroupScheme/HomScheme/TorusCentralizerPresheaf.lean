import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints
import Langlands.GroupScheme.HomScheme.TorusCentralizerResidueLocus
import Langlands.GroupScheme.SubgroupFunctor.ClosedZariskiDescent

/-! # The presheaf of smooth closed subgroups with torus-centralizer fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The subgroup on every test is represented by a smooth closed subgroup with
geometrically connected torus-centralizer residue fibres. -/
def IsCentralizerFamily (F : SubgroupFunctor G) : Prop :=
  ∃ (H : GroupScheme S) (i : H ⟶ G), IsClosedSubgroup i ∧ Smooth H.X.hom ∧
    GeometricallyConnected H.X.hom ∧ HasTorusCentralizerResidueFibres i ∧ F.IsRepresentedBy i

/-- Sections remember their literal subgroup on each test scheme. -/
abbrev CentralizerSubgroup (G : GroupScheme S) :=
  {F : SubgroupFunctor G // IsCentralizerFamily F}

/-- A chosen actual representative carries all the defining conditions. -/
structure CentralizerRepresentative (F : SubgroupFunctor G) extends ClosedRepresentative F where
  smooth : Smooth group.X.hom
  connected : GeometricallyConnected group.X.hom
  fibres : HasTorusCentralizerResidueFibres hom

/-- Choose a representative of an actual subgroup family. -/
def centralizerRepresentative (F : CentralizerSubgroup G) : CentralizerRepresentative F.val :=
  Classical.choice (by
    obtain ⟨H, i, hc, hs, hg, hf, hr⟩ := F.property
    exact ⟨⟨⟨H, i, hr, hc⟩, hs, hg, hf⟩⟩)

/-- Closed representability supplies the actual monomorphism in a range. -/
theorem isCentralizerFamily_range {H : GroupScheme S} (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hs : Smooth H.X.hom) (hg : GeometricallyConnected H.X.hom)
    (hf : HasTorusCentralizerResidueFibres i) : IsCentralizerFamily (range i) := by
  let : IsClosedImmersion i.hom.hom.left := hi
  exact ⟨H, i, hi, hs, hg, hf, Over.mono_of_mono_left _, rfl⟩

private def centralizerIdeal (F : CentralizerSubgroup G) : G.X.left.IdealSheafData :=
  (centralizerRepresentative F).hom.hom.hom.left.ker

private theorem centralizerIdeal_injective : Function.Injective (centralizerIdeal (G := G)) := by
  intro F F' h
  apply Subtype.ext
  rw [← (centralizerRepresentative F).represents.2,
    ← (centralizerRepresentative F').represents.2]
  ext T x
  rw [(centralizerRepresentative F).closed.mem_range_iff_ker_le,
    (centralizerRepresentative F').closed.mem_range_iff_ker_le]
  exact (congrArg (fun I => I ≤ x.left.ker) h).to_iff

/-- Closed subgroups are distinguished by their full defining ideals. -/
instance centralizerSubgroupSmall : Small.{u} (CentralizerSubgroup G) :=
  small_of_injective centralizerIdeal_injective

/-- A change of ambient group by an isomorphism preserves the fibre condition. -/
theorem hasTorusCentralizerResidueFibres_comp_iso_iff {H J : GroupScheme S}
    (i : H ⟶ G) (e : G ≅ J) :
    HasTorusCentralizerResidueFibres (i ≫ e.hom) ↔ HasTorusCentralizerResidueFibres i := by
  constructor <;> intro h s
  · have hs := h s
    rw [Functor.map_comp] at hs
    exact (isTorusCentralizer_comp_iso_iff _ ((baseChange (S.fromSpecResidueField s)).mapIso e)).mp hs
  · rw [Functor.map_comp]
    exact (isTorusCentralizer_comp_iso_iff _ ((baseChange (S.fromSpecResidueField s)).mapIso e)).mpr (h s)

/-- A change of source by an isomorphism preserves the fibre condition. -/
theorem hasTorusCentralizerResidueFibres_iso_comp_iff {H J : GroupScheme S}
    (e : H ≅ J) (i : J ⟶ G) :
    HasTorusCentralizerResidueFibres (e.hom ≫ i) ↔ HasTorusCentralizerResidueFibres i := by
  have h (s : S) :
      range ((baseChange (S.fromSpecResidueField s)).map (e.hom ≫ i)) =
        range ((baseChange (S.fromSpecResidueField s)).map i) := by
    rw [Functor.map_comp]
    exact range_iso_comp ((baseChange (S.fromSpecResidueField s)).mapIso e) _
  exact forall_congr' fun s => by rw [h s]

/-- The residue fibre condition depends only on the literal subgroup functor. -/
theorem hasTorusCentralizerResidueFibres_iff_of_range_eq {H J : GroupScheme S}
    {i : H ⟶ G} {j : J ⟶ G} (h : range i = range j) :
    HasTorusCentralizerResidueFibres i ↔ HasTorusCentralizerResidueFibres j := by
  apply forall_congr'
  intro s
  simp only [range_baseChangeHom, h]

theorem hasTorusCentralizerResidueFibres_familyHom_iff {M T : Over S}
    {H : GroupScheme M.left} (i : H ⟶ (baseChange M.hom).obj G) (a : T ⟶ M) :
    HasTorusCentralizerResidueFibres (familyHom i a) ↔
      HasTorusCentralizerResidueFibres ((baseChange a.left).map i) :=
  hasTorusCentralizerResidueFibres_comp_iso_iff _
    (Descent.pullbackComparison M.hom a.left T.hom a.w G)

variable (hG : HasAffineResidueFibers G) {M T U : Over S}

include hG in
/-- Evaluation of an actual family preserves each of its geometric conditions. -/
theorem isCentralizerFamily_evaluate {H : GroupScheme M.left}
    (i : H ⟶ (baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    (hs : Smooth H.X.hom) (hg : GeometricallyConnected H.X.hom)
    (hf : HasTorusCentralizerResidueFibres i) (a : T ⟶ M) :
    IsCentralizerFamily (evaluate i a) := by
  have := hs
  apply isCentralizerFamily_range _ (isClosedSubgroup_familyHom i hi a)
    (MorphismProperty.pullback_snd (P := @Smooth) _ _ hs)
    (MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ hg)
  apply (hasTorusCentralizerResidueFibres_familyHom_iff i a).mpr
  intro s
  exact (isTorusCentralizerAt_baseChange_iff (hG.baseChange M.hom) i hi a.left s).mpr (hf (a.left s))

/-- Restriction uses the actual base-changed subgroup. -/
def restrictCentralizer (a : T ⟶ M) (F : CentralizerSubgroup ((baseChange M.hom).obj G)) :
    CentralizerSubgroup ((baseChange T.hom).obj G) :=
  let r := centralizerRepresentative F
  ⟨evaluate r.hom a, isCentralizerFamily_evaluate hG r.hom r.closed r.smooth r.connected r.fibres a⟩

/-- Restriction does not depend on the chosen actual representative. -/
theorem restrictCentralizer_eq_evaluate {H : GroupScheme M.left}
    (a : T ⟶ M) (F : CentralizerSubgroup ((baseChange M.hom).obj G))
    (i : H ⟶ (baseChange M.hom).obj G) (hi : range i = F.val) :
    (restrictCentralizer hG a F).val = evaluate i a :=
  evaluate_eq_of_range_eq _ _ ((centralizerRepresentative F).represents.2.trans hi.symm) a

/-- Relative restriction and ordinary base change agree under the ambient comparison. -/
theorem restrictCentralizer_val_eq (a : T ⟶ M) (F : CentralizerSubgroup ((baseChange M.hom).obj G)) :
    (restrictCentralizer hG a F).val = (F.val.baseChange a.left).comap
      (Descent.pullbackComparison M.hom a.left T.hom a.w G).inv := by
  simp only [restrictCentralizer, evaluate, familyHom, range_comp_iso, range_baseChangeHom,
    (centralizerRepresentative F).represents.2]

@[simp]
private theorem restrictCentralizer_id (F : CentralizerSubgroup ((baseChange M.hom).obj G)) :
    restrictCentralizer hG (𝟙 M) F = F := by
  apply Subtype.ext
  exact (evaluate_id _).trans (centralizerRepresentative F).represents.2

private theorem restrictCentralizer_comp (a : T ⟶ M) (b : U ⟶ T)
    (F : CentralizerSubgroup ((baseChange M.hom).obj G)) :
    restrictCentralizer hG b (restrictCentralizer hG a F) = restrictCentralizer hG (b ≫ a) F := by
  apply Subtype.ext
  calc
    _ = evaluate (familyHom (centralizerRepresentative F).hom a) b :=
      restrictCentralizer_eq_evaluate hG b _ _ rfl
    _ = _ := evaluate_comp _ a b

/-- The small relative presheaf of actual centralizer families. -/
def centralizerPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (CentralizerSubgroup ((baseChange T.unop.hom).obj G))
  map {T T'} a := TypeCat.ofHom fun x => equivShrink _ (restrictCentralizer hG a.unop ((equivShrink _).symm x))
  map_id _ := by
    apply TypeCat.homEquiv.injective
    funext x
    simp only [unop_id, restrictCentralizer_id, Equiv.apply_symm_apply]
    rfl
  map_comp a b := by
    apply TypeCat.homEquiv.injective
    funext x
    simp only [TypeCat.homEquiv_apply, types_comp_apply, TypeCat.ofHom_apply,
      unop_comp, Equiv.symm_apply_apply, restrictCentralizer_comp]

/-- Decode a small section as an actual subgroup functor. -/
def centralizerEquiv (T : Over S) :
    (centralizerPresheaf hG).obj (op T) ≃ CentralizerSubgroup ((baseChange T.hom).obj G) :=
  (equivShrink _).symm

/-- Presheaf restriction decodes to actual family restriction. -/
@[simp]
theorem centralizerEquiv_map (a : T ⟶ M) (x : (centralizerPresheaf hG).obj (op M)) :
    centralizerEquiv hG T ((centralizerPresheaf hG).map a.op x) =
      restrictCentralizer hG a (centralizerEquiv hG M x) :=
  (equivShrink _).symm_apply_apply _

/-- The absolute presheaf remembers the parameter's structural morphism. -/
def totalCentralizerPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u := (centralizerPresheaf hG).overTotal

end Langlands.GroupScheme.TorusSubgroupModuli
