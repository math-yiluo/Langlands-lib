import Langlands.GroupScheme.Reductive.AffinePinnedAtlasDatum
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # The invariant positive-coroot cocharacter on a pinned atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

/-- Normalized restriction conjugates an actual endomorphism by the endpoint comparison. -/
theorem pullbackCocharacter_comp_pullIso {S T U : Scheme.{u}} {G : GroupScheme S}
    (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ p = r)
    (χ : (Gm T).toGrp ⟶ (baseChange p).obj G)
    (e : (baseChange p).obj G ≅ (baseChange p).obj G) :
    pullbackCocharacter p q r h (χ ≫ e.hom) =
      pullbackCocharacter p q r h χ ≫ (Descent.pullIso q h h e).hom := by
  simp [pullbackCocharacter, baseChangeCocharacter_comp_hom, Descent.pullIso,
    Category.assoc]

end Dynamic

namespace AffinePinnedChart

open Descent

variable {S T : Scheme.{u}} {G : GroupScheme S}

/-- The chart's positive-coroot cocharacter in the original chart pullback. -/
def cocharacter (C : AffinePinnedChart G) :
    (Gm C.model.base).toGrp ⟶ (baseChange C.map).obj G :=
  BasedBorelTransport.cocharacter C.model.inclusion C.model.rootDatum C.model.basis ≫
    C.iso.inv

/-- Pulling the chart cocharacter back gives its normalized original-group value. -/
theorem cocharacter_pull (C : AffinePinnedChart G) (f : T ⟶ C.model.base)
    (k : T ⟶ S) (hf : f ≫ C.map = k) :
    Dynamic.pullbackCocharacter C.map f k hf C.cocharacter =
      C.cocharacterInOriginal f k hf := by
  simp only [Dynamic.pullbackCocharacter, cocharacter,
    Dynamic.baseChangeCocharacter_comp_hom,
    BasedBorelTransport.cocharacter_baseChange, cocharacterInOriginal,
    AffinePinnedModel.cocharacterOver, AffinePinnedModel.inclusionOver,
    identify, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]

end AffinePinnedChart

namespace AffinePinnedAtlas

open Descent CoproductComponents Langlands.GroupScheme.Dynamic

variable {S T W : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)

local instance inclusions_isIso : IsIso (Sigma.desc A.inclusion) := by
  simpa only [inclusion, Sigma.desc_ι] using (inferInstance : IsIso (𝟙 A.space))

/-- Assemble the chart cocharacters on the actual atlas group. -/
def cocharacter : (Gm A.space).toGrp ⟶ A.group :=
  DisjointComponents.groupHom A.inclusion (fun i =>
    (Gm.baseChangeIso (A.inclusion i)).hom ≫ (A.chart i).cocharacter ≫
      (pullbackComparison A.projection (A.inclusion i) (A.chart i).map
        (A.inclusion_projection i) G).inv)

/-- Its direct pullback along a component inclusion is the original chart value. -/
theorem cocharacter_on_component (i : S) :
    pullbackCocharacter A.projection (A.inclusion i) (A.chart i).map
      (A.inclusion_projection i) A.cocharacter = (A.chart i).cocharacter := by
  simp [pullbackCocharacter, baseChangeCocharacter, cocharacter]

/-- Evaluate the atlas cocharacter at any actual chart coordinate. -/
theorem cocharacter_on_chart (a : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (i : S) (f : T ⟶ (A.chart i).model.base)
    (hf : f ≫ A.inclusion i = a) :
    pullbackCocharacter A.projection a k ha A.cocharacter =
      (A.chart i).cocharacterInOriginal f k
        (by rw [← A.inclusion_projection i, ← Category.assoc, hf, ha]) := by
  have h := pullbackCocharacter_recovers A.projection (A.inclusion i) (A.chart i).map
    (A.inclusion_projection i) f a k hf ha
    (by rw [← A.inclusion_projection i, ← Category.assoc, hf, ha]) A.cocharacter
  rw [show pullbackCocharacter A.projection (A.inclusion i) (A.chart i).map
      (A.inclusion_projection i) A.cocharacter = (A.chart i).cocharacter from
    A.cocharacter_on_component i] at h
  exact h.symm.trans ((A.chart i).cocharacter_pull f k _)

/-- Normalized cocharacter restrictions detect equality on a disjoint decomposition. -/
private theorem cocharacter_ext_along {B : Scheme.{u}} {H : GroupScheme B}
    {I : Type u} {Z : I → Scheme.{u}} (q : ∀ i, Z i ⟶ B)
    [IsIso (Sigma.desc q)] {χ ψ : (Gm B).toGrp ⟶ H}
    (h : ∀ i, baseChangeCocharacter (q i) χ = baseChangeCocharacter (q i) ψ) :
    χ = ψ := by
  apply DisjointComponents.groupHom_ext q
  intro i
  exact (cancel_epi (Gm.baseChangeIso (q i)).inv).mp (h i)

/-- Pairs of actual chart coordinates detect equality of cocharacters. -/
theorem cocharacter_ext_on_charts (a b : T ⟶ A.space) (k : T ⟶ S)
    {χ ψ : (Gm T).toGrp ⟶ (baseChange k).obj G}
    (h : ∀ (V : Scheme.{u}) (i j : S) (q : V ⟶ T)
      (f : V ⟶ (A.chart i).model.base) (g : V ⟶ (A.chart j).model.base),
      f ≫ A.inclusion i = q ≫ a → g ≫ A.inclusion j = q ≫ b →
      pullbackCocharacter k q (q ≫ k) rfl χ =
        pullbackCocharacter k q (q ≫ k) rfl ψ) : χ = ψ := by
  apply cocharacter_ext_along (toBase a)
  intro i
  apply cocharacter_ext_along (toBase (toBase a i ≫ b))
  intro j
  let q := toBase (toBase a i ≫ b) j ≫ toBase a i
  apply (cancel_mono (pullbackComparison (toBase a i)
    (toBase (toBase a i ≫ b) j) q rfl ((baseChange k).obj G)).hom).mp
  rw [baseChangeCocharacter_tower, baseChangeCocharacter_tower]
  apply (cancel_mono (pullbackComparison k q (q ≫ k) rfl G).hom).mp
  apply h _ i j q
    (toBase (toBase a i ≫ b) j ≫ toComponent a i)
    (toComponent (toBase a i ≫ b) j)
  · simp only [q, Category.assoc, component_condition]
  · simpa only [q, Category.assoc] using component_condition (toBase a i ≫ b) j

/-- Corrected atlas transitions carry the assembled direct cocharacters to each other. -/
theorem transition_cocharacter (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    pullbackCocharacter A.projection a k ha A.cocharacter ≫
        (A.transition P a b k ha hb).hom =
      pullbackCocharacter A.projection b k hb A.cocharacter := by
  apply A.cocharacter_ext_on_charts a b k
  intro V i j q f g hf hg
  rw [pullbackCocharacter_comp_pullIso, A.transition_on_charts P a b k ha hb
    i j q f g hf hg _ rfl]
  have hχa := pullbackCocharacter_recovers A.projection a k ha q (q ≫ a)
    (q ≫ k) rfl (by rw [Category.assoc, ha]) rfl A.cocharacter
  have hχb := pullbackCocharacter_recovers A.projection b k hb q (q ≫ b)
    (q ≫ k) rfl (by rw [Category.assoc, hb]) rfl A.cocharacter
  change pullbackCocharacter k q (q ≫ k) rfl
      (pullbackCocharacter A.projection a k ha A.cocharacter) =
    pullbackCocharacter A.projection (q ≫ a) (q ≫ k)
      (by rw [Category.assoc, ha]) A.cocharacter at hχa
  change pullbackCocharacter k q (q ≫ k) rfl
      (pullbackCocharacter A.projection b k hb A.cocharacter) =
    pullbackCocharacter A.projection (q ≫ b) (q ≫ k)
      (by rw [Category.assoc, hb]) A.cocharacter at hχb
  rw [hχa, hχb,
    A.cocharacter_on_chart (q ≫ a) (q ≫ k) _ i f hf,
    A.cocharacter_on_chart (q ≫ b) (q ≫ k) _ j g hg]
  exact AffinePinnedChart.transition_cocharacter P _ _ _ _ _ _ _

/-- The actual atlas transitions preserve the normalized atlas cocharacter. -/
theorem actualTransition_cocharacter (P : RelativePinnedComparison.{u})
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    baseChangeCocharacter a A.cocharacter ≫
        (A.actualTransition P a b k ha hb).hom =
      baseChangeCocharacter b A.cocharacter := by
  apply (cancel_mono (pullbackComparison A.projection b k hb G).hom).mp
  simpa only [actualTransition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, pullbackCocharacter] using
    A.transition_cocharacter P a b k ha hb

/-- The two atlas cocharacters agree across the actual descent overlap. -/
theorem overlap_cocharacter (P : RelativePinnedComparison.{u}) :
    baseChangeCocharacter (fst A.projection) A.cocharacter ≫ (A.overlap P).hom =
      baseChangeCocharacter (snd A.projection) A.cocharacter :=
  A.actualTransition_cocharacter P _ _ _ rfl pullback.condition.symm

end AffinePinnedAtlas

end Langlands.GroupScheme
