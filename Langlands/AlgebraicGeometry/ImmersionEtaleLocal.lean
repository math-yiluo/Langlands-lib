import Langlands.AlgebraicGeometry.ImmersionEtaleDescent

/-! # Checking immersions on étale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ImmersionEtaleLocal

variable {X Y U : Scheme.{u}}

/-- The open image of an étale morphism. -/
def etaleImage (p : U ⟶ Y) [Etale p] : Y.Opens :=
  ⟨Set.range p, p.isOpenMap.isOpen_range⟩

/-- An immersion after an étale target base change gives an immersion over
the open image of that base change. -/
theorem isImmersion_restrict_etaleImage (f : X ⟶ Y) (p : U ⟶ Y) [Etale p]
    [IsImmersion (pullback.snd f p)] :
    IsImmersion (f ∣_ etaleImage p) := by
  let W := etaleImage p
  let q : U ⟶ W := IsOpenImmersion.lift W.ι p (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)
  have hq : q ≫ W.ι = p := IsOpenImmersion.lift_fac _ _ _
  have : Surjective q := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := y.property
    refine ⟨z, ?_⟩
    apply W.ι.injective
    change (q ≫ W.ι) z = y.val
    rw [hq]
    exact hz
  have : Etale (q ≫ W.ι) := by rw [hq]; infer_instance
  have : Etale q := Etale.of_comp q W.ι
  let hres := (isPullback_morphismRestrict f W).flip
  have hc : pullback.fst f p ≫ f = (pullback.snd f p ≫ q) ≫ W.ι := by
    rw [Category.assoc, hq, pullback.condition]
  let a := hres.lift (pullback.fst f p) (pullback.snd f p ≫ q) hc
  have ha : a ≫ (f ⁻¹ᵁ W).ι = pullback.fst f p := hres.lift_fst _ _ _
  have hb : a ≫ f ∣_ W = pullback.snd f p ≫ q := hres.lift_snd _ _ _
  have houter : IsPullback (a ≫ (f ⁻¹ᵁ W).ι) (pullback.snd f p) f
      (q ≫ W.ι) := by
    rw [ha, hq]
    exact IsPullback.of_hasPullback f p
  exact ImmersionEtaleDescent.isImmersion_of_isPullback
    (houter.of_right hb hres)

/-- Immersion can be checked after an étale target neighbourhood of every
point. The neighbourhoods need not be quasi-compact or affine. -/
theorem isImmersion_of_etale_neighbourhoods (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ (U : Scheme.{u}) (p : U ⟶ Y),
      Etale p ∧ y ∈ Set.range p ∧ IsImmersion (pullback.snd f p)) :
    IsImmersion f := by
  classical
  choose U p hp hmem hI using h
  let (y : Y) : Etale (p y) := hp y
  let W : Y → Y.Opens := fun y => etaleImage (p y)
  have hW : iSup W = ⊤ := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsImmersion) W hW
  intro y
  let : IsImmersion (pullback.snd f (p y)) := hI y
  exact isImmersion_restrict_etaleImage f (p y)

end Langlands.AlgebraicGeometry.ImmersionEtaleLocal
