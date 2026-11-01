import Langlands.AlgebraicGeometry.Modules.FrameVanishingCriterionProof
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Line bundles from locally associated local equations -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

namespace AssociatedGluing

variable {X : Scheme.{u}}

/-- Two functions on `V` with the same germ at every point of `V` are equal. -/
lemma eq_of_germ_eq {V : X.Opens} {b c : Γ(X, V)}
    (h : ∀ (x : X) (hx : x ∈ V), X.presheaf.germ V x hx b = X.presheaf.germ V x hx c) :
    b = c :=
  TopCat.Presheaf.section_ext X.sheaf V b c h

variable [IsIntegral X]

/-- On an integral scheme, if the germs of `b` and `c` are associated at every point of `V`
and the germs of `c` are nonzero, then `b` is a unit multiple of `c` on `V`. -/
lemma exists_unit_ratio {V : X.Opens} (b c : Γ(X, V))
    (hc : ∀ (x : X) (hx : x ∈ V), X.presheaf.germ V x hx c ≠ 0)
    (hbc : ∀ (x : X) (hx : x ∈ V),
      Associated (X.presheaf.germ V x hx b) (X.presheaf.germ V x hx c)) :
    ∃ u : Γ(X, V), IsUnit u ∧ b = u * c := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hW : W ≤ V) (_ : (x : X) ∈ W) (p : Γ(X, W)),
      X.presheaf.map (homOfLE hW).op b = p * X.presheaf.map (homOfLE hW).op c := by
    intro x
    obtain ⟨w, hw⟩ := hbc x.1 x.2
    obtain ⟨W₁, hW₁, hxW₁, p, hp⟩ :=
      X.presheaf.exists_le_germ_eq (((w⁻¹ : (X.presheaf.stalk x.1)ˣ)) : X.presheaf.stalk x.1) x.2
    have hgerm : X.presheaf.germ V x.1 x.2 b =
        X.presheaf.germ W₁ x.1 hxW₁ (p * X.presheaf.map (homOfLE hW₁).op c) := by
      rw [map_mul, hp, TopCat.Presheaf.germ_res_apply, ← hw,
        mul_comm ((w⁻¹ : (X.presheaf.stalk x.1)ˣ) : X.presheaf.stalk x.1),
        Units.mul_inv_cancel_right]
    obtain ⟨W, hxW, iV, iW, he⟩ := X.presheaf.germ_eq x.1 x.2 hxW₁ _ _ hgerm
    refine ⟨W, iV.le, hxW, X.presheaf.map iW.op p, ?_⟩
    change X.presheaf.map iV.op b = _
    rw [he, map_mul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  choose W hWV hxW p hp using hloc
  have hcover : V ≤ ⨆ x : V, W x := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hres : ∀ (x : V) (Z : X.Opens) (hZ : Z ≤ W x),
      X.presheaf.map (homOfLE (hZ.trans (hWV x))).op b =
        X.presheaf.map (homOfLE hZ).op (p x) *
          X.presheaf.map (homOfLE (hZ.trans (hWV x))).op c := by
    intro x Z hZ
    have h := congrArg (fun t ↦ X.presheaf.map (homOfLE hZ).op t) (hp x)
    simp only [map_mul, CocycleGluing.res_res] at h
    exact h
  have hcZ : ∀ (Z : X.Opens) (hZ : Z ≤ V) (z : X) (hz : z ∈ Z),
      X.presheaf.germ Z z hz (X.presheaf.map (homOfLE hZ).op c) ≠ 0 := by
    intro Z hZ z hz
    rw [TopCat.Presheaf.germ_res_apply]
    exact hc z _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W p := by
    intro x y
    change X.presheaf.map (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op (p x) =
      X.presheaf.map (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op (p y)
    have h1 := hres x (W x ⊓ W y) inf_le_left
    have h2 := hres y (W x ⊓ W y) inf_le_right
    rw [h1] at h2
    apply eq_of_germ_eq
    intro z hz
    apply mul_right_cancel₀ (hcZ _ (inf_le_left.trans (hWV x)) z hz)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun t ↦ X.presheaf.germ (W x ⊓ W y) z hz t) h2
  obtain ⟨v₀, hv, -⟩ :=
    X.sheaf.existsUnique_gluing' W V (fun x ↦ homOfLE (hWV x)) hcover p hcompat
  obtain ⟨v, rfl⟩ : ∃ v : Γ(X, V), v = v₀ := ⟨v₀, rfl⟩
  have hv' : ∀ x : V, X.presheaf.map (homOfLE (hWV x)).op v = p x := hv
  have hbvc : b = v * c := by
    apply eq_of_germ_eq
    intro z hz
    have h := congrArg (fun t ↦ X.presheaf.germ (W ⟨z, hz⟩) z (hxW ⟨z, hz⟩) t) (hp ⟨z, hz⟩)
    simp only [map_mul, TopCat.Presheaf.germ_res_apply, ← hv' ⟨z, hz⟩] at h
    rw [h, map_mul]
  refine ⟨v, X.toRingedSpace.isUnit_of_isUnit_germ V v fun z hz ↦ ?_, hbvc⟩
  obtain ⟨w, hw⟩ := hbc z hz
  have h1 : X.presheaf.germ V z hz b = X.presheaf.germ V z hz v * X.presheaf.germ V z hz c := by
    rw [← map_mul, ← hbvc]
  have h2 : (X.presheaf.germ V z hz v * w) * X.presheaf.germ V z hz c =
      1 * X.presheaf.germ V z hz c := by
    calc (X.presheaf.germ V z hz v * w) * X.presheaf.germ V z hz c
        = (X.presheaf.germ V z hz v * X.presheaf.germ V z hz c) * w := by ring
      _ = X.presheaf.germ V z hz c := by rw [← h1, hw]
      _ = 1 * X.presheaf.germ V z hz c := (one_mul _).symm
  exact IsUnit.of_mul_eq_one _ (mul_right_cancel₀ (hc z hz) h2)

end AssociatedGluing

open AssociatedGluing in
/-- On an integral scheme, local equations `a i` on an open cover `T` whose germs are nonzero
and pairwise associated at every common point are the local expressions of a global section
`s` of a line bundle `L`: the generation open of `s` meets `T i` in the basic open of `a i`,
and `s` vanishes along a morphism landing in `T i` exactly when the pullback of `a i` is
zero. -/
theorem exists_lineBundle_of_associated_equations {X : Scheme.{u}} [IsIntegral X]
    {ι : Type u} (T : ι → X.Opens) (hT : (⨆ i, T i) = ⊤) (a : ∀ i, Γ(X, T i))
    (hreg : ∀ (i : ι) (x : X) (hx : x ∈ T i), X.presheaf.germ (T i) x hx (a i) ≠ 0)
    (hassoc : ∀ (i j : ι) (x : X) (hi : x ∈ T i) (hj : x ∈ T j),
      Associated (X.presheaf.germ (T i) x hi (a i)) (X.presheaf.germ (T j) x hj (a j))) :
    ∃ (L : LineBundle X) (s : GlobalSections L.obj),
      (∀ i, T i ⊓ trivializationOpen L.obj s = X.basicOpen (a i)) ∧
      ∀ (i : ι) (Y : Scheme.{u}) (f : Y ⟶ X) (hf : ⊤ ≤ f ⁻¹ᵁ T i),
        VanishesAlong L f s ↔ f.appLE (T i) ⊤ hf (a i) = 0 := by
  have hex : ∀ i j, ∃ u : Γ(X, T i ⊓ T j), IsUnit u ∧
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) =
        u * X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j) := by
    intro i j
    apply exists_unit_ratio
    · intro x hx
      rw [TopCat.Presheaf.germ_res_apply]
      exact hreg j x _
    · intro x hx
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
      exact hassoc i j x _ _
  choose u hu hrel using hex
  let g : ∀ i j, (Γ(X, T i ⊓ T j))ˣ := fun i j ↦ (hu i j).unit
  have hgerm : ∀ (i j : ι) (z : X) (hi : z ∈ T i) (hj : z ∈ T j),
      X.presheaf.germ (T i) z hi (a i) =
        X.presheaf.germ (T i ⊓ T j) z ⟨hi, hj⟩ (u i j) * X.presheaf.germ (T j) z hj (a j) := by
    intro i j z hi hj
    have h := congrArg (fun t ↦ X.presheaf.germ (T i ⊓ T j) z ⟨hi, hj⟩ t) (hrel i j)
    simpa only [map_mul, TopCat.Presheaf.germ_res_apply] using h
  have hg : CocycleGluing.IsCocycle g := by
    intro i j k
    apply eq_of_germ_eq
    intro z hz
    apply mul_right_cancel₀ (hreg k z hz.2)
    simp only [map_mul, TopCat.Presheaf.germ_res_apply, g, IsUnit.unit_spec]
    rw [mul_assoc, ← hgerm j k z hz.1.2 hz.2, ← hgerm i j z hz.1.1 hz.1.2,
      ← hgerm i k z hz.1.1 hz.2]
  have ha : CocycleGluing.IsCompatibleFamily g a := fun i j ↦ hrel i j
  let L : LineBundle X :=
    ⟨CocycleGluing.glued g, CocycleGluing.isLocallyFreeRankOne_glued g hT hg⟩
  refine ⟨L, CocycleGluing.globalSec g ha,
    CocycleGluing.inf_trivializationOpen_globalSec g hg ha, ?_⟩
  intro i Y f hf
  refine frameVanishingCriterion X L.obj (T i) (CocycleGluing.genSec g hg i le_rfl) (a i)
    (CocycleGluing.globalSec g ha) ?_ ?_ Y f hf
  · intro W hW
    have e : (CocycleGluing.glued g).presheaf.map (homOfLE hW).op
        (CocycleGluing.genSec g hg i le_rfl) = CocycleGluing.genSec g hg i hW :=
      CocycleGluing.map_genSec g hg i hW le_rfl
    change Function.Bijective (fun r : Γ(X, W) ↦ r • (CocycleGluing.glued g).presheaf.map
      (homOfLE hW).op (CocycleGluing.genSec g hg i le_rfl))
    rw [e]
    exact CocycleGluing.smul_genSec_bijective g hg i hW
  · have h := CocycleGluing.map_globalSec g hg ha i (le_rfl : T i ≤ T i)
    rw [CocycleGluing.res_self] at h
    exact h

end Langlands.AlgebraicGeometry.Picard
