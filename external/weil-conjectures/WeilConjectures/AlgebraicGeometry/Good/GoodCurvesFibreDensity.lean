/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Fibrewise density in a good curve diagram

Source: Stacks Project, Tag 0GK7, last paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem dense_fibre_open_of_marked_surjective
    {Y B T : Scheme.{u}} (j : Y ⟶ B) (p : B ⟶ T)
    [IsOpenImmersion j] [Smooth p]
    (hc : ∀ s : T, GeometricallyConnected (p.fiberToSpecResidueField s))
    (O : Y.Opens) [Surjective (O.ι ≫ j ≫ p)] (s : T) :
    Dense ((j ≫ p).fiberι s ⁻¹' (O : Set Y)) := by
  have := hc s
  have : Smooth (p.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd p (T.fromSpecResidueField s) inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField s)
  have := IsRegular.of_smooth (p.fiberToSpecResidueField s)
  have : ConnectedSpace (p.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (p.fiberToSpecResidueField s)
  have := IsRegular.irreducibleSpace (p.fiber s)
  let a : (j ≫ p).fiber s ⟶ p.fiber s :=
    (pullbackRightPullbackFstIso p (T.fromSpecResidueField s) j).inv ≫ pullback.snd _ _
  have : IsOpenImmersion a := by dsimp [a]; infer_instance
  have : PreirreducibleSpace ((j ≫ p).fiber s) := a.isOpenEmbedding.preirreducibleSpace
  apply (O.isOpen.preimage ((j ≫ p).fiberι s).continuous).dense
  obtain ⟨y, hy⟩ := (O.ι ≫ j ≫ p).surjective s
  have hy' : (j ≫ p) (O.ι y) = s := by
    simpa only [Scheme.Hom.comp_apply] using hy
  refine ⟨((j ≫ p).fiberHomeo s).symm ⟨O.ι y, hy'⟩, ?_⟩
  change (j ≫ p).fiberι s (((j ≫ p).fiberHomeo s).symm ⟨O.ι y, hy'⟩) ∈ (O : Set Y)
  rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  exact y.property

set_option backward.isDefEq.respectTransparency false in
private theorem dense_fibres_of_cover
    {X V : Scheme.{u}} (f : X ⟶ V) {ι : Type*}
    (Y T : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ T i) (t : ∀ i, T i ⟶ V)
    (a : ∀ i, Y i ⟶ X)
    (ha : ∀ i, a i ≫ f = p i ≫ t i)
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, a i y = x)
    (W : X.Opens)
    (hW : ∀ i (s : T i), Dense ((p i).fiberι s ⁻¹' (a i ⁻¹' (W : Set X)))) :
    ∀ v : V, Dense (f.fiberι v ⁻¹' (W : Set X)) := by
  intro v x
  obtain ⟨i, y, hy⟩ := hcover (f.fiberι v x)
  have hfv : f (f.fiberι v x) = v := (f.fiberHomeo v x).property
  have hty : t i (p i y) = v := by
    rw [← Scheme.Hom.comp_apply, ← ha, Scheme.Hom.comp_apply, hy, hfv]
  let s := p i y
  have hconst (z : (p i).fiber s) : f (a i ((p i).fiberι s z)) = v := by
    rw [← Scheme.Hom.comp_apply, ha, Scheme.Hom.comp_apply]
    have hz : p i ((p i).fiberι s z) = s := ((p i).fiberHomeo s z).property
    rw [hz]
    exact hty
  let b : (p i).fiber s → f.fiber v := fun z ↦
    (f.fiberHomeo v).symm ⟨a i ((p i).fiberι s z), hconst z⟩
  have hb : Continuous b := (f.fiberHomeo v).continuous_symm.comp
    (((a i).continuous.comp ((p i).fiberι s).continuous).subtype_mk hconst)
  have hby : b ((p i).asFiber y) = x := by
    apply (f.fiberHomeo v).injective
    apply Subtype.ext
    simp only [b, Homeomorph.apply_symm_apply, Scheme.Hom.fiberHomeo_apply]
    change a i ((p i).fiberι (p i y) ((p i).asFiber y)) = f.fiberι v x
    rw [Scheme.Hom.fiberι_asFiber]
    exact hy
  have hcl := mem_closure_image hb.continuousAt (hW i s ((p i).asFiber y))
  rw [hby] at hcl
  apply closure_mono (s := b '' ((p i).fiberι s ⁻¹' (a i ⁻¹' (W : Set X)))) ?_ hcl
  rintro z ⟨z', hz', rfl⟩
  simpa only [Set.mem_preimage, b, Scheme.Hom.fiberι_fiberHomeo_symm] using hz'

set_option backward.isDefEq.respectTransparency false in
/-- In a good curve diagram, surjectivity of each marked open onto its constant-field
base implies both required fibrewise densities.

Source: Stacks Project, Tag 0GK7, final paragraph.
(blueprint: lem-weil-pbc-good-curves-fibre-density)

Proof: A smooth geometrically connected fibre is regular and connected, hence
irreducible. Its open subscheme cut out by j is preirreducible. Surjectivity of the
marked open gives a point in each such fibre, so that open is dense. For any point
in a fibre of X over V, lift it through the surjective coproduct map and then to
the corresponding fibre of Y_i over T_i. This fibre maps continuously into the
chosen X fibre. The lifted point lies in the closure of the marked open, so its
image lies in the closure of W. This also proves the empty-family case.
-/
theorem good_curves_fibre_density
    {X V : Scheme.{u}} (f : X ⟶ V) (n : ℕ)
    (T Y B : Fin n → Scheme.{u}) (t : ∀ i, T i ⟶ V)
    (j : ∀ i, Y i ⟶ B i) (p : ∀ i, B i ⟶ T i)
    (ν : (∐ Y) ⟶ X) [Surjective ν]
    (hcomm : ∀ i, Sigma.ι Y i ≫ ν ≫ f = j i ≫ p i ≫ t i)
    (hj : ∀ i, IsOpenImmersion (j i))
    (hp : ∀ i, Smooth (p i))
    (hc : ∀ i (s : T i), GeometricallyConnected ((p i).fiberToSpecResidueField s))
    (W : X.Opens)
    (hW : ∀ i, Surjective (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i)) :
    (∀ v : V, Dense (f.fiberι v ⁻¹' (W : Set X))) ∧
    (∀ i (s : T i), Dense (((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹'
      (W : Set X))) := by
  have hd (i : Fin n) (s : T i) :
      Dense ((j i ≫ p i).fiberι s ⁻¹' ((Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X))) := by
    have := hj i
    have := hp i
    have := hW i
    exact dense_fibre_open_of_marked_surjective (j i) (p i) (hc i) ((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W) s
  refine ⟨?_, ?_⟩
  · refine dense_fibres_of_cover (ι := Fin n) f Y T (fun i ↦ j i ≫ p i) t
      (fun i ↦ Sigma.ι Y i ≫ ν) (fun i ↦ ?_) ?_ W hd
    · simpa only [Category.assoc] using hcomm i
    · intro x
      obtain ⟨z, rfl⟩ := ν.surjective x
      obtain ⟨i, y, rfl⟩ := (sigmaOpenCover Y).exists_eq z
      exact ⟨i, y, rfl⟩
  · intro i s
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] using hd i s

end AlgebraicGeometry
