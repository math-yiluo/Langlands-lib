import Langlands.AlgebraicGeometry.Deformation.ElementaryReductionProducts

/-! # Lifting a multiplication along the two unit axes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts
open AffineOpenQuotientSections
open AffineOpenQuotientSections.Reduction (product_isPullback)
open Picard.FieldTwoAxisH1Injectivity
open SmoothProperConnectedGlobalFunctionsProof (secHom)

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {I : Ideal R} {Z : Target R}

local notation "S" => Spec (CommRingCat.of R)
local notation "T" => Over.mk (𝟙 S)

section Axes

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {X : C}

/-- The first factor through the chosen section of the second factor. -/
def leftAxis (e : 𝟙_ C ⟶ X) : X ⟶ X ⊗ X := lift (𝟙 X) (toUnit X ≫ e)

/-- The second factor through the chosen section of the first factor. -/
def rightAxis (e : 𝟙_ C ⟶ X) : X ⟶ X ⊗ X := lift (toUnit X ≫ e) (𝟙 X)

@[simp] lemma leftAxis_mul [MonObj X] : leftAxis η[X] ≫ μ[X] = 𝟙 X :=
  MonObj.lift_comp_one_right _ _

@[simp] lemma rightAxis_mul [MonObj X] : rightAxis η[X] ≫ μ[X] = 𝟙 X :=
  MonObj.lift_comp_one_left _ _

end Axes

variable {X : Over (Spec (CommRingCat.of R))}

omit [IsLocalRing R] in
@[simp] lemma map_leftAxis {L : Ideal R} (A : Reduction X L) (e : T ⟶ X) :
    A.map (A.fibreProduct A) (leftAxis e) = leftAxis ((baseReduction L).map A e) := by
  simp only [leftAxis, Reduction.map_lift, Reduction.map_id,
    A.map_comp (baseReduction L) A, Reduction.map_toUnit]

omit [IsLocalRing R] in
@[simp] lemma map_rightAxis {L : Ideal R} (A : Reduction X L) (e : T ⟶ X) :
    A.map (A.fibreProduct A) (rightAxis e) = rightAxis ((baseReduction L).map A e) := by
  simp only [rightAxis, Reduction.map_lift, Reduction.map_id,
    A.map_comp (baseReduction L) A, Reduction.map_toUnit]

private lemma preimage_section_cases [IsArtinianRing R] (e : T ⟶ X) (U : X.left.Opens) :
    e.left ⁻¹ᵁ U = ⊤ ∨ e.left ⁻¹ᵁ U = ⊥ := by
  classical
  let pt := IsLocalRing.closedPoint R
  have hs : Subsingleton S := spec_subsingleton
  by_cases hm : e.left pt ∈ U
  · left
    apply top_le_iff.mp
    intro z _
    change e.left z ∈ U
    exact (@Subsingleton.elim S hs pt z) ▸ hm
  · right
    apply le_bot_iff.mp
    intro z hz
    exact (hm ((@Subsingleton.elim S hs z pt) ▸ hz)).elim

private lemma leftAxis_affine [IsArtinianRing R] (e : T ⟶ X) {U V : X.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen ((leftAxis e).left ⁻¹ᵁ prodOpen (fst X X).left (snd X X).left U V) := by
  have h₁ : (leftAxis e).left ≫ (fst X X).left = 𝟙 X.left :=
    congrArg (fun f : X ⟶ X ↦ f.left) (lift_fst (𝟙 X) (toUnit X ≫ e))
  have h₂ : (leftAxis e).left ≫ (snd X X).left = X.hom ≫ e.left :=
    congrArg (fun f : X ⟶ X ↦ f.left) (lift_snd (𝟙 X) (toUnit X ≫ e))
  rw [prodOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    h₁, h₂, Scheme.Hom.id_preimage, Scheme.Hom.comp_preimage]
  rcases preimage_section_cases e V with h | h
  · rwa [h, Scheme.Hom.preimage_top, inf_top_eq]
  · rw [h, Scheme.Hom.preimage_bot, inf_bot_eq]
    exact isAffineOpen_bot _

private lemma rightAxis_affine [IsArtinianRing R] (e : T ⟶ X) {U V : X.left.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen ((rightAxis e).left ⁻¹ᵁ prodOpen (fst X X).left (snd X X).left U V) := by
  have h₁ : (rightAxis e).left ≫ (fst X X).left = X.hom ≫ e.left :=
    congrArg (fun f : X ⟶ X ↦ f.left) (lift_fst (toUnit X ≫ e) (𝟙 X))
  have h₂ : (rightAxis e).left ≫ (snd X X).left = 𝟙 X.left :=
    congrArg (fun f : X ⟶ X ↦ f.left) (lift_snd (toUnit X ≫ e) (𝟙 X))
  rw [prodOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    h₁, h₂, Scheme.Hom.id_preimage, Scheme.Hom.comp_preimage]
  rcases preimage_section_cases e U with h | h
  · rwa [h, Scheme.Hom.preimage_top, top_inf_eq]
  · rw [h, Scheme.Hom.preimage_bot, bot_inf_eq]
    exact isAffineOpen_bot _

/-- The residue fibre in the presentation with its group law. -/
def targetFibre (Z : Target R) : Reduction Z.X (maximalIdeal R) :=
  ⟨Z.G.X, Z.i, Z.fibre⟩

omit [IsLocalRing R] in
private lemma map_eq_of_left {Y W : Over S} {L : Ideal R}
    (A : Reduction Y L) (B : Reduction W L) {f : Y ⟶ W} {g : A.obj ⟶ B.obj}
    (h : A.toOriginal ≫ f.left = g.left ≫ B.toOriginal) : A.map B f = g := by
  apply Over.OverMorphism.ext
  exact (cancel_mono B.toOriginal).mp ((A.map_left_toOriginal f).trans h)

section Field

variable {k : Type u} [Field k] {F : Over (Spec (CommRingCat.of k))}

-- The cover of the fibre is specified up to equality of families of opens.
private theorem product_coboundary {Idx : Type*} [Finite Idx] (U : Idx → F.left.Opens)
    (hU : ∀ a, IsAffineOpen (U a)) (hUU : ∀ a c, IsAffineOpen (U a ⊓ U c))
    (hc : ⊤ ≤ iSup U) (hglob : Function.Surjective (secHom F.hom ⊤).hom)
    (e : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ F)
    (V : (Idx × Idx) → (F ⊗ F).left.Opens)
    (hV : V = prodCover (fst F F).left (snd F F).left U U)
    (z : ∀ a c, Γ((F ⊗ F).left, V a ⊓ V c))
    (hz : ∀ a c d {O : (F ⊗ F).left.Opens} (h₁ : O ≤ V a ⊓ V c) (h₂ : O ≤ V c ⊓ V d)
      (h₃ : O ≤ V a ⊓ V d),
      ((F ⊗ F).left.presheaf.map (homOfLE h₁).op).hom (z a c) +
        ((F ⊗ F).left.presheaf.map (homOfLE h₂).op).hom (z c d) =
        ((F ⊗ F).left.presheaf.map (homOfLE h₃).op).hom (z a d))
    (hl : ∃ g : ∀ a, Γ(F.left, (leftAxis e).left ⁻¹ᵁ V a), ∀ a c,
      ((leftAxis e).left.app (V a ⊓ V c)).hom (z a c) =
        (F.left.presheaf.map (homOfLE ((leftAxis e).left.preimage_mono inf_le_right)).op).hom (g c) -
          (F.left.presheaf.map (homOfLE ((leftAxis e).left.preimage_mono inf_le_left)).op).hom (g a))
    (hr : ∃ g : ∀ a, Γ(F.left, (rightAxis e).left ⁻¹ᵁ V a), ∀ a c,
      ((rightAxis e).left.app (V a ⊓ V c)).hom (z a c) =
        (F.left.presheaf.map (homOfLE ((rightAxis e).left.preimage_mono inf_le_right)).op).hom (g c) -
          (F.left.presheaf.map (homOfLE ((rightAxis e).left.preimage_mono inf_le_left)).op).hom (g a)) :
    ∃ y : ∀ a, Γ((F ⊗ F).left, V a), ∀ a c,
      z a c = ((F ⊗ F).left.presheaf.map (homOfLE inf_le_right).op).hom (y c) -
        ((F ⊗ F).left.presheaf.map (homOfLE inf_le_left).op).hom (y a) := by
  subst V
  let _ : ∀ W : F.left.Opens, Algebra k Γ(F.left, W) := fun W ↦ (secHom F.hom W).hom.toAlgebra
  obtain ⟨a, ha⟩ := exists_top_le_preimage (R := CommRingCat.of k) (Field.toIsField k) e.left hc
  refine exists_coboundary_of_axes (fun _ ↦ rfl) (fun _ ↦ rfl) (Field.toIsField k)
    (product_isPullback F F) U U hU hUU hU hUU hc hc hglob hglob e.left (Over.w e) a ha
    e.left (Over.w e) a ha (leftAxis e).left ?_ ?_ (rightAxis e).left ?_ ?_ z hz hl hr
  · exact congrArg (fun f : F ⟶ F ↦ f.left) (lift_fst (𝟙 F) (toUnit F ≫ e))
  · exact congrArg (fun f : F ⟶ F ↦ f.left) (lift_snd (𝟙 F) (toUnit F ≫ e))
  · exact congrArg (fun f : F ⟶ F ↦ f.left) (lift_fst (toUnit F ≫ e) (𝟙 F))
  · exact congrArg (fun f : F ⟶ F ↦ f.left) (lift_snd (toUnit F ≫ e) (𝟙 F))

end Field

section Lifting

variable [IsArtinianRing R] [Fact (maximalIdeal R * I = ⊥)] [Smooth Z.X.hom] [IsProper Z.X.hom]
  [GeometricallyConnected Z.G.X.hom]

/-- The multiplication of the reduction lifts as a morphism, and can be chosen to take
the prescribed value at the pair of unit sections. -/
theorem exists_multiplication_lift (hI : I ≤ maximalIdeal R) (b : Z.Coordinates I)
    (B : Reduction Z.X I) [GrpObj B.obj] (e : T ⟶ Z.X) (he : (baseReduction I).map B e = η[B.obj]) :
    ∃ g : Z.X ⊗ Z.X ⟶ Z.X, (B.fibreProduct B).map B g = μ[B.obj] ∧ lift e e ≫ g = e := by
  classical
  let X := Z.X
  let P := X ⊗ X
  let F := targetFibre Z
  let D := B.fibreProduct B
  let H := F.fibreProduct F
  let g₀ := μ[B.obj].left ≫ B.toOriginal
  have hg₀ : g₀ ≫ X.hom = D.toOriginal ≫ P.hom := by
    dsimp only [g₀]
    rw [Category.assoc, B.cartesian.w, Over.w_assoc, D.cartesian.w]
    rfl
  let _ : Smooth P.hom := by
    change Smooth (pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  let _ : IsProper P.hom := by
    change IsProper (pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  have : Smooth F.obj.hom := MorphismProperty.of_isPullback F.cartesian inferInstance
  have : IsProper F.obj.hom := MorphismProperty.of_isPullback F.cartesian inferInstance
  have : GeometricallyConnected F.obj.hom := ‹GeometricallyConnected Z.G.X.hom›
  obtain ⟨Idx, hFinite, U, hU, hUU, hc⟩ := exists_affineCover X.hom
  let V := prodCover (fst X X).left (snd X X).left U U
  have hV (a : Idx × Idx) : IsAffineOpen (V a) :=
    isAffineOpen_prodOpen (product_isPullback X X) (hU a.1) (hU a.2)
  have hVc : ⊤ ≤ iSup V := iSup_prodOpen_eq_top hc hc
  choose x hx using fun a ↦ exists_localLift D hI hg₀ (hV a)
  let eₖ := (baseReduction (maximalIdeal R)).map F e
  have hleft : B.toOriginal ≫ Over.Hom.left (𝟙 X) = (B.map D (leftAxis e)).left ≫ g₀ := by
    have h : B.map D (leftAxis e) ≫ μ[B.obj] = 𝟙 B.obj := by
      change B.map (B.fibreProduct B) (leftAxis e) ≫ μ[B.obj] = 𝟙 B.obj
      rw [map_leftAxis, he, leftAxis_mul]
    change B.toOriginal ≫ 𝟙 X.left = (B.map D (leftAxis e)).left ≫ μ[B.obj].left ≫ B.toOriginal
    rw [← Over.comp_left_assoc, h, Over.id_left, Category.id_comp, Category.comp_id]
  have hright : B.toOriginal ≫ Over.Hom.left (𝟙 X) = (B.map D (rightAxis e)).left ≫ g₀ := by
    have h : B.map D (rightAxis e) ≫ μ[B.obj] = 𝟙 B.obj := by
      change B.map (B.fibreProduct B) (rightAxis e) ≫ μ[B.obj] = 𝟙 B.obj
      rw [map_rightAxis, he, rightAxis_mul]
    change B.toOriginal ≫ 𝟙 X.left = (B.map D (rightAxis e)).left ≫ μ[B.obj].left ≫ B.toOriginal
    rw [← Over.comp_left_assoc, h, Over.id_left, Category.id_comp, Category.comp_id]
  have hl (a : Idx × Idx) : IsAffineOpen ((leftAxis e).left ⁻¹ᵁ V a) := leftAxis_affine e (hU a.1)
  have hr (a : Idx × Idx) : IsAffineOpen ((rightAxis e).left ⁻¹ᵁ V a) := rightAxis_affine e (hU a.2)
  have hl' (a c : Idx × Idx) : IsAffineOpen ((leftAxis e).left ⁻¹ᵁ (V a ⊓ V c)) :=
    affine_inf (hl a) (hl c)
  have hr' (a c : Idx × Idx) : IsAffineOpen ((rightAxis e).left ⁻¹ᵁ (V a ⊓ V c)) :=
    affine_inf (hr a) (hr c)
  let Uₖ (a : Idx) := F.toOriginal ⁻¹ᵁ U a
  let Vₖ (a : Idx × Idx) := H.toOriginal ⁻¹ᵁ V a
  have hVₖ : Vₖ = prodCover (fst F.obj F.obj).left (snd F.obj F.obj).left Uₖ Uₖ :=
    funext fun a ↦ F.fibreProduct_preimage_prodOpen F (U a.1) (U a.2)
  have hL : F.map H (leftAxis e) = leftAxis eₖ := map_leftAxis F e
  have hR : F.map H (rightAxis e) = rightAxis eₖ := map_rightAxis F e
  have hprimitive (j : Fin b.cotangentRank × Fin b.idealRank) :=
    product_coboundary (k := ResidueField R) Uₖ (fun a ↦ F.affine_preimage (hU a))
      (fun a c ↦ F.affine_preimage (hUU a c)) (F.cover_preimage U hc)
      (surjective_secHom_top F.obj.hom) eₖ Vₖ hVₖ (fun a c ↦ cocycle D b H V hV x hx a c j)
      (fun a c d _ h₁ h₂ h₃ ↦ cocycle_condition D b H V hV x hx a c d h₁ h₂ h₃ j) (by
        have h := cocycle_pullback_coboundary D B H F b (leftAxis e) V hV x hx hl hl' (𝟙 X) hleft j
        rw [hL] at h
        exact h) (by
        have h := cocycle_pullback_coboundary D B H F b (rightAxis e) V hV x hx hr hr' (𝟙 X) hright j
        rw [hR] at h
        exact h)
  choose d hd using hprimitive
  have heq (a c : Idx × Idx) (j : Fin b.cotangentRank × Fin b.idealRank) :
      cocycle D b H V hV x hx a c j =
        (H.obj.left.presheaf.map (homOfLE (H.toOriginal.preimage_mono
          (show V a ⊓ V c ≤ V a from inf_le_left))).op).hom (-d j a) -
        (H.obj.left.presheaf.map (homOfLE (H.toOriginal.preimage_mono
          (show V a ⊓ V c ≤ V c from inf_le_right))).op).hom (-d j c) := by
    rw [map_neg, map_neg, neg_sub_neg]
    exact hd j a c
  obtain ⟨g, hg, -⟩ := exists_lift_of_coboundary D b H V hV x hx hVc (fun a j ↦ -d j a) heq
  have hgm : D.map B g = μ[B.obj] := map_eq_of_left D B hg
  have hv : (baseReduction I).toOriginal ≫ (lift e e ≫ g).left = (baseReduction I).toOriginal ≫ e.left := by
    have hh : (baseReduction I).map B (lift e e ≫ g) = (baseReduction I).map B e := by
      rw [Reduction.map_comp (baseReduction I) D B, Reduction.map_lift, hgm, he]
      have hη : (toUnit (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I)))))) ≫ η[B.obj] = η[B.obj] := by
        rw [show toUnit (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I))))) = 𝟙 _ from Subsingleton.elim _ _,
          Category.id_comp]
      rw [← hη, MonObj.lift_comp_one_left, hη]
    simpa only [Reduction.map_left_toOriginal] using
      congrArg (fun f ↦ f.left ≫ B.toOriginal) hh
  obtain ⟨m, hm, hp⟩ := exists_lift_with_value D H b g (lift e e) e hv
  exact ⟨m, map_eq_of_left D B (hm.trans hg), hp⟩

end Lifting

end Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech
