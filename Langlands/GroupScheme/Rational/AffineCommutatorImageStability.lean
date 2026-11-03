import Langlands.GroupScheme.Rational.AffineCommutatorImage
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Stability of the actual commutator scheme image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

private theorem spec_schematic_of_injective {A B : CommRingCat.{u}}
    (f : A ⟶ B) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map f) := by
  have : Mono f := ConcreteCategory.mono_of_injective f hf
  have : Mono (Spec.map f).appTop :=
    mono_of_mono_fac (Scheme.ΓSpecIso_naturality f)
  have hinj : Function.Injective (Spec.map f).appTop :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp inferInstance
  constructor
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  ext U : 2
  simp

private theorem closed_lift_of_schematic_precomp
    {X Y Z W : Scheme.{u}} (i : X ⟶ W) [IsClosedImmersion i]
    (p : Z ⟶ Y) [IsSchemeTheoreticallyDominant p]
    (g : Y ⟶ W) (h : Z ⟶ X) (he : p ≫ g = h ≫ i) :
    ∃ a : Y ⟶ X, a ≫ i = g := by
  have hker : i.ker ≤ g.ker := by
    have hh := h.le_ker_comp i
    rw [← he, Scheme.Hom.ker_comp, p.ker_eq_bot, Scheme.IdealSheafData.map_bot] at hh
    exact hh
  exact ⟨IsClosedImmersion.lift i g hker, IsClosedImmersion.lift_fac i g hker⟩

private theorem whiskerLeft_pullback {B : Scheme.{u}} (X : Over B)
    {V W : Over B} (p : V ⟶ W) :
    IsPullback (snd X V) (X ◁ p) p (snd X W) := by
  have he : snd X V ≫ p = (X ◁ p) ≫ snd X W := by simp
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ he) ?_
  refine PullbackCone.IsLimit.mk he
    (fun s => lift (s.snd ≫ fst X W) s.fst) (fun s => by simp) ?_ ?_
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using s.condition
  · intro s m hm₁ hm₂
    apply CartesianMonoidalCategory.hom_ext
    · have hh := congrArg (fun f => f ≫ fst X W) hm₂
      simpa using hh
    · simpa using hm₁

private theorem whiskerLeft_schematic {B : Scheme.{u}} (X : Over B)
    [Flat X.hom] {V W : Over B} (p : V ⟶ W)
    [QuasiCompact p.left] [IsSchemeTheoreticallyDominant p.left] :
    IsSchemeTheoreticallyDominant (X ◁ p).left := by
  have : Flat (snd X W).left := by
    change Flat (pullback.snd X.hom W.hom)
    infer_instance
  have hpb : IsPullback (snd X V).left (X ◁ p).left p.left (snd X W).left :=
    (whiskerLeft_pullback X p).map (Over.forget B)
  exact IsSchemeTheoreticallyDominant.of_isPullback hpb

variable {R : CommRingCat.{u}} {G H K : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- The rational point of the commutator image induced by both input identities. -/
def imageOrigin (i : H ⟶ G) (j : K ⟶ G) :
    𝟙_ (Over (Spec R)) ⟶ imageScheme i j :=
  lift (1 : 𝟙_ (Over (Spec R)) ⟶ H.X) (1 : 𝟙_ (Over (Spec R)) ⟶ K.X) ≫
    imageFactor i j

/-- The image origin maps to the actual identity of the ambient group. -/
theorem imageOrigin_comp (i : H ⟶ G) (j : K ⟶ G) :
    imageOrigin i j ≫ imageInclusion i j = η[G.X] := by
  rw [imageOrigin, imageFactor_apply]
  simp [Hom.one_def]

/-- The independent tensor-coordinate test is schematically dominant onto its image. -/
theorem imageProjection_schematic (i : H ⟶ G) (j : K ⟶ G) :
    IsSchemeTheoreticallyDominant (imageProjection i j).left :=
  spec_schematic_of_injective
    (CommRingCat.ofHom (Subalgebra.val (imageAlgebra i j)).toRingHom)
    (imageAlgebra_injective i j)

/-- The actual product-to-image factor is schematically dominant. -/
theorem imageFactor_schematic (i : H ⟶ G) (j : K ⟶ G) :
    IsSchemeTheoreticallyDominant (imageFactor i j).left := by
  let : IsIso (tensorPresentation (H := H) (K := K)).inv.left :=
    (Over.forget (Spec R)).map_isIso (tensorPresentation (H := H) (K := K)).inv
  let : IsSchemeTheoreticallyDominant (imageProjection i j).left :=
    imageProjection_schematic i j
  change IsSchemeTheoreticallyDominant
    ((tensorPresentation (H := H) (K := K)).inv.left ≫ (imageProjection i j).left)
  infer_instance

/-- The product-to-image morphism is quasi-compact over the arbitrary base ring. -/
theorem imageFactor_quasiCompact (i : H ⟶ G) (j : K ⟶ G) :
    QuasiCompact (imageFactor i j).left := by
  let : QuasiCompact (imageProjection i j).left := by
    change QuasiCompact (Spec.map
      (CommRingCat.ofHom (Subalgebra.val (imageAlgebra i j)).toRingHom))
    infer_instance
  let : IsIso (tensorPresentation (H := H) (K := K)).inv.left :=
    (Over.forget (Spec R)).map_isIso (tensorPresentation (H := H) (K := K)).inv
  change QuasiCompact
    ((tensorPresentation (H := H) (K := K)).inv.left ≫ (imageProjection i j).left)
  infer_instance

/-- Under compatible actual actions, the commutator scheme image is stable on
every test. Flatness of the acting scheme suffices. -/
theorem imageInclusion_isStable {S : GroupScheme (Spec R)} [Flat S.X.hom]
    (b : AutomorphicAction S G) (c : AutomorphicAction S H)
    (d : AutomorphicAction S K) (i : H ⟶ G) (j : K ⟶ G)
    (hi : ∀ {T : Over (Spec R)} (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (hj : ∀ {T : Over (Spec R)} (s : T ⟶ S.X) (h : T ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) :
    ∀ (T : Over (Spec R)) (s : T ⟶ S.X) (v : T ⟶ imageScheme i j),
      ∃ w : T ⟶ imageScheme i j,
        w ≫ imageInclusion i j = b.act s (v ≫ imageInclusion i j) := by
  let : IsClosedImmersion (imageInclusion i j).left := imageInclusion_closed i j
  let : IsSchemeTheoreticallyDominant (imageFactor i j).left := imageFactor_schematic i j
  let : QuasiCompact (imageFactor i j).left := imageFactor_quasiCompact i j
  let p := S.X ◁ imageFactor i j
  let : IsSchemeTheoreticallyDominant p.left := whiskerLeft_schematic S.X (imageFactor i j)
  let g := b.act (fst S.X (imageScheme i j))
    (snd S.X (imageScheme i j) ≫ imageInclusion i j)
  let h := lift
    (c.act (fst S.X (H.X ⊗ K.X)) (snd S.X (H.X ⊗ K.X) ≫ fst H.X K.X))
    (d.act (fst S.X (H.X ⊗ K.X)) (snd S.X (H.X ⊗ K.X) ≫ snd H.X K.X)) ≫
      imageFactor i j
  have he : p ≫ g = h ≫ imageInclusion i j := by
    dsimp only [p, g, h]
    simp only [b.naturality, whiskerLeft_fst, whiskerLeft_snd_assoc, Category.assoc,
      imageFactor_comp]
    have hh := commutatorHom_equivariant b c d i j hi hj
      (fst S.X (H.X ⊗ K.X))
      (snd S.X (H.X ⊗ K.X) ≫ fst H.X K.X)
      (snd S.X (H.X ⊗ K.X) ≫ snd H.X K.X)
    simpa only [← comp_lift, lift_fst_snd, Category.comp_id] using hh.symm
  obtain ⟨a, ha⟩ := closed_lift_of_schematic_precomp (imageInclusion i j).left
    p.left g.left h.left (congrArg Over.Hom.left he)
  let aOver : S.X ⊗ imageScheme i j ⟶ imageScheme i j :=
    Over.homMk a (by
      rw [← (imageInclusion i j).w, ← Category.assoc, ha]
      exact g.w)
  have haOver : aOver ≫ imageInclusion i j = g := by
    apply Over.OverMorphism.ext
    exact ha
  intro T s v
  refine ⟨lift s v ≫ aOver, ?_⟩
  rw [Category.assoc, haOver]
  dsimp only [g]
  rw [b.naturality, lift_fst, lift_snd_assoc]

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
