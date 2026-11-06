import Langlands.GroupScheme.KernelPair
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # A group homomorphism monomorphic on an open cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OpenCell

/-- Two opens which meet every geometrically irreducible fiber have an
intersection which also meets every fiber. -/
theorem surjective_intersection {X Y : Scheme.{u}} (q : X ⟶ Y)
    [GeometricallyIrreducible q] [UniversallyOpen q]
    (V W : X.Opens) [Surjective (V.ι ≫ q)] [Surjective (W.ι ≫ q)] :
    Surjective ((V ⊓ W).ι ≫ q) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨v, hv⟩ := (V.ι ≫ q).surjective y
  obtain ⟨w, hw⟩ := (W.ι ≫ q).surjective y
  obtain ⟨x, hx, hxV, hxW⟩ :=
    (q.isIrreducible_preimage q.isOpenMap (isIrreducible_singleton (x := y))).2
      V W V.isOpen W.isOpen ⟨v.val, hv, v.property⟩ ⟨w.val, hw, w.property⟩
  exact ⟨⟨x, hxV, hxW⟩, hx⟩

variable {S : Scheme.{u}} {D G : GroupScheme S} {C : Over S}

/-- Factor a morphism through an open immersion containing its image. -/
def lift (j : C ⟶ D.X) [IsOpenImmersion j.left] {T : Over S}
    (a : T ⟶ D.X) (ha : Set.range a.left ⊆ Set.range j.left) : T ⟶ C :=
  Over.homMk (IsOpenImmersion.lift j.left a.left ha) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w a)

@[reassoc (attr := simp)]
theorem lift_comp (j : C ⟶ D.X) [IsOpenImmersion j.left] {T : Over S}
    (a : T ⟶ D.X) (ha : Set.range a.left ⊆ Set.range j.left) :
    lift j a ha ≫ j = a :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left a.left ha)

/-- Injectivity on an open cell compares any two test points whose images
lie in that cell. -/
theorem eq_of_comp_eq (p : D ⟶ G) (j : C ⟶ D.X)
    [IsOpenImmersion j.left] [Mono (j ≫ p.hom.hom)] {T : Over S}
    (a b : T ⟶ D.X)
    (ha : Set.range a.left ⊆ Set.range j.left)
    (hb : Set.range b.left ⊆ Set.range j.left)
    (h : a ≫ p.hom.hom = b ≫ p.hom.hom) : a = b := by
  have he : lift j a ha = lift j b hb := by
    apply (cancel_mono (j ≫ p.hom.hom)).mp
    simpa only [← Category.assoc, lift_comp] using h
  simpa only [lift_comp] using congrArg (fun f => f ≫ j) he

/-- If a homomorphism is monomorphic on an identity-containing open cell
of a smooth geometrically irreducible group, its full scheme kernel is trivial. -/
theorem kernelι_eq_zero [Smooth D.X.hom] [GeometricallyIrreducible D.X.hom]
    (p : D ⟶ G) (j : C ⟶ D.X) [IsOpenImmersion j.left]
    [Mono (j ≫ p.hom.hom)]
    (c : 𝟙_ (Over S) ⟶ C) (hc : c ≫ j = 1) : kernelι p = 0 := by
  let K := kernel p
  let X := D.X ⊗ K.X
  let f : X ⟶ D.X := fst D.X K.X
  let a : X ⟶ D.X := KernelPair.action p
  let q : X ⟶ K.X := snd D.X K.X
  let O : D.X.left.Opens := j.left.opensRange
  let V : X.left.Opens := f.left ⁻¹ᵁ O
  let W : X.left.Opens := a.left ⁻¹ᵁ O
  let e : K.X ⟶ X := CategoryTheory.CartesianMonoidalCategory.lift (toUnit K.X ≫ c ≫ j) (𝟙 K.X)
  let ei : K.X ⟶ X := CategoryTheory.CartesianMonoidalCategory.lift ((kernelι p).hom.hom)⁻¹ (𝟙 K.X)
  have heq : e ≫ q = 𝟙 K.X := lift_snd _ _
  have hef : e ≫ f = toUnit K.X ≫ c ≫ j := lift_fst _ _
  have heif : ei ≫ f = ((kernelι p).hom.hom)⁻¹ := lift_fst _ _
  have heiq : ei ≫ q = 𝟙 K.X := lift_snd _ _
  have heV : Set.range e.left ⊆ V := by
    rintro _ ⟨x, rfl⟩
    change f.left (e.left x) ∈ Set.range j.left
    exact ⟨(toUnit K.X ≫ c).left x, congrArg (fun h => h.left x) hef.symm⟩
  have heiW : Set.range ei.left ⊆ W := by
    have hi : ei ≫ a = toUnit K.X ≫ c ≫ j := by
      change ei ≫ (f * (q ≫ (kernelι p).hom.hom)) = _
      rw [MonObj.comp_mul, heif, ← Category.assoc, heiq, Category.id_comp,
        inv_mul_cancel, hc, MonObj.comp_one]
    rintro _ ⟨x, rfl⟩
    change a.left (ei.left x) ∈ Set.range j.left
    exact ⟨(toUnit K.X ≫ c).left x, congrArg (fun h => h.left x) hi.symm⟩
  have hsurjV : Surjective (V.ι ≫ q.left) := by
    refine ⟨fun x => ?_⟩
    exact ⟨⟨e.left x, heV ⟨x, rfl⟩⟩, congrArg (fun h => h.left x) heq⟩
  have hsurjW : Surjective (W.ι ≫ q.left) := by
    refine ⟨fun x => ?_⟩
    exact ⟨⟨ei.left x, heiW ⟨x, rfl⟩⟩,
      congrArg (fun h => h.left x) heiq⟩
  have : Smooth q.left := inferInstanceAs (Smooth (pullback.snd D.X.hom K.X.hom))
  have : GeometricallyIrreducible q.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd D.X.hom K.X.hom))
  have : Surjective ((V ⊓ W).ι ≫ q.left) := surjective_intersection q.left V W
  let T : Over S := Over.mk ((V ⊓ W).ι ≫ X.hom)
  let t : T ⟶ X := Over.homMk (V ⊓ W).ι
  have : Smooth (t ≫ q).left := inferInstanceAs (Smooth ((V ⊓ W).ι ≫ q.left))
  have : Surjective (t ≫ q).left :=
    inferInstanceAs (Surjective ((V ⊓ W).ι ≫ q.left))
  have : Epi (t ≫ q) := Over.epi_of_epi_left _
  have hfa : t ≫ f = t ≫ a := eq_of_comp_eq p j (t ≫ f) (t ≫ a)
    (by rintro _ ⟨x, rfl⟩; exact x.property.1)
    (by rintro _ ⟨x, rfl⟩; exact x.property.2)
    (by
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun h => t ≫ h) (KernelPair.action_comp p).symm)
  have hk : (t ≫ q) ≫ (kernelι p).hom.hom = (t ≫ q) ≫ 1 := by
    have hmul : (t ≫ f) * ((t ≫ q) ≫ (kernelι p).hom.hom) = (t ≫ f) * 1 := by
      simpa only [a, KernelPair.action, MonObj.comp_mul, Category.assoc, mul_one] using hfa.symm
    simpa only [MonObj.comp_one] using mul_left_cancel hmul
  apply Grp.hom_ext
  exact (cancel_epi (t ≫ q)).mp hk

/-- A homomorphism monomorphic on such a cell is monomorphic as a scheme map. -/
theorem mono [Smooth D.X.hom] [GeometricallyIrreducible D.X.hom]
    (p : D ⟶ G) (j : C ⟶ D.X) [IsOpenImmersion j.left]
    [Mono (j ≫ p.hom.hom)]
    (c : 𝟙_ (Over S) ⟶ C) (hc : c ≫ j = 1) : Mono p.hom.hom.left := by
  have hk : kernelι p ≫ 𝟙 D = 0 := by rw [kernelι_eq_zero p j c hc, Category.comp_id]
  refine ⟨fun h h' he => ?_⟩
  simpa only [Grp.id_hom_hom, Over.id_left, Category.comp_id] using
    FpqcHomDescent.scheme_comp_eq_of_quotient_eq p (𝟙 D) hk h h' he

/-- A faithfully flat quasi-compact homomorphism which is monomorphic on an
identity-containing open cell is an actual group-scheme isomorphism. -/
def iso [Smooth D.X.hom] [GeometricallyIrreducible D.X.hom]
    (p : D ⟶ G) [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left]
    (j : C ⟶ D.X) [IsOpenImmersion j.left] [Mono (j ≫ p.hom.hom)]
    (c : 𝟙_ (Over S) ⟶ C) (hc : c ≫ j = 1) : D ≅ G := by
  have : Mono p.hom.hom.left := mono p j c hc
  have : IsIso p.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget _).map p.hom.hom) := ‹IsIso p.hom.hom.left›
  have : IsIso p.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map p.hom) := ‹IsIso p.hom.hom›
  have : IsIso p.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map p) := ‹IsIso p.hom›
  have : IsIso p := isIso_of_reflects_iso p (Grp.forget₂Mon _)
  exact asIso p

@[simp]
theorem iso_hom [Smooth D.X.hom] [GeometricallyIrreducible D.X.hom]
    (p : D ⟶ G) [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left]
    (j : C ⟶ D.X) [IsOpenImmersion j.left] [Mono (j ≫ p.hom.hom)]
    (c : 𝟙_ (Over S) ⟶ C) (hc : c ≫ j = 1) :
    (iso p j c hc).hom = p := rfl

end Langlands.GroupScheme.OpenCell
