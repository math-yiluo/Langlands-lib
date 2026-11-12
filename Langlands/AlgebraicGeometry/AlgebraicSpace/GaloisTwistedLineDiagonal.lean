import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineLocalLift
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfLocalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.GroupScheme.AffineQuotientReduction

/-!
# The diagonal of the Galois-twisted line

The diagonal of the Galois-twisted line is representable by affine immersions. Equalizer loci
of two points over a scheme `W` are immersions: on the fppf covering sieve where both points
lift to the line they are the loci `liftLocus`, and immersed equalizer loci glue
(`exists_representsEqualizer_of_fppf_local`). They are affine: after the finite surjective base
change `W_{K'} → W` the points lift Zariski-locally (`exists_local_lift`), where the locus is
again `liftLocus`, and affineness descends along finite surjective morphisms
(`Langlands.GroupScheme.AffineQuotient.isAffine_of_finite_surjective`). In particular the
space is quasi-separated, and it is locally of finite type over `Spec K`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace EqualizerLocus

variable {S : Scheme.{u}} {F : Presheaf S}

/-- The base change of an equalizer locus along `g` is the equalizer locus of the
restrictions along `g`. -/
theorem representsEqualizer_pullback {U Z U' : Over S} {ι : Z ⟶ U} {x y : F.obj (op U)}
    (hι : RepresentsEqualizer ι x y) (g : U' ⟶ U) :
    RepresentsEqualizer (F := F) (Limits.pullback.snd ι g) (F.map g.op x) (F.map g.op y) := by
  intro T h
  have key : F.map h.op (F.map g.op x) = F.map h.op (F.map g.op y) ↔
      F.map (h ≫ g).op x = F.map (h ≫ g).op y := by
    simp only [op_comp, Functor.map_comp_apply]
  rw [key, ← hι (h ≫ g)]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z ≫ Limits.pullback.fst ι g, by
      rw [Category.assoc, Limits.pullback.condition, Category.assoc]⟩
  · rintro ⟨z, hz⟩
    exact ⟨Limits.pullback.lift z h hz, Limits.pullback.lift_snd _ _ _⟩

/-- Two monomorphisms representing the same equalizer locus are isomorphic over the base, so
they share every property of scheme morphisms that is invariant under isomorphism. -/
theorem prop_of_representsEqualizer {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {U Z Z' : Over S} {ι : Z ⟶ U} {ι' : Z' ⟶ U} {x y : F.obj (op U)} [Mono ι] [Mono ι']
    (hι : RepresentsEqualizer ι x y) (hι' : RepresentsEqualizer ι' x y) (h : P ι'.left) :
    P ι.left := by
  obtain ⟨a, ha⟩ := (hι' ι).2 ((hι ι).1 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨b, hb⟩ := (hι ι').2 ((hι' ι').1 ⟨𝟙 _, Category.id_comp _⟩)
  have : IsIso a := ⟨⟨b, (cancel_mono ι).1 (by rw [Category.assoc, hb, ha, Category.id_comp]),
    (cancel_mono ι').1 (by rw [Category.assoc, ha, hb, Category.id_comp])⟩⟩
  have : IsIso a.left := inferInstanceAs (IsIso ((Over.forget S).map a))
  rw [← ha, Over.comp_left, P.cancel_left_of_respectsIso]
  exact h

end EqualizerLocus

namespace AffineHomDescent

/-- For two pullback squares over the same cospan, a property of morphisms invariant under
isomorphism transfers between their second projections. -/
theorem prop_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {A A' B C E : Scheme.{u}} {a : A ⟶ C} {b : A ⟶ B} {a' : A' ⟶ C} {b' : A' ⟶ B}
    {c : C ⟶ E} {d : B ⟶ E} (h : IsPullback a b c d) (h' : IsPullback a' b' c d)
    (hb : P b) : P b' := by
  rw [← h'.isoIsPullback_hom_snd _ _ h, P.cancel_left_of_respectsIso]
  exact hb

/-- Affineness of morphisms descends along finite surjective morphisms. -/
theorem isAffineHom_of_isPullback {Z T Z' T' : Scheme.{u}} {ι : Z ⟶ T} {p : T' ⟶ T}
    {ι' : Z' ⟶ T'} {p' : Z' ⟶ Z} (h : IsPullback p' ι' ι p) [_root_.AlgebraicGeometry.IsFinite p]
    [Surjective p] [IsAffineHom ι'] : IsAffineHom ι := by
  have : _root_.AlgebraicGeometry.IsFinite p' := MorphismProperty.of_isPullback h.flip ‹_›
  have : Surjective p' := MorphismProperty.of_isPullback h.flip ‹_›
  constructor
  intro U hU
  have hA : IsAffineOpen (p' ⁻¹ᵁ ι ⁻¹ᵁ U) := by
    have e : p' ⁻¹ᵁ ι ⁻¹ᵁ U = ι' ⁻¹ᵁ p ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    rw [e]
    exact (hU.preimage p).preimage ι'
  have : IsAffine (Over.mk (p' ∣_ (ι ⁻¹ᵁ U))).left := hA
  exact Langlands.GroupScheme.AffineQuotient.isAffine_of_finite_surjective
    (S := (ι ⁻¹ᵁ U : Scheme.{u})) (U := Over.mk (𝟙 _)) (V := Over.mk (p' ∣_ (ι ⁻¹ᵁ U)))
    (Over.homMk (p' ∣_ (ι ⁻¹ᵁ U)) (by simp))
    (show _root_.AlgebraicGeometry.IsFinite (p' ∣_ (ι ⁻¹ᵁ U)) from inferInstance)
    (show Surjective (p' ∣_ (ι ⁻¹ᵁ U)) from IsZariskiLocalAtTarget.restrict ‹_› _)

end AffineHomDescent

namespace GaloisTwistedLine

open RelationQuotient KernelPair EqualizerLocus AffineHomDescent

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

/-- **Equalizer loci are immersions.** On the fppf covering sieve where both points lift to
the line, the equalizer locus is `liftLocus`, an immersion; immersed loci glue. -/
theorem exists_isImmersion {W : Over (Spec (CommRingCat.of K))}
    (x y : (space D).presheaf.obj (op W)) :
    ∃ (Z : Over (Spec (CommRingCat.of K))) (ι : Z ⟶ W),
      RepresentsEqualizer (F := (space D).presheaf) ι x y ∧ IsImmersion ι.left := by
  have : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology _) (atlas D) :=
    inferInstanceAs (CategoryTheory.Presheaf.IsLocallySurjective _
      (quotientMap (tOver D) (sOver D)))
  refine exists_representsEqualizer_of_fppf_local (space D).toSheaf.property x y
    (CategoryTheory.Presheaf.imageSieve (atlas D) x ⊓
      CategoryTheory.Presheaf.imageSieve (atlas D) y)
    ((fppfTopology _).intersection_covering
      (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology _) (atlas D) x)
      (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology _) (atlas D) y)) ?_
  rintro V g ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩
  exact ⟨liftLocus D t₁.down t₂.down, liftLocusι D t₁.down t₂.down,
    isImmersion_liftLocusι D _ _, representsEqualizer_liftLocus D _ _ _ _ ht₁ ht₂⟩

section KStructure

variable {W : Over (Spec (CommRingCat.of K))} (q : W.left ⟶ Spec (CommRingCat.of K'))
  (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap K K')) = W.hom)

include hq in
/-- Zariski-local lifts of two points at once. -/
theorem exists_local_lift₂ (x y : (space D).presheaf.obj (op W)) (w : W.left) :
    ∃ (V : W.left.Opens), w ∈ V ∧
      ∃ τ₁ τ₂ : Over.mk (V.ι ≫ W.hom) ⟶ lineOver K K',
        (atlas D).app (op _) ⟨τ₁⟩ =
          (space D).presheaf.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ W.hom) ⟶ W).op x ∧
        (atlas D).app (op _) ⟨τ₂⟩ =
          (space D).presheaf.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ W.hom) ⟶ W).op y := by
  obtain ⟨V₁, hw₁, τx, hx⟩ := exists_local_lift D q hq x w
  obtain ⟨V₂, hw₂, τy, hy⟩ := exists_local_lift D q hq y w
  let i₁ : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ Over.mk (V₁.ι ≫ W.hom) :=
    Over.homMk (W.left.homOfLE inf_le_left) (by
      change _ ≫ V₁.ι ≫ W.hom = _
      rw [← Category.assoc, Scheme.homOfLE_ι]
      rfl)
  let i₂ : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ Over.mk (V₂.ι ≫ W.hom) :=
    Over.homMk (W.left.homOfLE inf_le_right) (by
      change _ ≫ V₂.ι ≫ W.hom = _
      rw [← Category.assoc, Scheme.homOfLE_ι]
      rfl)
  have e₁ : i₁ ≫ (Over.homMk V₁.ι rfl : Over.mk (V₁.ι ≫ W.hom) ⟶ W) = Over.homMk (V₁ ⊓ V₂).ι rfl := by
    ext1
    exact Scheme.homOfLE_ι _ inf_le_left
  have e₂ : i₂ ≫ (Over.homMk V₂.ι rfl : Over.mk (V₂.ι ≫ W.hom) ⟶ W) = Over.homMk (V₁ ⊓ V₂).ι rfl := by
    ext1
    exact Scheme.homOfLE_ι _ inf_le_right
  refine ⟨V₁ ⊓ V₂, ⟨hw₁, hw₂⟩, i₁ ≫ τx, i₂ ≫ τy, ?_, ?_⟩
  · rw [atlas_app_comp]
    refine (congrArg _ hx).trans ?_
    rw [← Functor.map_comp_apply, ← op_comp, e₁]
  · rw [atlas_app_comp]
    refine (congrArg _ hy).trans ?_
    rw [← Functor.map_comp_apply, ← op_comp, e₂]

end KStructure

/-- The structure map of `Spec K'` over `Spec K`. -/
abbrev extBase (K K' : Type u) [Field K] [Field K'] [Algebra K K'] :
    Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

variable (K') in
/-- The base change of a scheme over `Spec K` to `Spec K'`. -/
abbrev extOver (W : Over (Spec (CommRingCat.of K))) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Limits.pullback.fst W.hom (extBase K K') ≫ W.hom)

variable (K') in
/-- The projection of the base change to `Spec K'`. -/
abbrev extMap (W : Over (Spec (CommRingCat.of K))) : extOver K' W ⟶ W :=
  Over.homMk (Limits.pullback.fst W.hom (extBase K K')) rfl

theorem surjective_extBase : Surjective (extBase K K') :=
  ⟨fun _ => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

theorem isFinite_extBase [Module.Finite K K'] :
    _root_.AlgebraicGeometry.IsFinite (extBase K K') :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- **Equalizer loci are affine.** -/
theorem isAffineHom_of_representsEqualizer [Module.Finite K K']
    {W Z : Over (Spec (CommRingCat.of K))} {ι : Z ⟶ W} [Mono ι]
    {x y : (space D).presheaf.obj (op W)}
    (hι : RepresentsEqualizer (F := (space D).presheaf) ι x y) : IsAffineHom ι.left := by
  have : MorphismProperty.RespectsIso @IsAffineHom.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := surjective_extBase (K := K) (K' := K')
  have := isFinite_extBase (K := K) (K' := K')
  let p := extMap K' W
  let q : (extOver K' W).left ⟶ Spec (CommRingCat.of K') :=
    Limits.pullback.snd W.hom (extBase K K')
  have hq : q ≫ extBase K K' = (extOver K' W).hom := Limits.pullback.condition.symm
  have sq : IsPullback (Limits.pullback.fst ι p).left (Limits.pullback.snd ι p).left ι.left
      p.left := (IsPullback.of_hasPullback ι p).map (Over.forget _)
  have : _root_.AlgebraicGeometry.IsFinite p.left :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsFinite (Limits.pullback.fst W.hom (extBase K K')))
  have : Surjective p.left :=
    inferInstanceAs (Surjective (Limits.pullback.fst W.hom (extBase K K')))
  have : IsAffineHom (Limits.pullback.snd ι p).left := by
    have : IsZariskiLocalAtTarget @IsAffineHom.{u} := by
      set_option backward.isDefEq.respectTransparency false in infer_instance
    refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsAffineHom) fun w => ?_
    obtain ⟨V, hw, τ₁, τ₂, h₁, h₂⟩ :=
      exists_local_lift₂ D q hq ((space D).presheaf.map p.op x) ((space D).presheaf.map p.op y) w
    refine ⟨V, hw, ?_⟩
    let jV : Over.mk (V.ι ≫ (extOver K' W).hom) ⟶ W := Over.homMk V.ι rfl ≫ p
    have hrep := representsEqualizer_pullback hι jV
    have hrep' := representsEqualizer_liftLocus D τ₁ τ₂ ((space D).presheaf.map jV.op x)
      ((space D).presheaf.map jV.op y)
      (h₁.trans (by rw [← Functor.map_comp_apply, ← op_comp]))
      (h₂.trans (by rw [← Functor.map_comp_apply, ← op_comp]))
    have : Mono (liftLocusι D τ₁ τ₂) :=
      (Over.forget _).mono_of_mono_map (mono_liftLocusι D τ₁ τ₂)
    have haff : IsAffineHom (Limits.pullback.snd ι jV).left :=
      prop_of_representsEqualizer hrep hrep' (isAffineHom_liftLocusι D τ₁ τ₂)
    have sqV : IsPullback (Limits.pullback.fst ι jV).left (Limits.pullback.snd ι jV).left
        ι.left (V.ι ≫ p.left) := (IsPullback.of_hasPullback ι jV).map (Over.forget _)
    exact prop_of_isPullback sqV
      ((isPullback_morphismRestrict (Limits.pullback.snd ι p).left V).flip.paste_horiz sq) haff
  exact isAffineHom_of_isPullback sq

/-- **Equalizer loci are affine immersions.** -/
theorem exists_affineImmersion [Module.Finite K K'] {W : Over (Spec (CommRingCat.of K))}
    (x y : (space D).presheaf.obj (op W)) :
    ∃ (Z : Over (Spec (CommRingCat.of K))) (ι : Z ⟶ W), Mono ι.left ∧
      RepresentsEqualizer (F := (space D).presheaf) ι x y ∧
      (@IsImmersion ⊓ @IsAffineHom) ι.left := by
  obtain ⟨Z, ι, hrep, himm⟩ := exists_isImmersion D x y
  have : Mono ι.left := inferInstance
  have : Mono ι := (Over.forget _).mono_of_mono_map this
  exact ⟨Z, ι, inferInstance, hrep, himm, isAffineHom_of_representsEqualizer D hrep⟩

/-- **The diagonal of the Galois-twisted line is an affine immersion.** -/
theorem relative_diag [Module.Finite K K'] :
    (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} ⊓ @_root_.AlgebraicGeometry.IsAffineHom.{u})
        (Over.forget _)).relative (schemeYoneda _) (diag (space D).presheaf) := by
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso @IsAffineHom.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@IsImmersion.{u} ⊓ @IsAffineHom.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  exact relative_diag_of_representsEqualizer _ fun _ x y => exists_affineImmersion D x y

theorem isQuasiSeparated [Module.Finite K K'] : IsQuasiSeparated (space D) := by
  have : MorphismProperty.RespectsIso @QuasiCompact.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_of_representsEqualizer _ fun _ x y =>
    (exists_affineImmersion D x y).imp fun _ ⟨ι, hm, hr, _, ha⟩ =>
      ⟨ι, hm, hr, by have := ha; infer_instance⟩

theorem locallyOfFiniteType_lineBase [Module.Finite K K'] :
    LocallyOfFiniteType (lineBase (K := K) (K' := K')) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K K'[X]).FiniteType
  rw [RingHom.finiteType_algebraMap]
  exact Algebra.FiniteType.trans (S := K') inferInstance inferInstance

theorem locallyOfFiniteTypeOverBase [Module.Finite K K'] :
    LocallyOfFiniteTypeOverBase (space D) :=
  ⟨lineOver K K', atlas D, atlas_isEtale D, atlas_isSurjective D, locallyOfFiniteType_lineBase⟩

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
