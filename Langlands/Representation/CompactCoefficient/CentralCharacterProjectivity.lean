import Langlands.Representation.CompactCoefficient.RestrictedSplitting
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Projectivity and injectivity with a fixed central character

Let `χ` be a character of the centre of a locally profinite group `G`, and let
`M(G)_χ` be the full subcategory of smooth complex representations on which the
centre acts through `χ`. This subcategory is closed under subobjects and
quotients, so its epimorphisms and monomorphisms are the surjective and
injective intertwiners, and pushouts of its objects in the category of smooth
representations stay in it.

Let `H` be an open normal subgroup with `H ⊔ center G` of finite index, and let
`τ` be an irreducible object of `M(G)_χ` whose restriction to `H` has compactly
supported smooth-dual coefficients. Then `τ` is projective and injective in
`M(G)_χ`: `H`-equivariant lifts and retractions exist by
`RestrictedSplitting`, they commute with the centre because both sides have
central character `χ`, and averaging over the finite quotient
`G ⧸ (H ⊔ center G)` makes them `G`-equivariant without changing the composites.
This is the argument of Renard VI.3.6.
-/

noncomputable section

namespace Langlands.CentralCharacterProjectivity

open CategoryTheory CategoryTheory.Limits FiniteQuotientAveraging RestrictedSplitting
open scoped ZeroObject

universe uG uV

section Category

variable {G : Type uG} [Group G] [TopologicalSpace G] (χ : Subgroup.center G →* ℂˣ)

/-- Morphisms of smooth representations with the same underlying map are equal. -/
theorem hom_ext' {A B : SmoothRep.{0, uG, uV} ℂ G} {f g : A ⟶ B}
    (h : ∀ v, SmoothRep.hom f v = SmoothRep.hom g v) : f = g := by
  have hfg : SmoothRep.hom f = SmoothRep.hom g :=
    Representation.IntertwiningMap.ext (LinearMap.ext h)
  calc f = SmoothRep.ofHom (SmoothRep.hom f) := rfl
    _ = SmoothRep.ofHom (SmoothRep.hom g) := by rw [hfg]
    _ = g := rfl

/-- Smooth representations on which the centre acts through `χ`. -/
abbrev centralCharacterProperty : ObjectProperty (SmoothRep.{0, uG, uV} ℂ G) :=
  fun A => A.HasCentralCharacter χ

instance : (centralCharacterProperty.{uG, uV} χ).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, fun z v => ?_⟩
    have hv : ∀ w : (0 : SmoothRep.{0, uG, uV} ℂ G), w = 0 := fun w =>
      congrArg (fun f => SmoothRep.hom f w) ((isZero_zero _).eq_of_src (𝟙 _) 0)
    rw [hv v, map_zero, smul_zero]

instance : (centralCharacterProperty.{uG, uV} χ).IsClosedUnderSubobjects where
  prop_of_mono f hf hY := fun z v => by
    apply (SmoothRep.mono_iff_injective f).1 hf
    rw [(SmoothRep.hom f).isIntertwining _ _ (z : G) v, map_smul]
    exact hY z _

instance : (centralCharacterProperty.{uG, uV} χ).IsClosedUnderQuotients where
  prop_of_epi f hf hX := fun z w => by
    obtain ⟨v, rfl⟩ := (SmoothRep.epi_iff_surjective f).1 hf w
    rw [← (SmoothRep.hom f).isIntertwining _ _ (z : G) v, hX z v, map_smul]

instance : (centralCharacterProperty.{uG, uV} χ).ι.PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

instance : (centralCharacterProperty.{uG, uV} χ).ι.PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- Epimorphisms with central character `χ` are surjective. -/
theorem surjective_of_epi {A B : (centralCharacterProperty.{uG, uV} χ).FullSubcategory}
    (f : A ⟶ B) [Epi f] : Function.Surjective (SmoothRep.hom f.hom) :=
  (SmoothRep.epi_iff_surjective ((centralCharacterProperty χ).ι.map f)).1 inferInstance

/-- Monomorphisms with central character `χ` are injective. -/
theorem injective_of_mono {A B : (centralCharacterProperty.{uG, uV} χ).FullSubcategory}
    (f : A ⟶ B) [Mono f] : Function.Injective (SmoothRep.hom f.hom) :=
  (SmoothRep.mono_iff_injective ((centralCharacterProperty χ).ι.map f)).1 inferInstance

/-- The central defect `A z - χ z`, an endomorphism because `z` is central. -/
def centralDefect (A : SmoothRep.{0, uG, uV} ℂ G) (z : Subgroup.center G) : A ⟶ A :=
  SmoothRep.ofHom
    ((A.representation z - (χ z : ℂ) • LinearMap.id).intertwiningMap_of_isIntertwiningMap
      A.representation A.representation fun g v => by
        have hzg : (z : G) * g = g * z := ((Subgroup.mem_center_iff.mp z.2) g).symm
        have h : A.representation z (A.representation g v) =
            A.representation g (A.representation z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hzg, map_mul, Module.End.mul_apply]
        change A.representation z (A.representation g v) - (χ z : ℂ) • A.representation g v =
          A.representation g (A.representation z v - (χ z : ℂ) • v)
        rw [map_sub, map_smul, h])

theorem centralDefect_apply (A : SmoothRep.{0, uG, uV} ℂ G) (z : Subgroup.center G) (v : A) :
    SmoothRep.hom (centralDefect χ A z) v = A.representation z v - (χ z : ℂ) • v := rfl

/-- The central defect is natural. -/
theorem comp_centralDefect {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (z : Subgroup.center G) : f ≫ centralDefect χ B z = centralDefect χ A z ≫ f := by
  apply hom_ext'
  intro v
  change B.representation z (SmoothRep.hom f v) - (χ z : ℂ) • SmoothRep.hom f v =
    SmoothRep.hom f (A.representation z v - (χ z : ℂ) • v)
  rw [map_sub, map_smul, (SmoothRep.hom f).isIntertwining _ _ (z : G) v]

theorem centralDefect_eq_zero {A : SmoothRep.{0, uG, uV} ℂ G} (hA : A.HasCentralCharacter χ)
    (z : Subgroup.center G) : centralDefect χ A z = 0 := by
  apply hom_ext'
  intro v
  rw [centralDefect_apply, hA z v, sub_self]
  rfl

theorem hasCentralCharacter_of_centralDefect {A : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ z, centralDefect χ A z = 0) : A.HasCentralCharacter χ := by
  intro z v
  have hv : SmoothRep.hom (centralDefect χ A z) v = 0 := by
    rw [h z]
    rfl
  rw [centralDefect_apply] at hv
  exact sub_eq_zero.mp hv

/-- A pushout of smooth representations with central character `χ` has central
character `χ`. -/
theorem hasCentralCharacter_pushout {X Y Z : SmoothRep.{0, uG, uV} ℂ G} (f : X ⟶ Y)
    (g : X ⟶ Z) (hY : Y.HasCentralCharacter χ) (hZ : Z.HasCentralCharacter χ) :
    (pushout f g).HasCentralCharacter χ := by
  refine hasCentralCharacter_of_centralDefect χ fun z => ?_
  apply pushout.hom_ext
  · rw [comp_centralDefect, centralDefect_eq_zero χ hY, zero_comp, comp_zero]
  · rw [comp_centralDefect, centralDefect_eq_zero χ hZ, zero_comp, comp_zero]

end Category

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Renard VI.3.6, generic form: an irreducible smooth representation with
central character `χ`, whose restriction to an open normal subgroup `H` with
`H ⊔ center G` of finite index has compactly supported smooth-dual coefficients,
is projective and injective among smooth representations with central
character `χ`. -/
theorem projective_and_injective_of_compactRestriction
    (H : OpenSubgroup G) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    (χ : Subgroup.center G →* ℂˣ) (τ : SmoothRep.{0, uG, uV} ℂ G)
    (hχ : τ.HasCentralCharacter χ) (hirr : τ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients
      (SmoothRep.restrictSubgroup H.toSubgroup τ).representation) :
    Projective (C := (centralCharacterProperty.{uG, uV} χ).FullSubcategory) ⟨τ, hχ⟩ ∧
      Injective (C := (centralCharacterProperty.{uG, uV} χ).FullSubcategory) ⟨τ, hχ⟩ := by
  classical
  let N := H.toSubgroup ⊔ Subgroup.center G
  let : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hscalar : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v : τ, τ.representation z v = c • v :=
    fun z => ⟨χ z, hχ z⟩
  refine ⟨⟨fun {E X} f e _ => ?_⟩, ⟨fun {X Y} g f _ => ?_⟩⟩
  · obtain ⟨l₀, hl₀, hl₀e⟩ := exists_restricted_lift H τ hirr hscalar hc E.obj.isSmooth
      X.obj.isSmooth (SmoothRep.hom e.hom) (surjective_of_epi χ e) (SmoothRep.hom f.hom)
    have hl := isEquivariantOn_sup_center χ hχ E.property hl₀
    refine ⟨ObjectProperty.homMk (SmoothRep.ofHom (averageMap (N := N) hl)), ?_⟩
    apply ObjectProperty.hom_ext
    apply hom_ext'
    intro v
    change SmoothRep.hom e.hom (average τ.representation E.obj.representation N l₀ v) =
      SmoothRep.hom f.hom v
    have hcomp : (SmoothRep.hom e.hom).toLinearMap ∘ₗ l₀ = (SmoothRep.hom f.hom).toLinearMap :=
      LinearMap.ext hl₀e
    rw [← average_comp_left (SmoothRep.hom e.hom) l₀ v, hcomp, average_intertwiningMap]
    rfl
  · have hmono : Mono f.hom := (SmoothRep.mono_iff_injective f.hom).2 (injective_of_mono χ f)
    have hP : (pushout f.hom g.hom).HasCentralCharacter χ :=
      hasCentralCharacter_pushout χ f.hom g.hom Y.property hχ
    have hjinj : Function.Injective (SmoothRep.hom (pushout.inr f.hom g.hom)) :=
      (SmoothRep.mono_iff_injective _).1 inferInstance
    obtain ⟨r₀, hr₀, hr₀j⟩ := exists_restricted_retraction H τ hirr hscalar hc
      (pushout f.hom g.hom).isSmooth (SmoothRep.hom (pushout.inr f.hom g.hom)) hjinj
    have hr := isEquivariantOn_sup_center χ hP hχ hr₀
    let r : pushout f.hom g.hom ⟶ τ := SmoothRep.ofHom (averageMap (N := N) hr)
    have hjr : pushout.inr f.hom g.hom ≫ r = 𝟙 τ := by
      apply hom_ext'
      intro v
      change average (pushout f.hom g.hom).representation τ.representation N r₀
        (SmoothRep.hom (pushout.inr f.hom g.hom) v) = v
      have hcomp : r₀ ∘ₗ (SmoothRep.hom (pushout.inr f.hom g.hom)).toLinearMap =
          (Representation.IntertwiningMap.id τ.representation).toLinearMap :=
        LinearMap.ext hr₀j
      rw [← average_comp_right r₀ (SmoothRep.hom (pushout.inr f.hom g.hom)) v, hcomp,
        average_intertwiningMap]
      rfl
    refine ⟨ObjectProperty.homMk (pushout.inl f.hom g.hom ≫ r), ?_⟩
    apply ObjectProperty.hom_ext
    change f.hom ≫ pushout.inl f.hom g.hom ≫ r = g.hom
    rw [← Category.assoc, pushout.condition, Category.assoc, hjr, Category.comp_id]

end Main

end Langlands.CentralCharacterProjectivity
