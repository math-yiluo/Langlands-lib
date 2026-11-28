import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Extending a morphism from a dense open subscheme by local pieces

Let `X` be reduced, `Z` separated and `θ : D ⟶ Z` a morphism on a dense open `D` of `X`. If every
point of `X` has an open neighbourhood `O` with a morphism `O ⟶ Z` agreeing with `θ` on `O ∩ D`,
then `θ` extends to a morphism `X ⟶ Z`. Agreement on `O ∩ D` follows from agreement on any open
subset of `O ∩ D` dense in `O`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {X Z : Scheme.{u}}

/-- A morphism `φ` on an open `O` agrees with `θ` on the points of `O ∩ D` lying in `W`, in the
functorial sense. -/
def AgreesOn {D O : X.Opens} (θ : D.toScheme ⟶ Z) (φ : O.toScheme ⟶ Z) (W : Set X) : Prop :=
  ∀ (T : Scheme.{u}) (u : T ⟶ O.toScheme) (v : T ⟶ D.toScheme), u ≫ O.ι = v ≫ D.ι →
    Set.range (u ≫ O.ι) ⊆ W → u ≫ φ = v ≫ θ

theorem dominant_homOfLE {U V : X.Opens} (h : U ≤ V) (hd : (V : Set X) ⊆ closure (U : Set X)) :
    IsDominant (X.homOfLE h) := by
  constructor
  rw [DenseRange, dense_iff_inter_open]
  intro N hN ⟨v, hv⟩
  have hN' : IsOpen (V.ι '' N) := V.ι.isOpenEmbedding.isOpenMap _ hN
  have hvV : V.ι v ∈ (V : Set X) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨v, rfl⟩
  obtain ⟨_, ⟨n, hnN, rfl⟩, hnU⟩ := mem_closure_iff.mp (hd hvV) _ hN' ⟨v, hv, rfl⟩
  refine ⟨n, hnN, ⟨(show U.toScheme from ⟨V.ι n, hnU⟩), ?_⟩⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  rfl

/-- Agreement on a dense open part of `O ∩ D` implies agreement on all of `O ∩ D`. -/
theorem AgreesOn.of_dense [IsReduced X] [Z.IsSeparated] {D O W : X.Opens}
    {θ : D.toScheme ⟶ Z} {φ : O.toScheme ⟶ Z} (hW : W ≤ O ⊓ D)
    (hd : (O : Set X) ⊆ closure (W : Set X)) (h : AgreesOn θ φ W) :
    AgreesOn θ φ Set.univ := by
  have hWM : W ≤ O ⊓ D := hW
  have hkey : X.homOfLE (inf_le_left : O ⊓ D ≤ O) ≫ φ = X.homOfLE (inf_le_right : O ⊓ D ≤ D) ≫ θ := by
    have : IsDominant (X.homOfLE hWM) :=
      dominant_homOfLE hWM (fun x hx => hd hx.1)
    refine ext_of_isDominant (X.homOfLE hWM) ?_
    rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]
    apply h
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    · rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact t.2
  intro T u v huv _
  have hr : Set.range (u ≫ O.ι) ⊆ Set.range (O ⊓ D).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_apply]
      exact (u t).2
    · rw [huv, Scheme.Hom.comp_apply]
      exact (v t).2
  set w := IsOpenImmersion.lift (O ⊓ D).ι _ hr
  have hw : w ≫ (O ⊓ D).ι = u ≫ O.ι := IsOpenImmersion.lift_fac _ _ _
  have hwu : w ≫ X.homOfLE (inf_le_left : O ⊓ D ≤ O) = u := by
    rw [← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, hw]
  have hwv : w ≫ X.homOfLE (inf_le_right : O ⊓ D ≤ D) = v := by
    rw [← cancel_mono D.ι, Category.assoc, Scheme.homOfLE_ι, hw, huv]
  rw [← hwu, ← hwv, Category.assoc, Category.assoc, hkey]

/-- **Extension from local pieces.** -/
theorem exists_extension [IsReduced X] [Z.IsSeparated] (D : X.Opens)
    (hD : Dense (D : Set X)) (θ : D.toScheme ⟶ Z)
    (pieces : ∀ x : X, ∃ (O : X.Opens) (φ : O.toScheme ⟶ Z), x ∈ O ∧ AgreesOn θ φ Set.univ) :
    ∃ Φ : X ⟶ Z, D.ι ≫ Φ = θ := by
  choose O φ hxO hag using pieces
  have hcov : IsOpenCover O := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩
  let 𝒰 := X.openCoverOfIsOpenCover O hcov
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ φ x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ φ y := by
    intro (x : X) (y : X)
    change pullback.fst (O x).ι (O y).ι ≫ φ x = pullback.snd (O x).ι (O y).ι ≫ φ y
    set j := pullback.fst (O x).ι (O y).ι ≫ (O x).ι
    have : IsReduced (pullback (O x).ι (O y).ι) := isReduced_of_isOpenImmersion j
    set Q := j ⁻¹ᵁ D
    have hQ : IsDominant Q.ι := by
      constructor
      rw [DenseRange, Scheme.Opens.range_ι]
      exact hD.preimage j.isOpenEmbedding.isOpenMap
    have hr : Set.range (Q.ι ≫ j) ⊆ Set.range D.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      exact t.2
    set v := IsOpenImmersion.lift D.ι _ hr
    have hv : v ≫ D.ι = Q.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
    have e1 : (Q.ι ≫ pullback.fst (O x).ι (O y).ι) ≫ (O x).ι = v ≫ D.ι := by
      rw [hv, Category.assoc]
    have e2 : (Q.ι ≫ pullback.snd (O x).ι (O y).ι) ≫ (O y).ι = v ≫ D.ι := by
      rw [hv]
      simp only [j, Category.assoc, pullback.condition]
    refine ext_of_isDominant Q.ι ?_
    rw [← Category.assoc, hag x _ _ v e1 (Set.subset_univ _),
      ← Category.assoc, hag y _ _ v e2 (Set.subset_univ _)]
  refine ⟨𝒰.glueMorphisms φ hf, ?_⟩
  apply Scheme.hom_ext_of_forall
  intro d
  set U := D.ι ⁻¹ᵁ O d.1
  refine ⟨U, hxO d.1 |> fun h => (show d ∈ U from h), ?_⟩
  have hr : Set.range (U.ι ≫ D.ι) ⊆ Set.range (O d.1).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact t.2
  set w := IsOpenImmersion.lift (O d.1).ι _ hr
  have hw : w ≫ (O d.1).ι = U.ι ≫ D.ι := IsOpenImmersion.lift_fac _ _ _
  rw [← Category.assoc, ← hw, Category.assoc]
  have h1 : (O d.1).ι ≫ 𝒰.glueMorphisms φ hf = φ d.1 :=
    Scheme.Cover.ι_glueMorphisms 𝒰 φ hf d.1
  rw [h1]
  exact hag d.1 _ w U.ι hw (Set.subset_univ _)

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
