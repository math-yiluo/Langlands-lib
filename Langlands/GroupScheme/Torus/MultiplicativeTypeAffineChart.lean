import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # An affine fppf chart of a group of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- A flat morphism locally of finite presentation `f : U ⟶ S` has, around the image of any
point `u` of `U`, an affine open `Spec R ⟶ S` together with a faithfully flat ring map
`R ⟶ R'` of finite presentation whose spectrum factors through `f`. -/
theorem exists_affine_fppf_chart {U S : Scheme.{u}} (f : U ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (u : U) :
    ∃ (R R' : CommRingCat.{u}) (ι : Spec R ⟶ S) (φ : R ⟶ R') (g : Spec R' ⟶ U),
      IsOpenImmersion ι ∧ f u ∈ Set.range ι ∧ φ.hom.FaithfullyFlat ∧
        φ.hom.FinitePresentation ∧ Spec.map φ ≫ ι = g ≫ f := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f u)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWV⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show u ∈ f ⁻¹ᵁ V from hsV) (f ⁻¹ᵁ V).2
  have eWV : W ≤ f ⁻¹ᵁ V := hWV
  let O : S.Opens := ⟨f '' (W : Set U), f.isOpenMap _ W.2⟩
  obtain ⟨r, hrO, hr⟩ := hV.exists_basicOpen_le (V := O) ⟨f u, u, huW, rfl⟩ hsV
  let D : S.Opens := S.basicOpen r
  have hD : IsAffineOpen D := hV.basicOpen r
  let W' : U.Opens := U.basicOpen (f.appLE V W eWV r)
  have hW' : IsAffineOpen W' := hW.basicOpen _
  have hW'eq : W' = W ⊓ f ⁻¹ᵁ D := Scheme.basicOpen_appLE f W V eWV r
  have eW'D : W' ≤ f ⁻¹ᵁ D := by rw [hW'eq]; exact inf_le_right
  let φ := f.appLE D W' eW'D
  have hfac : Spec.map φ ≫ hD.fromSpec = hW'.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hD hW' eW'D
  have hflat : φ.hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) f inferInstance ⟨D, hD⟩ ⟨W', hW'⟩ eW'D
  have hfp : φ.hom.FinitePresentation :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) f inferInstance
      ⟨D, hD⟩ ⟨W', hW'⟩ eW'D
  have hsurj : Surjective (Spec.map φ) := by
    constructor
    intro y
    have hy : hD.fromSpec y ∈ (D : Set S) := by
      rw [← hD.range_fromSpec]; exact ⟨y, rfl⟩
    obtain ⟨w, hwW, hw⟩ := hrO hy
    have hwW' : w ∈ (W' : Set U) := by
      rw [hW'eq]
      exact ⟨hwW, show f w ∈ D from hw ▸ hy⟩
    rw [← hW'.range_fromSpec] at hwW'
    obtain ⟨z, rfl⟩ := hwW'
    refine ⟨z, hD.fromSpec.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply, hw]
  have hff : φ.hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff φ).1
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat, hsurj⟩
  refine ⟨Γ(S, D), Γ(U, W'), hD.fromSpec, φ, hW'.fromSpec, inferInstance, ?_, hff, hfp, hfac⟩
  rw [hD.range_fromSpec]
  exact hr

/-- The group algebra of a finitely generated abelian group is finitely presented over any
commutative ring: over `ℤ` finite type suffices, and finite presentation is stable under the
scalar extension `R[Λ] ≅ R ⊗ ℤ[Λ]`. -/
theorem finitePresentation_addMonoidAlgebra (R : Type u) [CommRing R] (Λ : Type u)
    [AddCommGroup Λ] [AddGroup.FG Λ] : Algebra.FinitePresentation R (AddMonoidAlgebra R Λ) := by
  have : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ Λ) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FinitePresentation.equiv (AddMonoidAlgebra.scalarTensorEquiv ℤ R (M := Λ))

/-- The diagonalizable group `D_S(Λ)` of a finitely generated abelian group is affine and
locally of finite presentation over `S`. -/
theorem diagonalizable_isAffineHom_and_lfp (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ]
    [AddGroup.FG Λ] :
    IsAffineHom (diagonalizable S Λ).X.hom ∧
      LocallyOfFinitePresentation (diagonalizable S Λ).X.hom := by
  have h₁ : IsAffineHom (Diagonalizable.groupScheme
      (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := Diagonalizable.isAffineHom _ _
  have h₂ : LocallyOfFinitePresentation (Diagonalizable.groupScheme
      (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact finitePresentation_addMonoidAlgebra _ Λ
  refine ⟨?_, ?_⟩
  · change IsAffineHom (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ h₁
  · change LocallyOfFinitePresentation (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ h₂

/-- A group scheme over `Spec R` that becomes diagonalizable after a faithfully flat base
change `R ⟶ R'` is affine and locally of finite presentation over `Spec R`, by fpqc descent
of both properties of its structure morphism. -/
theorem isAffine_and_lfp_of_faithfullyFlat {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : φ.hom.FaithfullyFlat) (G : GroupScheme (Spec R))
    (hG : IsDiagonalizable ((GroupScheme.baseChange (Spec.map φ)).obj G)) :
    IsAffine G.X.left ∧ LocallyOfFinitePresentation G.X.hom := by
  obtain ⟨Λ, _, hΛ, ⟨e⟩⟩ := hG
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map φ) := ⟨⟨hsurj, hflat⟩, inferInstance⟩
  obtain ⟨hDaff, hDlfp⟩ := diagonalizable_isAffineHom_and_lfp (Spec R') Λ
  let b := Spec.map φ
  have he : e.hom.hom.hom.left ≫ (diagonalizable (Spec R') Λ).X.hom =
      ((GroupScheme.baseChange b).obj G).X.hom := Over.w e.hom.hom.hom
  have : IsIso e.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  have hbcaff : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    rw [← he]; infer_instance
  have hbclfp : LocallyOfFinitePresentation ((GroupScheme.baseChange b).obj G).X.hom := by
    rw [← he]; infer_instance
  have haff : IsAffineHom G.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsAffineHom)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := G.X.hom) (g := b) hQ hbcaff
  have hlfp : LocallyOfFinitePresentation G.X.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := G.X.hom) (g := b) hQ hbclfp
  exact ⟨isAffine_of_isAffineHom G.X.hom, hlfp⟩

/-- **An affine fppf chart of a group of multiplicative type.** Every point `s` of the base
lies in an affine open `Spec R ⟶ S` over which `H` is affine and locally of finite
presentation, and which has a single faithfully flat ring map `R ⟶ R'` of finite
presentation splitting `H`. -/
theorem IsMultiplicativeType.exists_affine_chart {S : Scheme.{u}} {H : GroupScheme S}
    (hH : IsMultiplicativeType H) (s : S) :
    ∃ (R : CommRingCat.{u}) (ι : Spec R ⟶ S), IsOpenImmersion ι ∧ s ∈ Set.range ι ∧
      IsAffine ((GroupScheme.baseChange ι).obj H).X.left ∧
      LocallyOfFinitePresentation ((GroupScheme.baseChange ι).obj H).X.hom ∧
      ∃ (R' : CommRingCat.{u}) (φ : R ⟶ R'), φ.hom.FaithfullyFlat ∧ φ.hom.FinitePresentation ∧
        IsDiagonalizable ((GroupScheme.baseChange (Spec.map φ ≫ ι)).obj H) := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  obtain ⟨u, hu⟩ := 𝒰.covers s
  have : Flat (𝒰.f (𝒰.idx s)) := (𝒰.map_prop _).1
  have : LocallyOfFinitePresentation (𝒰.f (𝒰.idx s)) := (𝒰.map_prop _).2
  obtain ⟨R, R', ι, φ, g, hι, hsι, hφ, hfp, hfac⟩ := exists_affine_fppf_chart (𝒰.f (𝒰.idx s)) u
  have hdiag : IsDiagonalizable ((GroupScheme.baseChange (Spec.map φ ≫ ι)).obj H) :=
    IsDiagonalizable.of_iso (Descent.pullbackComparison _ g _ hfac.symm H).symm
      ((h𝒰 _).baseChange g)
  have hdiag' : IsDiagonalizable
      ((GroupScheme.baseChange (Spec.map φ)).obj ((GroupScheme.baseChange ι).obj H)) :=
    IsDiagonalizable.of_iso (Descent.pullbackComparison ι (Spec.map φ) _ rfl H) hdiag
  obtain ⟨haff, hlfp⟩ := isAffine_and_lfp_of_faithfullyFlat φ hφ _ hdiag'
  exact ⟨R, ι, hι, hu ▸ hsι, haff, hlfp, R', φ, hφ, hfp, hdiag⟩

end Langlands.GroupScheme.RelativeMultiplicativeType
