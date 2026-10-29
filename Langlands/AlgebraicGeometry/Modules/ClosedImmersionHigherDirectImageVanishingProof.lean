import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingStatement

/-! # Higher direct images along a closed immersion vanish: proof -/

universe w' w v v' u u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace ClosedImmersionHigherDirectImageVanishing

section ToSheaf

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups preserves
colimits of every shape that exists in abelian groups. -/
lemma toSheaf_preservesColimit {K : Type w} [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] (F : K ⥤ SheafOfModules.{v} R) :
    PreservesColimit F (SheafOfModules.toSheaf.{v} R) := by
  let S := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙ S :=
    Functor.isoWhiskerLeft F
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
  suffices PreservesColimit ((F ⋙ SheafOfModules.forget R) ⋙ S)
      (SheafOfModules.toSheaf.{v} R) from preservesColimit_of_iso_diagram _ e.symm
  have : PreservesColimitsOfShape K (S ⋙ SheafOfModules.toSheaf.{v} R) :=
    inferInstanceAs (PreservesColimitsOfShape K
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}))
  have hc := colimit.isColimit (F ⋙ SheafOfModules.forget R)
  exact preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves S hc)
    ((isColimitOfPreserves (S ⋙ SheafOfModules.toSheaf.{v} R) hc).ofIsoColimit
      (Functor.mapCoconeMapCocone _).symm)

instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) where
  preservesFiniteColimits _ _ _ := ⟨fun {F} => toSheaf_preservesColimit R F⟩

end ToSheaf

variable {X Y : Scheme.{u}}

/-- An epimorphism of `𝒪_X`-modules is locally surjective on underlying abelian presheaves. -/
lemma isLocallySurjective_of_epi {M N : X.Modules} (φ : M ⟶ N) [Epi φ] :
    TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf := by
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).2
    (@preserves_epi_of_preservesColimit _ _ _ _ _ _ _ φ
      (toSheaf_preservesColimit X.ringCatSheaf (span φ φ)) _)

/-- A morphism of `𝒪_X`-modules which is locally surjective on underlying abelian presheaves
is an epimorphism. -/
lemma epi_of_isLocallySurjective {M N : X.Modules} (φ : M ⟶ N)
    (h : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf) : Epi φ := by
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).1 h
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map this

/-- Sections of an `𝒪_X`-module over an empty open form a subsingleton. -/
lemma subsingleton_sections_of_eq_bot (M : X.Modules) {U : X.Opens} (hU : U = ⊥) :
    Subsingleton Γ(M, U) := by
  have h : IsTerminal (M.presheaf.obj (op U)) :=
    TopCat.Sheaf.isTerminalOfEqEmpty ⟨M.presheaf, M.isSheaf⟩ hU
  exact AddCommGrpCat.subsingleton_of_isZero
    ((isZero_zero _).of_iso (h.uniqueUpToIso (isZero_zero _).isTerminal))

/-- Pushforward along a closed immersion preserves local surjectivity. -/
lemma isLocallySurjective_pushforward (i : X ⟶ Y) [IsClosedImmersion i] {M N : X.Modules}
    (φ : M ⟶ N) (h : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf) :
    TopCat.Presheaf.IsLocallySurjective ((Scheme.Modules.pushforward i).map φ).mapPresheaf := by
  rw [TopCat.Presheaf.isLocallySurjective_iff] at h ⊢
  intro W t y hy
  by_cases hyr : y ∈ Set.range i.base
  · obtain ⟨x, rfl⟩ := hyr
    obtain ⟨V, hV, ⟨s, hs⟩, hxV⟩ := h (i ⁻¹ᵁ W) t x hy
    obtain ⟨W₀, hW₀, hW₀V⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.1 V.isOpen
    have hW' : i ⁻¹ᵁ (W ⊓ ⟨W₀, hW₀⟩) = V := by
      apply le_antisymm
      · intro z hz
        have hz₀ : z ∈ i.base ⁻¹' W₀ := hz.2
        rw [hW₀V] at hz₀
        exact hz₀
      · intro z hz
        have hz₀ : z ∈ i.base ⁻¹' W₀ := by
          rw [hW₀V]
          exact hz
        exact ⟨hV hz, hz₀⟩
    subst hW'
    refine ⟨W ⊓ ⟨W₀, hW₀⟩, inf_le_left, ⟨s, hs⟩, hy, ?_⟩
    have hx₀ : x ∈ i.base ⁻¹' W₀ := hxV.2
    exact hx₀
  · let W' : Y.Opens :=
      W ⊓ ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hW' : i ⁻¹ᵁ W' = ⊥ := by
      ext z
      simp [W']
    exact ⟨W', inf_le_left,
      ⟨0, @Subsingleton.elim _ (subsingleton_sections_of_eq_bot N hW') _ _⟩, hy, hyr⟩

/-- Pushforward along a closed immersion preserves epimorphisms. -/
lemma pushforward_preservesEpimorphisms (i : X ⟶ Y) [IsClosedImmersion i] :
    (Scheme.Modules.pushforward i).PreservesEpimorphisms where
  preserves φ _ := epi_of_isLocallySurjective _
    (isLocallySurjective_pushforward i φ (isLocallySurjective_of_epi φ))

end ClosedImmersionHigherDirectImageVanishing

open ClosedImmersionHigherDirectImageVanishing in
/-- Higher direct images along a closed immersion vanish in every positive degree. -/
theorem closedImmersionHigherDirectImageVanishing :
    ClosedImmersionHigherDirectImageVanishingStatement.{u} := by
  intro X Y i _ M q
  have := pushforward_preservesEpimorphisms i
  have : (Scheme.Modules.pushforward i).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let I : InjectiveResolution M := injectiveResolution M
  refine IsZero.of_iso ?_ (DerivedSections.higherDirectImageIsoOfResolution i I (q + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  have h := I.cocomplex_exactAt_succ q
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (Scheme.Modules.pushforward i)

end Langlands.AlgebraicGeometry.Modules
