import Langlands.AlgebraicGeometry.Descent.FppfSeparatedLocallyQuasiFiniteDescentStatement
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Covering
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingProof

/-! # Effective fppf descent of separated locally quasi-finite schemes -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace

variable {S : Scheme.{u}}

/-- Every point `t` of `T` lies in the image of a member `g : V ⟶ T` of a given fppf covering
sieve such that `V` is affine and `g` factors through an affine open `D` of `T` by a flat
morphism of finite presentation. -/
theorem exists_affineChart {T : Over S} {J : Sieve T} (hJ : J ∈ fppfTopology S T)
    (t : T.left) :
    ∃ (D : T.left.Opens) (V : Over S) (g : V ⟶ T) (g' : V.left ⟶ D.toScheme),
      IsAffineOpen D ∧ IsAffine V.left ∧ Flat g' ∧ LocallyOfFinitePresentation g' ∧
        g' ≫ D.ι = g.left ∧ J g ∧ t ∈ Set.range g.left := by
  have : MorphismProperty.IsMultiplicative (@Flat : MorphismProperty Scheme.{u}) :=
    inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := inferInstance
  have : MorphismProperty.IsMultiplicative
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X => (inferInstance : LocallyOfFinitePresentation (𝟙 X)) }
  have : flatLFPScheme.{u}.IsMultiplicative := MorphismProperty.IsMultiplicative.inf
  have hJ' : Sieve.overEquiv T J ∈ Scheme.grothendieckTopology flatLFPScheme.{u} T.left :=
    (GrothendieckTopology.mem_over_iff _ J).1 hJ
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hJ'
  obtain ⟨i, z, hz⟩ := 𝒰.exists_eq t
  obtain ⟨D, hD, htD, -⟩ : ∃ D : T.left.Opens, IsAffineOpen D ∧ t ∈ D ∧ D ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens
    (show t ∈ (⊤ : T.left.Opens) from trivial)
  obtain ⟨W, hW, hzW, hWD⟩ : ∃ W : (𝒰.X i).Opens, IsAffineOpen W ∧ z ∈ W ∧
      W ≤ 𝒰.f i ⁻¹ᵁ D :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (𝒰.X i).isBasis_affineOpens
    (show z ∈ 𝒰.f i ⁻¹ᵁ D by
      show 𝒰.f i z ∈ D
      rw [hz]
      exact htD)
  have hf : flatLFPScheme (𝒰.f i) := 𝒰.map_prop i
  have : Flat (𝒰.f i) := hf.1
  have : LocallyOfFinitePresentation (𝒰.f i) := hf.2
  let V : Over S := Over.mk (W.ι ≫ 𝒰.f i ≫ T.hom)
  let g : V ⟶ T := Over.homMk (W.ι ≫ 𝒰.f i)
  have : IsAffine V.left := hW
  refine ⟨D, V, g, (𝒰.f i).resLE D W hWD, hD, inferInstance, inferInstance, inferInstance,
    Scheme.Hom.resLE_comp_ι _ _, ?_, ⟨⟨z, hzW⟩, hz⟩⟩
  have hi : Sieve.overEquiv T J (𝒰.f i) := h𝒰 _ _ (Presieve.ofArrows.mk i)
  rw [Sieve.overEquiv_iff] at hi
  convert J.downward_closed hi (Over.homMk W.ι : V ⟶ Over.mk (𝒰.f i ≫ T.hom)) using 1
  exact Over.OverMorphism.ext rfl

/-- A jointly surjective family of flat morphisms locally of finite presentation generates an
fppf covering sieve. -/
theorem ofArrows_mem_fppfTopology {T : Over S} {I : Type u} {V : I → Over S}
    (g : ∀ i, V i ⟶ T) (hflat : ∀ i, Flat (g i).left)
    (hlfp : ∀ i, LocallyOfFinitePresentation (g i).left)
    (hsurj : ∀ t : T.left, ∃ i, t ∈ Set.range (g i).left) :
    Sieve.ofArrows V g ∈ fppfTopology S T := by
  let 𝒰 := Scheme.Cover.mkOfCovers (P := flatLFPScheme.{u}) I (fun i => (V i).left)
    (fun i => (g i).left) (fun t => by
      obtain ⟨i, y, hy⟩ := hsurj t
      exact ⟨i, y, hy⟩) (fun i => ⟨hflat i, hlfp i⟩)
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact 𝒰.mem_grothendieckTopology

/-- Stacks Project Lemma 02W8 (sheaf form): effective fppf descent of separated, locally
quasi-finite morphisms locally of finite type. -/
theorem fppfSeparatedLocallyQuasiFiniteDescent :
    FppfSeparatedLocallyQuasiFiniteDescentStatement.{u} := by
  intro S G T p J hJ hrep
  choose D V g g' hD hV hg'flat hg'lfp hg'ι hgJ hgt using exists_affineChart hJ
  choose X' x' a' hpb hsep hlqf hlft using fun t => hrep (g t) (hgJ t)
  have hcover : Sieve.ofArrows V g ∈ fppfTopology S T :=
    ofArrows_mem_fppfTopology g
      (fun t => by
        have := hg'flat t
        rw [← hg'ι t]
        infer_instance)
      (fun t => by
        have := hg'lfp t
        rw [← hg'ι t]
        infer_instance)
      (fun t => ⟨t, hgt t⟩)
  -- An open chart of `G` through an affine open neighbourhood of each point of each `X' t`.
  have hchart : ∀ (t : T.left) (ξ : (X' t).left), ∃ (Y : Over S)
      (b : (schemeYoneda S).obj Y ⟶ G.obj) (U : (X' t).left.Opens)
      (z : openOver (X' t) U ⟶ Y), ξ ∈ U ∧ AlgebraicSpace.IsOpenImmersion b ∧
        (schemeYoneda S).map z ≫ b = (schemeYoneda S).map (openOverι (X' t) U) ≫ a' t := by
    intro t ξ
    obtain ⟨U, hU, hξU, -⟩ : ∃ U : (X' t).left.Opens, IsAffineOpen U ∧ ξ ∈ U ∧ U ≤ ⊤ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (X' t).left.isBasis_affineOpens
      (show ξ ∈ (⊤ : (X' t).left.Opens) from trivial)
    have := hsep t
    have := hlqf t
    have := hlft t
    have : IsAffine (D t).toScheme := hD t
    have := hV t
    have := hg'flat t
    have := hg'lfp t
    obtain ⟨Y, b, z, hb, hz⟩ := exists_openChart (hpb t) (D t).ι (g' t) (hg'ι t) U hU
    exact ⟨Y, b, U, z, hξU, hb, hz⟩
  choose Y b U z hξU hb hz using hchart
  let K := Σ t : T.left, (X' t).left
  let Y' : K → Over S := fun k => Y k.1 k.2
  let b' : ∀ k, (schemeYoneda S).obj (Y' k) ⟶ G.obj := fun k => b k.1 k.2
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc b') :=
    isLocallySurjective_sigmaDesc_of_charts p g hcover x' a' hpb b'
      (fun t ξ => ⟨⟨t, ξ⟩, U t ξ, z t ξ, hξU t ξ, hz t ξ⟩)
  obtain ⟨X, ⟨e⟩⟩ := openChartGluing S G K Y' b' (fun k => hb k.1 k.2) hsurj
  exact ⟨X, (schemeYoneda S).preimage (e.hom ≫ p), e, (Functor.map_preimage _ _).symm⟩

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
