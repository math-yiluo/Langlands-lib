import Langlands.GroupScheme.SplitSolvableSchemeStatement
import Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.CharacterProjection

/-! # Milne 16.56 from the splitness of the canonical extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitSolvableScheme

open RelativeRoot

section Product

variable {R : CommRingCat.{u}}

/-- If `K ⟶ H ⟶ V` is an fppf quotient of an affine group by a closed subgroup with a split
series and `V` is affine, the quotient map has a section `σ` and `(κ, t) ↦ j(κ) · σ(t)`
identifies `K ⊗ V` with `H` as schemes over `Spec R`. -/
theorem nonempty_tensor_iso_of_hasSplitSeries {K H V : GroupScheme (Spec R)}
    (j : K ⟶ H) (q : H ⟶ V) (hj : IsClosedSubgroup j)
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q) {n : ℕ} (hK : HasSplitSeries n K)
    [IsAffineHom H.X.hom] [IsAffine V.X.left] :
    Nonempty (K.X ⊗ V.X ≅ H.X) := by
  obtain ⟨hflat, hsurj, hlfp, hjq⟩ := hq
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom K.X.hom := hj.isAffineHom
  have hKv := SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries
    (fun _ hV' T _ U _ _ _ ξ => Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV' T U ξ)
    n K hK this
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Flat q.hom.hom.left := hflat
  have : Surjective q.hom.hom.left := hsurj
  have : LocallyOfFinitePresentation q.hom.hom.left := hlfp
  obtain ⟨σ, hσ⟩ := SplitUnipotentAffineTorsor.exists_section j q hjq hKv
  have hjq1 : j.hom.hom ≫ q.hom.hom = 1 := by
    have h := SplitUnipotentAffineTorsor.comp_comp_eq_one hjq (𝟙 K.X)
    rwa [Category.id_comp] at h
  have : IsIso ((fst K.X V.X ≫ j.hom.hom) * (snd K.X V.X ≫ σ)) :=
    SplitSeriesDecomposition.isIso_mul_of_section j.hom.hom q.hom.hom hjq1 σ hσ
      (fun x hx => SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hjq x hx)
  exact ⟨asIso ((fst K.X V.X ≫ j.hom.hom) * (snd K.X V.X ≫ σ))⟩

end Product

section Main

/-- A split torus over any base is isomorphic to the split torus indexed by
`ULift (Fin m)` for some `m`. -/
theorem nonempty_iso_splitTorus_ulift_fin {S : Scheme.{u}} {D : GroupScheme S}
    (hD : IsSplitTorus D) :
    ∃ m : ℕ, Nonempty (D ≅ splitTorus S (ULift.{u} (Fin m))) := by
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨m, ⟨eI⟩⟩ := Finite.exists_equiv_fin I
  exact ⟨m, ⟨eD ≪≫ splitTorus.coordinatePermutationIso S (Equiv.ulift.trans eI.symm)⟩⟩

/-- Milne 16.56 follows once every canonical extension of a split solvable group is known to
have a split unipotent kernel and a split torus as quotient. -/
theorem splitSolvableSchemeProduct_of_split
    (h : ∀ (k : Type u) [Field k] (G U D : GroupScheme (Spec (CommRingCat.of k)))
      (i : U ⟶ G) (q : G ⟶ D),
      IsSplitSolvableGroupScheme G → IsClosedSubgroup i → IsUnipotent U →
      IsFppfQuotient (SubgroupFunctor.range i) q → IsMultiplicativeType D →
      IsSplitUnipotent U ∧ IsSplitTorus D) :
    SplitSolvableSchemeProductStatement.{u} := by
  intro k _ G hG U D i q hi hU _ hq hD
  obtain ⟨⟨r, hser⟩, hsplit⟩ := h k G U D i q hG hi hU hq hD
  obtain ⟨m, ⟨eT⟩⟩ := nonempty_iso_splitTorus_ulift_fin hsplit
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : IsAffine D.X.left := hD.isAffine
  obtain ⟨eA⟩ := splitUnipotentAffineSpaceStatement.{u} k r U inferInstance hser
  obtain ⟨eP⟩ := nonempty_tensor_iso_of_hasSplitSeries i q hi hq hser
  exact ⟨r, m, ⟨eA⟩, ⟨eT⟩, ⟨eP.symm ≪≫ tensorIso eA ((Grp.forget _).mapIso eT)⟩⟩

end Main

end Langlands.GroupScheme.SplitSolvableScheme
