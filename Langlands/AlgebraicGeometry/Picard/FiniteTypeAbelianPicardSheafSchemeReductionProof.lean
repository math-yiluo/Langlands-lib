import Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.DisjointCoverAFRepresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.MinimalPrimeNormalizationCover
import Langlands.AlgebraicGeometry.Picard.AbelianPicardSheafSeparated
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement
import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeStatement
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheafBaseChange

/-! # Scheme representability of the Picard sheaf from the normal case

Let `R` be of finite type over `ℤ` and `A` an abelian scheme over `Spec R`. Suppose the
Picard sheaf of `A` is an algebraic space, and that over every integrally closed
finite-type `ℤ`-domain the Picard sheaf of an abelian scheme is represented by a scheme
whose finite sets of points lie in affine opens. Then the Picard sheaf of `A` is
represented by a scheme.

Over the normalization cover `g : S' = ∐_p Spec (R ⧸ p)^ν ⟶ Spec R` the restricted Picard
sheaf is represented on each component by the Picard scheme of the base-changed abelian
scheme. These representatives glue along the disjoint components to an AF scheme `V'` over
`S'`. The induced chart `V' ⟶ Pic(A/R)` is finite and surjective because `g` is, and the
Picard space is quasi-separated, so the published AF descent makes it a scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

open NoetherianApproximation MinimalPrimeNormalization AlgebraicSpace

/-- The Picard sheaf of an abelian scheme over a finite-type `ℤ`-algebra is represented by
a scheme, given that it is an algebraic space and the normal-domain AF representation. -/
theorem finiteTypeAbelianPicardSheafScheme_of_algebraicSpace_of_normal
    (h1 : FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u})
    (h3 : NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}) :
    FiniteTypeAbelianPicardSheafSchemeStatement.{u} := by
  intro R _ _ A
  let S := Spec (CommRingCat.of R)
  let Y : AlgebraicSpace S := ⟨RelativePicard.classSheaf A.X.hom, (h1 R A).1⟩
  have hY : IsQuasiSeparated Y := AbelianScheme.classSheaf_isQuasiSeparated A (h1 R A).1
  let N : minimalPrimes R → Scheme.{u} := fun p ↦ Spec (CommRingCat.of (Normalization R p.1))
  let g : ∐ N ⟶ S := cover R
  let φ : ∀ p, N p ⟶ S := fun p ↦ Spec.map (CommRingCat.ofHom (toNormalization R p.1))
  have hφ : ∀ p, φ p = Sigma.ι N p ≫ g := fun p ↦ (ι_cover R p).symm
  -- The Picard scheme of each component.
  have hP : ∀ p : minimalPrimes R, ∃ P : Over (N p),
      PointTopology.HasFiniteAffineNeighborhoods P.left ∧
        Nonempty ((RelativePicard.classSheafPresheaf
          ((AbelianScheme.baseChange (φ p)).obj A).X.hom).RepresentableBy P) := fun p ↦
    have : p.1.IsPrime := p.2.1.1
    h3 (Normalization R p.1) ((AbelianScheme.baseChange (φ p)).obj A)
  choose H hH r using hP
  -- The Picard sheaf restricted to the normalization cover.
  let F' : AlgebraicSpace.Presheaf (∐ N) :=
    (Over.map g).op ⋙ RelativePicard.classSheafPresheaf A.X.hom
  have hF' : Presheaf.IsSheaf (fppfTopology (∐ N)) F' :=
    (((Over.map g).sheafPushforwardContinuous (Type (u + 1)) (Scheme.fppfTopology.over (∐ N))
      (Scheme.fppfTopology.over S)).obj (RelativePicard.classSheaf A.X.hom)).property
  have hdisj : Pairwise fun k l : minimalPrimes R ↦
      Disjoint (Set.range (Sigma.ι N k)) (Set.range (Sigma.ι N l)) := by
    intro k l hkl
    have := disjoint_opensRange_sigmaι N k l hkl
    rw [← TopologicalSpace.Opens.coe_disjoint] at this
    simpa only [Scheme.Hom.coe_opensRange] using this
  let e : ∀ p : minimalPrimes R,
      (schemeYoneda (N p)).obj (H p) ≅ (Over.map (Sigma.ι N p)).op ⋙ F' := fun p ↦
    (Functor.RepresentableBy.equivUliftYonedaIso _ _ (r p).some) ≪≫
      RelativePicard.classSheafPresheafBaseChangeIso A.X.hom (φ p) ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (Over.mapCongr _ _ (hφ p) ≪≫ Over.mapComp (Sigma.ι N p) g)).symm
        (RelativePicard.classSheafPresheaf A.X.hom)
  have : Finite (sigmaOpenCover N).I₀ := inferInstanceAs (Finite (minimalPrimes R))
  obtain ⟨V', hV', ⟨E⟩⟩ :=
    LocalRepresentation.exists_representation_of_disjoint_cover hF' (sigmaOpenCover N) hdisj
      H hH e
  -- The finite surjective chart from the glued AF scheme.
  let π : (schemeYoneda S).obj ((Over.map g).obj V') ⟶ Y.presheaf :=
    LocalRepresentation.chart g V' E
  have hπ : AlgebraicSpace.IsFinite π :=
    LocalRepresentation.chart_relative g V' E @_root_.AlgebraicGeometry.IsFinite
      (cover_isFinite R)
  have hs : AlgebraicSpace.IsSurjective π :=
    LocalRepresentation.chart_relative g V' E @Surjective (cover_surjective R)
  obtain ⟨P, ⟨eP⟩⟩ := AFDescentOpenCharts.exists_representation
    finiteSurjectiveQuasiAffineSourceAF π hπ hs hV' hY
  exact ⟨P, ⟨(Functor.RepresentableBy.equivUliftYonedaIso _ _).symm eP⟩⟩

/-- The published reduction statement. -/
theorem finiteTypeAbelianPicardSheafSchemeReduction :
    FiniteTypeAbelianPicardSheafSchemeReductionStatement.{u} :=
  fun h1 h3 ↦ finiteTypeAbelianPicardSheafScheme_of_algebraicSpace_of_normal h1 h3

end Langlands.AlgebraicGeometry.Picard
