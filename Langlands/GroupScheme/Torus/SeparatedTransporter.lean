import Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation
import Langlands.AlgebraicGeometry.SquareZeroLiftingSmooth
import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Torus.HenselianSplitConjugacy
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Cohomology.SourceTransport

/-! # Smooth transporters in separated groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.PointwiseSchemeAction

private theorem equalizer_lfp {S : Scheme.{u}} {X Y : Over S}
    [LocallyOfFinitePresentation Y.hom] (f g : X ⟶ Y) :
    LocallyOfFinitePresentation (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation _
    (Over.prodLeftIsoPullback Y Y).hom]
  have h : LocallyOfFinitePresentation (pullback.diagonal Y.hom) := by
    have : LocallyOfFinitePresentation (pullback.diagonal Y.hom ≫ pullback.fst Y.hom Y.hom) := by
      rw [pullback.diagonal_fst]
      infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp
      (pullback.diagonal Y.hom) (pullback.fst Y.hom Y.hom)
  convert! h
  ext1 <;> simp [← Over.comp_left]

/-- The transporter relation on a test scheme is conjugacy of the corresponding
base-changed maps by the point of the base-changed group. -/
theorem isTransporter_iff_conjugateRelative {S : Scheme.{u}} {H G : GroupScheme S}
    (i₁ i₂ : H ⟶ G) {U : Over S} (g : U ⟶ G.X) :
    IsTransporter i₁ i₂ g ↔
      (baseChange U.hom).map i₁ = HomScheme.conjugateRelative ((baseChange U.hom).map i₂) g := by
  let b := U.hom
  let c : (Over.map b).obj (Over.mk (𝟙 U.left)) ≅ U :=
    Over.isoMk (Iso.refl U.left) (by simp [b])
  let p := RelativeLevi.pulledBackPoint G U g
  have hp : baseChangePointsEquiv b G _ p = c.hom ≫ g := by
    apply Over.OverMorphism.ext
    rw [baseChangePointsEquiv_left]
    change pullback.lift g.left (𝟙 U.left) _ ≫ pullback.fst G.X.hom b = 𝟙 U.left ≫ g.left
    rw [pullback.lift_fst, Category.id_comp]
  have he : IsTransporter ((baseChange b).map i₁) ((baseChange b).map i₂) p ↔
      IsTransporter i₁ i₂ g := by
    constructor
    · intro h
      have h' := h.baseChangePointsEquiv b
      rw [hp] at h'
      simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h'.restrict c.inv
    · intro h
      exact h.baseChange b c.hom p hp
  exact he.symm.trans (isTransporter_iff_conjugation_eq.trans eq_comm)

section Representability

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {G : GroupScheme (Spec R)} [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
  (i₁ i₂ : (Diagonalizable.groupScheme R Λ).toGrp ⟶ G)

private abbrev diagonalizableSource (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] : Over (Spec R) := (Diagonalizable.groupScheme R Λ).toGrp.X

local notation "H₀" => diagonalizableSource R Λ

/-- A closed locally finitely presented scheme representing the actual transporter
of two maps from the same diagonalizable group into a separated group. -/
def separatedTransporterModel :
    Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation.Model
      (equalizer.ι (twistedTransporter i₁ i₂).hom (snd H₀ G.X)) := by
  let : Flat (H₀).hom := Diagonalizable.flat_structure R Λ
  let : Module.Free R (((algΓ R).obj H₀).unop) := Diagonalizable.free_coordinateModule R Λ
  let : LocallyOfFinitePresentation
      (equalizer.ι (twistedTransporter i₁ i₂).hom (snd H₀ G.X)).left := equalizer_lfp _ _
  exact Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation.model H₀ _

/-- The model represents the transporter condition on every test scheme. -/
theorem exists_separatedTransporterModel_factor_iff {U : Over (Spec R)} (g : U ⟶ G.X) :
    (∃ z : U ⟶ (separatedTransporterModel i₁ i₂).source,
      z ≫ (separatedTransporterModel i₁ i₂).ι = g) ↔ IsTransporter i₁ i₂ g := by
  let a := twistedTransporter i₁ i₂
  rw [(separatedTransporterModel i₁ i₂).represents, ← twistedTransporter_isFixed_iff]
  change (∃ q : H₀ ⊗ U ⟶ equalizer a.hom (snd H₀ G.X), q ≫ equalizer.ι _ _ = H₀ ◁ g) ↔ a.IsFixed g
  have he : (∃ q : H₀ ⊗ U ⟶ equalizer a.hom (snd H₀ G.X),
      q ≫ equalizer.ι _ _ = H₀ ◁ g) ↔
      (H₀ ◁ g) ≫ a.hom = snd H₀ U ≫ g := by
    constructor
    · rintro ⟨q, hq⟩
      rw [← whiskerLeft_snd, ← hq, Category.assoc, Category.assoc, equalizer.condition]
    · intro h
      exact ⟨equalizer.lift _ (h.trans (whiskerLeft_snd H₀ g).symm), equalizer.lift_ι _ _⟩
  rw [he]
  have hlift : lift (fst H₀ U) (snd H₀ U ≫ g) = H₀ ◁ g := by
    apply hom_ext <;> simp
  constructor
  · intro hg V b h
    have e := congrArg (fun k => lift h b ≫ k) hg
    simpa only [Category.assoc, lift_whiskerLeft_assoc, lift_snd_assoc, act] using e
  · intro hg
    simpa only [act, hlift] using hg (H₀ ⊗ U) (snd H₀ U) (fst H₀ U)

end Representability

/-- A prescribed transporter between two maps from a diagonalizable group lifts over
an arbitrary affine square-zero thickening in a smooth group. -/
theorem exists_transporter_lift_squareZero {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth G.X.hom] (i₁ i₂ : H ⟶ G) (hDiag : RelativeMultiplicativeType.IsDiagonalizable H)
    (C : CommRingCat.{u}) (I : Ideal C) (hI : I ^ 2 = ⊥)
    (y : Spec C ⟶ S)
    (g₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) ⟶ G.X)
    (hg₀ : IsTransporter i₁ i₂ g₀) :
    ∃ g : Over.mk y ⟶ G.X, IsTransporter i₁ i₂ g ∧
      Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl ≫ g = g₀ := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let b := q ≫ y
  let U := Over.mk y
  let U₀ := Over.mk b
  let a : U₀ ⟶ U := Over.homMk q
  let : IsAffineHom ((baseChange y).obj H).X.hom := (hDiag.baseChange y).isAffineHom
  have hflat : Flat ((baseChange y).obj H).X.hom := (hDiag.baseChange y).flat
  have haff : IsAffine ((baseChange y).obj H).X.left :=
    isAffine_of_isAffineHom ((baseChange y).obj H).X.hom
  have hcoh := Cohomology.hasVanishingLowDegreeCohomology_of_isDiagonalizable (hDiag.baseChange b)
  have hdeform : HomScheme.HasConjugatorLifting H G a :=
    HomScheme.squareZeroHomomorphismCohomology S H G C I hI y b rfl hflat haff hcoh
  obtain ⟨g, hg, he⟩ := hdeform.2 ((baseChange U.hom).map i₂) ((baseChange U.hom).map i₁) g₀ (by
    simpa only [HomScheme.evaluate_baseChange] using
      (isTransporter_iff_conjugateRelative i₁ i₂ g₀).mp hg₀)
  exact ⟨g, (isTransporter_iff_conjugateRelative i₁ i₂ g).mpr he, hg⟩

open Langlands.AlgebraicGeometry in
/-- The actual transporter model is smooth for a finitely generated character
group and a smooth separated ambient group. -/
theorem smooth_separatedTransporterModel {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    [AddGroup.FG Λ] {G : GroupScheme (Spec R)} [IsSeparated G.X.hom] [Smooth G.X.hom]
    (i₁ i₂ : (Diagonalizable.groupScheme R Λ).toGrp ⟶ G) :
    Smooth (separatedTransporterModel i₁ i₂).source.hom := by
  let L := separatedTransporterModel i₁ i₂
  let : IsClosedImmersion L.ι.left := L.isClosedImmersion
  let : Mono L.ι := Over.mono_of_mono_left L.ι
  let : LocallyOfFinitePresentation L.source.hom := by
    let : LocallyOfFinitePresentation L.ι.left := L.locallyOfFinitePresentation
    rw [← Over.w L.ι]
    infer_instance
  apply HasAffineSquareZeroLifting.smooth
  intro C I hI z₀ y hz₀
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let b := q ≫ y
  let a : Over.mk b ⟶ Over.mk y := Over.homMk q
  let z : Over.mk b ⟶ L.source := Over.homMk z₀ hz₀
  have hz : IsTransporter i₁ i₂ (z ≫ L.ι) :=
    (exists_separatedTransporterModel_factor_iff i₁ i₂ _).mp ⟨z, rfl⟩
  obtain ⟨g, hg, he⟩ := exists_transporter_lift_squareZero i₁ i₂
    (Diagonalizable.isDiagonalizable_groupScheme R Λ) C I hI y (z ≫ L.ι) hz
  obtain ⟨x, hx⟩ := (exists_separatedTransporterModel_factor_iff i₁ i₂ _).mpr hg
  have hrec : a ≫ x = z := by
    apply (cancel_mono L.ι).mp
    rw [Category.assoc, hx]
    exact he
  exact ⟨x.left, Over.w x, congrArg Over.Hom.left hrec⟩

section Henselian

variable {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsSeparated G.X.hom] [Smooth G.X.hom]

/-- A specified residue transporter lifts over the Henselian ring for a
finitely generated diagonalizable source, without affineness of the target. -/
theorem exists_henselian_transporter_of_separated
    {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    (i₁ i₂ : (Diagonalizable.groupScheme (CommRingCat.of R) Λ).toGrp ⟶ G)
    (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ G.X) (hg₀ : IsTransporter i₁ i₂ g₀) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsTransporter i₁ i₂ g ∧
        (Over.homMk (Spec.algebraMap R k) (by simp) :
          Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ g = g₀ := by
  let L := separatedTransporterModel i₁ i₂
  obtain ⟨y, hy⟩ := (exists_separatedTransporterModel_factor_iff i₁ i₂ _).mpr hg₀
  let : Smooth L.source.hom := smooth_separatedTransporterModel i₁ i₂
  obtain ⟨s, hs, hsk⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk L.source.hom y.left (Over.w y)
  let a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ L.source := Over.homMk s hs
  refine ⟨a ≫ L.ι, (exists_separatedTransporterModel_factor_iff i₁ i₂ _).mp ⟨a, rfl⟩, ?_⟩
  apply Over.OverMorphism.ext
  change (Spec.algebraMap R k ≫ s) ≫ L.ι.left = g₀.left
  rw [hsk]
  exact congrArg Over.Hom.left hy

/-- Exact Henselian lifting for a source isomorphic to a finitely generated
relative diagonalizable group. -/
theorem exists_henselian_transporter_of_diagonalizable_of_separated
    {H : GroupScheme (Spec (CommRingCat.of R))} (j₁ j₂ : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (Spec.algebraMap R k) ⟶ G.X) (hg₀ : IsTransporter j₁ j₂ g₀) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X,
      IsTransporter j₁ j₂ g ∧
        (Over.homMk (Spec.algebraMap R k) (by simp) :
          Over.mk (Spec.algebraMap R k) ⟶ Over.mk (𝟙 _)) ≫ g = g₀ := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  let d := Diagonalizable.relativeModelIso (CommRingCat.of R) Λ ≪≫ e.symm
  obtain ⟨g, hg, he⟩ := exists_henselian_transporter_of_separated
    (d.hom ≫ j₁) (d.hom ≫ j₂) hk g₀ (hg₀.precomp d.hom)
  refine ⟨g, ?_, he⟩
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hg.precomp d.inv

end Henselian

end Langlands.GroupScheme.PointwiseSchemeAction

namespace Langlands.GroupScheme

section Henselian

variable {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsSeparated G.X.hom] [Smooth G.X.hom]
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R))}
    (j₁ : T₁.toGrp ⟶ G) (j₂ : T₂.toGrp ⟶ G)

/-- A prescribed residue conjugacy of two split tori in a smooth separated group
lifts, recovering both its conjugating point and its source isomorphism. -/
theorem exists_henselian_splitTorus_conjugacy_lift_of_separated
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((baseChange (Spec.algebraMap R k)).obj G).X)
    (e₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁ ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₂)
    (h₀ : (baseChange (Spec.algebraMap R k)).map j₁ ≫
        (((baseChange (Spec.algebraMap R k)).obj G).innerIso g₀).hom =
      CommGroupScheme.groupHom e₀.hom ≫ (baseChange (Spec.algebraMap R k)).map j₂) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (e : T₁ ≅ T₂),
      j₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G g = g₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso e = e₀ := by
  let b := Spec.algebraMap R k
  obtain ⟨e, he⟩ := hT₁.isomorphism_fieldBaseChange_surjective b hT₂ e₀
  have h₀' : (baseChange b).map j₁ ≫ (((baseChange b).obj G).innerIso g₀).hom =
      (baseChange b).map (CommGroupScheme.groupHom e.hom ≫ j₂) := by
    rw [Functor.map_comp]
    change (baseChange b).map j₁ ≫ (((baseChange b).obj G).innerIso g₀).hom =
      CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).mapIso e).hom ≫
        (baseChange b).map j₂
    have heq := congrArg (fun σ : (CommGroupScheme.baseChange b).obj T₁ ≅
        (CommGroupScheme.baseChange b).obj T₂ =>
      CommGroupScheme.groupHom σ.hom ≫ (baseChange b).map j₂) he
    exact h₀.trans heq.symm
  have ht := PointwiseSchemeAction.isTransporter_iff_conjugation_eq.mpr h₀'
  let c : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Over.homMk (𝟙 _) (by simp)
  obtain ⟨g, hg, hrec⟩ :=
    PointwiseSchemeAction.exists_henselian_transporter_of_diagonalizable_of_separated
      (CommGroupScheme.groupHom e.hom ≫ j₂) j₁ hT₁.isRelativeDiagonalizable hk
      (c ≫ baseChangePointsEquiv b G _ g₀) ((ht.baseChangePointsEquiv b).restrict c)
  refine ⟨g, e, PointwiseSchemeAction.isTransporter_iff_conjugation_eq.mp hg, ?_, he⟩
  apply (baseChangePointsEquiv b G _).injective
  rw [baseChangePointsEquiv_baseChangeSectionHom]
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left hrec
  change b ≫ g.left = (𝟙 (Spec (CommRingCat.of k))) ≫
    g₀.left ≫ pullback.fst G.X.hom b at hh
  change b ≫ g.left = g₀.left ≫ pullback.fst G.X.hom b
  simpa only [Category.id_comp] using hh

/-- Split tori with maximal residues in a connected affine smooth group over an
algebraically closed residue field are integrally conjugate in the separated
ambient group. Only the residue fibre is required to be affine. -/
theorem exists_henselian_splitTorus_conjugacy_of_separated
    [IsAlgClosed k] [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
    [IsAffineHom ((baseChange (Spec.algebraMap R k)).obj G).X.hom]
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hk : Function.Surjective (algebraMap R k))
    (hj₁ : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁)
      ((baseChange (Spec.algebraMap R k)).map j₁))
    (hj₂ : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₂)
      ((baseChange (Spec.algebraMap R k)).map j₂)) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (e : T₁ ≅ T₂),
      j₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂ := by
  let b := Spec.algebraMap R k
  let : Smooth ((baseChange b).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  obtain ⟨g₀, e₀, h₀⟩ := maximalTorusConjugacy k ((baseChange b).obj G)
    ((CommGroupScheme.baseChange b).obj T₁) ((CommGroupScheme.baseChange b).obj T₂)
    ((baseChange b).map j₁) ((baseChange b).map j₂) hj₁ hj₂
  obtain ⟨g, e, he, -, -⟩ := exists_henselian_splitTorus_conjugacy_lift_of_separated
    j₁ j₂ hT₁ hT₂ hk g₀ e₀ h₀
  exact ⟨g, e, he⟩

end Henselian

end Langlands.GroupScheme
