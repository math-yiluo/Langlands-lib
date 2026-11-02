import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartPoint
import Langlands.Sheaf.Godement
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Pi

/-! # Godement constructions from all points of the finite rational chart site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u vE uE

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.Godement

open CategoryTheory CategoryTheory.Limits Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
variable (E : Type uE) [Category.{vE} E]
  [HasProducts.{u} E] [HasColimitsOfSize.{u, u} E]

/-- Coefficient sheaves on the actual finite rational chart site. -/
abbrev CoefficientSheaf := CategoryTheory.Sheaf (finiteRationalTopology K A) E

/-- The family of all actual spectrum-point stalks. -/
def stalkFamily : CoefficientSheaf (A := A) E ⥤ (BanachSpectrum A → E) :=
  Functor.pi' fun x => stalk E x

/-- Direct image of an actual coefficient family is the product of its
point skyscrapers. -/
def skyscraperFamily : (BanachSpectrum A → E) ⥤ CoefficientSheaf (A := A) E :=
  Functor.pi (fun x => (spectrumPoint x).skyscraperSheafFunctor (A := E)) ⋙
    Pi.functor (BanachSpectrum A)

variable {E}

/-- The universal property of the product of the individual stalk/skyscraper
adjunctions. -/
def familyHomEquiv (F : CoefficientSheaf (A := A) E) (M : BanachSpectrum A → E) :
    ((stalkFamily E).obj F ⟶ M) ≃ (F ⟶ (skyscraperFamily E).obj M) where
  toFun f := Pi.lift fun x => (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x) (f x)
  invFun g x := ((spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x)).symm
    (g ≫ Pi.π (fun x => (spectrumPoint x).skyscraperSheaf (M x)) x)
  left_inv f := by
    funext x
    exact (congrArg ((spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x)).symm
      (Pi.lift_comp_π (fun x =>
        (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x) (f x)) x)).trans
          (Equiv.symm_apply_apply _ _)
  right_inv g := by
    apply Pi.hom_ext
    intro x
    change (Pi.lift fun x =>
      (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x)
        (((spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x)).symm
          (g ≫ Pi.π _ x))) ≫ Pi.π _ x = g ≫ Pi.π _ x
    rw [Pi.lift_comp_π]
    exact Equiv.apply_symm_apply _ _

variable (E)

/-- The actual all-spectrum-point inverse image is left adjoint to the
product of the actual skyscraper direct images. -/
def familyAdjunction : stalkFamily (A := A) E ⊣ skyscraperFamily E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := familyHomEquiv
      homEquiv_naturality_left_symm := by
        intro F G M f g
        funext x
        change ((spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x)).symm
          ((f ≫ g) ≫ Pi.π _ x) = (stalk E x).map f ≫
            ((spectrumPoint x).skyscraperSheafAdjunction.homEquiv G (M x)).symm
              (g ≫ Pi.π _ x)
        rw [Category.assoc]
        exact (spectrumPoint x).skyscraperSheafAdjunction.homEquiv_naturality_left_symm
          f (g ≫ Pi.π _ x)
      homEquiv_naturality_right := by
        intro F M N f g
        apply Pi.hom_ext
        intro x
        change (Pi.lift fun x =>
          (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (N x) (f x ≫ g x)) ≫
            Pi.π _ x =
          ((Pi.lift fun x =>
            (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F (M x) (f x)) ≫
              Limits.Pi.map (fun x => (spectrumPoint x).skyscraperSheafFunctor.map (g x))) ≫
                Pi.π _ x
        rw [Pi.lift_comp_π, Category.assoc, Limits.Pi.map_π, ← Category.assoc,
          Pi.lift_comp_π]
        exact (spectrumPoint x).skyscraperSheafAdjunction.homEquiv_naturality_right (f x) (g x) }

/-- The product-of-skyscrapers endofunctor already used by the site Godement
construction, specialized to every actual spectrum point. -/
def zeroFunctor : CoefficientSheaf (A := A) E ⥤ CoefficientSheaf (A := A) E :=
  Langlands.Sheaf.Godement.zeroFunctor (spectrumPoint (K := K) (A := A)) E

/-- Its canonical map is the product of the actual adjunction units. -/
def coaugmentation : 𝟭 (CoefficientSheaf (A := A) E) ⟶ zeroFunctor E :=
  Langlands.Sheaf.Godement.coaugmentation (spectrumPoint (K := K) (A := A)) E

/-- Evaluating the product of point endofunctors gives the direct image of
the actual stalk family. -/
def zeroFamilyIso : zeroFunctor (A := A) E ≅ stalkFamily E ⋙ skyscraperFamily E :=
  NatIso.ofComponents
    (fun F => piObjIso (fun x =>
      Langlands.Sheaf.Godement.pointFunctor (spectrumPoint (K := K) (A := A)) E x) F)
    (by
      intro F G f
      let P := fun x =>
        Langlands.Sheaf.Godement.pointFunctor (spectrumPoint (K := K) (A := A)) E x
      apply Pi.hom_ext
      intro x
      change ((zeroFunctor E).map f ≫ (piObjIso P G).hom) ≫ Pi.π _ x =
        ((piObjIso P F).hom ≫ Limits.Pi.map (fun x => (P x).map f)) ≫ Pi.π _ x
      rw [Category.assoc, piObjIso_hom_comp_π, Category.assoc,
        Limits.Pi.map_π, ← Category.assoc,
        piObjIso_hom_comp_π]
      exact (Pi.π P x).naturality f)

variable {E}

/-- The unit projects to each individual stalk/skyscraper unit. -/
@[reassoc (attr := simp)]
theorem familyAdjunction_unit_π (F : CoefficientSheaf (A := A) E)
    (x : BanachSpectrum A) :
    (familyAdjunction E).unit.app F ≫
      Pi.π (fun x => (spectrumPoint x).skyscraperSheaf ((stalk E x).obj F)) x =
        (spectrumPoint x).skyscraperSheafAdjunction.unit.app F := by
  change (Pi.lift fun x =>
    (spectrumPoint x).skyscraperSheafAdjunction.homEquiv F _ (𝟙 _)) ≫ Pi.π _ x = _
  rw [Pi.lift_comp_π]
  exact (spectrumPoint x).skyscraperSheafAdjunction.homEquiv_id F

/-- The Godement coaugmentation is the unit of the all-point adjunction,
under the product comparison. -/
@[reassoc (attr := simp)]
theorem coaugmentation_zeroFamilyIso :
    coaugmentation (A := A) E ≫ (zeroFamilyIso E).hom = (familyAdjunction E).unit := by
  apply NatTrans.ext
  funext F
  apply Pi.hom_ext
  intro x
  change ((coaugmentation E).app F ≫ (piObjIso (fun x =>
    Langlands.Sheaf.Godement.pointFunctor (spectrumPoint (K := K) (A := A)) E x) F).hom) ≫
      Pi.π _ x = _
  rw [Category.assoc, piObjIso_hom_comp_π]
  exact (NatTrans.congr_app
    (Langlands.Sheaf.Godement.coaugmentation_π (spectrumPoint (K := K) (A := A)) E x) F).trans
      (familyAdjunction_unit_π F x).symm

/-- Projection from degree zero to the actual skyscraper at a spectrum point. -/
def zeroProjection (F : CoefficientSheaf (A := A) E) (x : BanachSpectrum A) :
    (zeroFunctor E).obj F ⟶ (spectrumPoint x).skyscraperSheaf ((stalk E x).obj F) :=
  (Pi.π (fun x =>
    Langlands.Sheaf.Godement.pointFunctor (spectrumPoint (K := K) (A := A)) E x) x).app F

@[reassoc (attr := simp)]
theorem coaugmentation_zeroProjection (F : CoefficientSheaf (A := A) E)
    (x : BanachSpectrum A) :
    (coaugmentation E).app F ≫ zeroProjection F x =
      (spectrumPoint x).skyscraperSheafAdjunction.unit.app F :=
  NatTrans.congr_app
    (Langlands.Sheaf.Godement.coaugmentation_π (spectrumPoint (K := K) (A := A)) E x) F

/-- The component of the Godement unit at an actual chart membership is
precisely the constructed germ map. -/
@[reassoc (attr := simp)]
theorem coaugmentation_germ (F : CoefficientSheaf (A := A) E)
    (x : BanachSpectrum A) (d : RationalChart K A) (hx : x ∈ d.locus) :
    (((coaugmentation E).app F ≫ zeroProjection F x).hom.app (op d)) ≫
      Pi.π (fun _ : (pointFiber x).obj d => (stalk E x).obj F) ⟨⟨hx⟩⟩ =
        germ x d hx F.obj := by
  rw [coaugmentation_zeroProjection,
    ← (spectrumPoint x).skyscraperSheafAdjunction.homEquiv_id F]
  have h := (spectrumPoint x).skyscraperSheafAdjunction_homEquiv_apply_hom
    (F := F) (𝟙 ((stalk E x).obj F))
  exact (congrArg (fun f : F.obj ⟶
      (spectrumPoint x).skyscraperPresheaf ((stalk E x).obj F) =>
        f.app (op d) ≫ Pi.π _ ⟨⟨hx⟩⟩) h).trans (by
          exact ((spectrumPoint x).skyscraperPresheafHomEquiv_app_π
            (P := F.obj) (𝟙 ((stalk E x).obj F)) d ⟨⟨hx⟩⟩).trans (Category.comp_id _))

/-- Each stalk has its own retraction of the stalk of the Godement unit. -/
def stalkRetraction (F : CoefficientSheaf (A := A) E) (x : BanachSpectrum A) :
    (stalk E x).obj ((zeroFunctor E).obj F) ⟶ (stalk E x).obj F :=
  (stalk E x).map (zeroProjection F x) ≫
    (spectrumPoint x).skyscraperSheafAdjunction.counit.app ((stalk E x).obj F)

/-- Stalkwise splitting follows from an individual adjunction triangle;
it does not assume the family conservative. -/
@[reassoc (attr := simp)]
theorem coaugmentation_stalkRetraction (F : CoefficientSheaf (A := A) E)
    (x : BanachSpectrum A) :
    (stalk E x).map ((coaugmentation E).app F) ≫ stalkRetraction F x = 𝟙 _ := by
  rw [stalkRetraction, ← Category.assoc, ← Functor.map_comp,
    coaugmentation_zeroProjection]
  exact (spectrumPoint x).skyscraperSheafAdjunction.left_triangle_components F

variable (E) [Abelian E] [HasSheafify (finiteRationalTopology K A) E]

/-- The actual cochain complex obtained by iterating cokernels of this unit. -/
def complexFunctor :
    CoefficientSheaf (A := A) E ⥤ CochainComplex (CoefficientSheaf (A := A) E) ℕ :=
  Langlands.Sheaf.Godement.complexFunctor (spectrumPoint (K := K) (A := A)) E

/-- The Godement cokernel complex on a sheaf. -/
abbrev complex (F : CoefficientSheaf (A := A) E) :
    CochainComplex (CoefficientSheaf (A := A) E) ℕ :=
  (complexFunctor E).obj F

variable {E}

/-- The original sheaf maps to degree zero by its constructed unit. -/
def augmentation (F : CoefficientSheaf (A := A) E) : F ⟶ (complex E F).X 0 :=
  (coaugmentation E).app F

@[reassoc (attr := simp)]
theorem augmentation_d (F : CoefficientSheaf (A := A) E) :
    augmentation F ≫ (complex E F).d 0 1 = 0 :=
  Langlands.Sheaf.Godement.augmentation_d (spectrumPoint (K := K) (A := A)) E F

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.Godement
