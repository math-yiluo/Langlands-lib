import Langlands.Shimura.Unitary.DeligneSchemeSplitting
import Langlands.Shimura.Unitary.HarrisDeligneGroupScheme

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.DeligneTorus

/-- Select the first or second factor of a product of scalar unit groups. -/
def factorUnits (first : Bool) (S : Type) [CommRing S] : Sˣ →* Sˣ × Sˣ :=
  if first then (MonoidHom.id _).prod 1 else (1 : Sˣ →* Sˣ).prod (MonoidHom.id _)

theorem factorUnits_natural (first : Bool) {S T : Type} [CommRing S] [CommRing T]
    (f : S →+* T) (z : Sˣ) :
    factorUnits first T (Units.map f.toMonoidHom z) =
      Prod.map (Units.map f.toMonoidHom) (Units.map f.toMonoidHom)
        (factorUnits first S z) := by
  cases first <;> simp [factorUnits]

private theorem factor_naturality (first : Bool)
    {T T' : Over (Spec (CommRingCat.of ℂ))} (a : T' ⟶ T)
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    (complexSplitPointsEquiv T').symm
        (factorUnits first Γ(T'.left, ⊤)
          (GroupScheme.Gm.pointsEquiv _ T' (a ≫ x))) =
      a ≫ (complexSplitPointsEquiv T).symm
        (factorUnits first Γ(T.left, ⊤) (GroupScheme.Gm.pointsEquiv _ T x)) := by
  apply (complexSplitPointsEquiv T').injective
  rw [MulEquiv.apply_symm_apply, complexSplitPointsEquiv_naturality,
    MulEquiv.apply_symm_apply, GroupScheme.Gm.pointsEquiv_naturality,
    factorUnits_natural]

/-- The actual cocharacter of the complex Deligne group in the selected split factor. -/
def factorCocharacter (first : Bool) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ complexGroupScheme :=
  GroupScheme.homOfPoints (fun T =>
    (complexSplitPointsEquiv T).symm.toMonoidHom.comp
      ((factorUnits first Γ(T.left, ⊤)).comp (GroupScheme.Gm.pointsEquiv _ T).toMonoidHom))
    (factor_naturality first)

/-- The cocharacter is the selected factor inclusion on every complex test scheme. -/
theorem factorCocharacter_points (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    complexSplitPointsEquiv T (x ≫ (factorCocharacter first).hom.hom) =
      factorUnits first Γ(T.left, ⊤) (GroupScheme.Gm.pointsEquiv _ T x) := by
  have key : x ≫ (factorCocharacter first).hom.hom = _ :=
    GroupScheme.comp_homOfPoints _ (factor_naturality first) T x
  rw [key]
  exact (complexSplitPointsEquiv T).apply_symm_apply _

/-- Under the published scheme splitting this is precisely the same factor inclusion. -/
theorem factorCocharacter_splitting (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    splitSchemePointsEquiv T
      (x ≫ (factorCocharacter first ≫ complexSplitting.hom).hom.hom) =
        factorUnits first Γ(T.left, ⊤) (GroupScheme.Gm.pointsEquiv _ T x) := by
  rw [Grp.comp_hom_hom, ← Category.assoc, complexSplitting_hom_points,
    factorCocharacter_points]

local instance complexSections (T : Over (Spec (CommRingCat.of ℂ))) :
    Algebra ℂ Γ(T.left, ⊤) := ((algΓ (CommRingCat.of ℂ)).obj T).unop.algebra

/-- The underlying quadratic unit is obtained by the explicit inverse root-evaluation map. -/
theorem factorCocharacter_quadratic (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    complexPointsEquiv T (x ≫ (factorCocharacter first).hom.hom) =
      (splitPointsEquiv Γ(T.left, ⊤)).symm
        (factorUnits first Γ(T.left, ⊤) (GroupScheme.Gm.pointsEquiv _ T x)) := by
  apply (splitPointsEquiv Γ(T.left, ⊤)).injective
  rw [MulEquiv.apply_symm_apply]
  exact factorCocharacter_points first T x

/-- Restricting the Deligne norm to either factor is the identity character. -/
theorem factorCocharacter_norm (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    norm Γ(T.left, ⊤) (complexPointsEquiv T (x ≫ (factorCocharacter first).hom.hom)) =
      GroupScheme.Gm.pointsEquiv _ T x := by
  rw [splitPointsEquiv_norm, factorCocharacter_quadratic, MulEquiv.apply_symm_apply]
  cases first <;> simp [factorUnits]

variable {G H : GroupScheme (Spec (CommRingCat.of ℝ))}

/-- Complex scalar extension of a given real Deligne homomorphism. -/
def complexMapOf (h : groupScheme ⟶ G) :
    complexGroupScheme ⟶ (Over.pullback complexBaseMap).mapGrp.obj G :=
  (Over.pullback complexBaseMap).mapGrp.map h

/-- The complex cocharacter associated to a real Deligne map and a selected source factor. -/
def cocharacterOf (h : groupScheme ⟶ G) (first : Bool) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      (Over.pullback complexBaseMap).mapGrp.obj G :=
  factorCocharacter first ≫ complexMapOf h

/-- The associated cocharacter is evaluated by the actual pullback point adjunction. -/
theorem cocharacterOf_points (h : groupScheme ⟶ G) (first : Bool)
    (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    GroupScheme.baseChangePointsEquiv complexBaseMap G T
        (x ≫ (cocharacterOf h first).hom.hom) =
      GroupScheme.baseChangePointsEquiv complexBaseMap groupScheme T
        (x ≫ (factorCocharacter first).hom.hom) ≫ h.hom.hom := by
  rw [cocharacterOf, Grp.comp_hom_hom, ← Category.assoc]
  exact GroupScheme.baseChangePointsEquiv_comp complexBaseMap h T _

/-- A comparison of real target group schemes carries the associated cocharacter along it. -/
theorem cocharacterOf_comp (h : groupScheme ⟶ G) (f : G ⟶ H) (first : Bool) :
    cocharacterOf (h ≫ f) first =
      cocharacterOf h first ≫ (Over.pullback complexBaseMap).mapGrp.map f := by
  simp only [cocharacterOf, complexMapOf, Functor.map_comp, Category.assoc]

end Langlands.Shimura.DeligneTorus

namespace Langlands.Shimura.AlgebraInvolution

variable {A : Type} [Ring A] [Algebra ℝ A]
  {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ A) (σ : AlgebraInvolution ℝ A)

/-- Global sections of a complex test scheme, regarded as a real algebra via its structure map. -/
abbrev complexTestAlgebra (T : Over (Spec (CommRingCat.of ℂ))) : CommAlgCat ℝ :=
  ((algΓ (CommRingCat.of ℝ)).obj ((Over.map DeligneTorus.complexBaseMap).obj T)).unop

/-- Actual complex-pullback points are similitudes in the scalar-extended real algebra. -/
def complexSimilitudePointsEquiv (T : Over (Spec (CommRingCat.of ℂ))) :
    (T ⟶ ((Over.pullback DeligneTorus.complexBaseMap).mapGrp.obj
      (σ.similitudeGroupScheme b)).X) ≃*
        (σ.baseChange (complexTestAlgebra T)).similitudes :=
  (GroupScheme.baseChangePointsEquiv DeligneTorus.complexBaseMap
    (σ.similitudeGroupScheme b) T).trans
      (GroupScheme.Corepresented.pointsEquiv (R := CommRingCat.of ℝ) σ.similitudeFunctor
        (σ.similitudeCorepresentableBy b) ((Over.map DeligneTorus.complexBaseMap).obj T))

namespace ComplexHom

variable {σ} (h : ComplexHom σ)

set_option backward.isDefEq.respectTransparency false in
/-- On every complex test scheme the cocharacter is scalar extension at the selected quadratic unit. -/
theorem cocharacter_points (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    complexSimilitudePointsEquiv b σ T
        (x ≫ (DeligneTorus.cocharacterOf (h.deligneGroupSchemeMap b) first).hom.hom) =
      h.delignePoints (complexTestAlgebra T)
        (DeligneTorus.complexPointsEquiv T
          (x ≫ (DeligneTorus.factorCocharacter first).hom.hom)) := by
  unfold complexSimilitudePointsEquiv
  rw [MulEquiv.trans_apply, DeligneTorus.cocharacterOf_points]
  exact GroupScheme.Corepresented.groupSchemeMap_points (R := CommRingCat.of ℝ)
    DeligneTorus.corepresentableBy (σ.similitudeCorepresentableBy b) h.deligneHom _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-convention cocharacter evaluates the same scalar extension at the inverse unit. -/
theorem inverseCocharacter_points (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    complexSimilitudePointsEquiv b σ T
        (x ≫ (DeligneTorus.cocharacterOf (h.inverseDeligneGroupSchemeMap b) first).hom.hom) =
      h.delignePoints (complexTestAlgebra T)
        (DeligneTorus.complexPointsEquiv T
          (x ≫ (DeligneTorus.factorCocharacter first).hom.hom))⁻¹ := by
  unfold complexSimilitudePointsEquiv
  rw [MulEquiv.trans_apply, DeligneTorus.cocharacterOf_points]
  exact GroupScheme.Corepresented.groupSchemeMap_points (R := CommRingCat.of ℝ)
    DeligneTorus.corepresentableBy (σ.similitudeCorepresentableBy b) h.inverseDeligneHom _

/-- The direct cocharacter has multiplier equal to the original scalar unit. -/
theorem cocharacter_multiplier (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    (σ.baseChange (complexTestAlgebra T)).multiplier
      (complexSimilitudePointsEquiv b σ T
        (x ≫ (DeligneTorus.cocharacterOf (h.deligneGroupSchemeMap b) first).hom.hom)) =
      GroupScheme.Gm.pointsEquiv _ T x := by
  rw [h.cocharacter_points]
  exact DeligneTorus.factorCocharacter_norm first T x

/-- The inverse-convention cocharacter has inverse multiplier. -/
theorem inverseCocharacter_multiplier (first : Bool) (T : Over (Spec (CommRingCat.of ℂ)))
    (x : T ⟶ (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).X) :
    (σ.baseChange (complexTestAlgebra T)).multiplier
      (complexSimilitudePointsEquiv b σ T
        (x ≫ (DeligneTorus.cocharacterOf (h.inverseDeligneGroupSchemeMap b) first).hom.hom)) =
      (GroupScheme.Gm.pointsEquiv _ T x)⁻¹ := by
  rw [h.inverseCocharacter_points]
  change DeligneTorus.norm Γ(T.left, ⊤)
    (DeligneTorus.complexPointsEquiv T
      (x ≫ (DeligneTorus.factorCocharacter first).hom.hom))⁻¹ = _
  rw [map_inv]
  exact congrArg Inv.inv (DeligneTorus.factorCocharacter_norm first T x)

end ComplexHom
end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual iterated complex pullback of the rational CM similitude group. -/
abbrev complexRationalGroupScheme :=
  (Over.pullback DeligneTorus.complexBaseMap).mapGrp.obj
    (D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ))

/-- The complex cocharacter of the corrected Harris map in either source factor. -/
def harrisCocharacter (first : Bool) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme :=
  DeligneTorus.cocharacterOf (D.harrisDeligneMap C) first

/-- Kottwitz's convention retains conjugation before inversion in the original real map. -/
def kottwitzCocharacter (first : Bool) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme :=
  DeligneTorus.cocharacterOf (D.kottwitzDeligneMap C) first

/-- The Harris cocharacter agrees with the one obtained from the actual real algebra model. -/
theorem harrisCocharacter_comparison (first : Bool) :
    D.harrisCocharacter C first ≫
        (Over.pullback DeligneTorus.complexBaseMap).mapGrp.map D.realGroupSchemeIso.hom =
      DeligneTorus.cocharacterOf
        ((D.realComplexHom C).deligneGroupSchemeMap (D.rationalBasis.baseChange ℝ)) first := by
  rw [harrisCocharacter, ← DeligneTorus.cocharacterOf_comp, D.harrisDeligneMap_comparison]

/-- The Kottwitz cocharacter agrees with the inverse map of the conjugate homomorphism. -/
theorem kottwitzCocharacter_comparison (first : Bool) :
    D.kottwitzCocharacter C first ≫
        (Over.pullback DeligneTorus.complexBaseMap).mapGrp.map D.realGroupSchemeIso.hom =
      DeligneTorus.cocharacterOf
        ((D.realComplexHom C).conj.inverseDeligneGroupSchemeMap
          (D.rationalBasis.baseChange ℝ)) first := by
  rw [kottwitzCocharacter, ← DeligneTorus.cocharacterOf_comp,
    D.kottwitzDeligneMap_comparison]

/-- Signature and CM-section hypotheses construct the first Harris cocharacter. -/
def harrisCocharacterOfSignature (h : HasHarrisSignature D.toSecondKindInvolution n)
    (hΦ : IsCMSection E K Φ) :
    (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶ D.complexRationalGroupScheme :=
  D.harrisCocharacter (HarrisSignatureCharts.ofSignature h hΦ) true

end Langlands.Shimura.CentralSimpleUnitaryData
