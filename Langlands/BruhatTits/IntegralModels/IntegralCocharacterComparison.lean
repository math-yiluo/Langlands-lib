import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellProof
import Langlands.BruhatTits.IntegralModels.FacetRootSignBaseChange
import Langlands.BruhatTits.IntegralModels.FacetRootDatum
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerResidueRoots
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.TwistCoefficientComparison
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # Integral cocharacters under a change of coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

/-- Normalized cocharacter base change commutes with a commuting square. -/
theorem baseChangeCocharacter_square {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) {G : GroupScheme B}
    (χ : (Gm B).toGrp ⟶ G) :
    baseChangeCocharacter c (baseChangeCocharacter b χ) ≫
        (Descent.squareComparison b c d e h G).hom =
      baseChangeCocharacter e (baseChangeCocharacter d χ) := by
  apply (cancel_mono (Descent.pullbackComparison d e (e ≫ d) rfl G).hom).mp
  simp only [Descent.squareComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [baseChangeCocharacter_tower, baseChangeCocharacter_tower]

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K G)

/-- An ambient integral cocharacter is determined by its prescribed generic fibre. -/
theorem cocharacterHom_eq_of_generic
    {χ ψ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ N.group}
    (h : Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ ≫ N.genericIso.hom =
      Dynamic.baseChangeCocharacter (Spec.algebraMap R K) ψ ≫ N.genericIso.hom) :
    χ = ψ := by
  let : Smooth (Gm (Spec (CommRingCat.of R))).X.hom := smooth_gm _
  have h₁ := (cancel_mono N.genericIso.hom).mp h
  have h₂ := (cancel_epi (Gm.baseChangeIso (Spec.algebraMap R K)).inv).mp h₁
  apply Grp.hom_ext
  exact Langlands.AbelianScheme.genericFibre_map_injective K
    (congrArg (fun f => f.hom.hom) h₂)

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

section ResidueSquare

variable {A : Type u} [CommRing A] [IsLocalRing R] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]

omit [IsDomain R] in
/-- Normalized cocharacters commute with the actual special-fibre square. -/
theorem baseChangeCocharacter_specialFibreSquare
    (N : GroupScheme (Spec (CommRingCat.of R)))
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ N) :
    Dynamic.baseChangeCocharacter
        (algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
        (Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap R) χ) ≫
        (specialFibreSquareIso A N).hom =
      Dynamic.baseChangeCocharacter (IntegralModel.residueBaseMap A)
        (Dynamic.baseChangeCocharacter (Spec.algebraMap R A) χ) := by
  apply (cancel_mono (Descent.pullbackComparison (Spec.algebraMap R A)
    (IntegralModel.residueBaseMap A)
    (algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) ≫
      IntegralModel.residueBaseMap R)
    (residueExtension_comp_residueBaseMap A).symm N).hom).mp
  simp only [specialFibreSquareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [Dynamic.baseChangeCocharacter_tower, Dynamic.baseChangeCocharacter_tower]

end ResidueSquare

namespace IntegralTorusData

/-- The generic cocharacter obtained from an actual integral torus cocharacter. -/
def genericCocharacter (T : IntegralTorusData D S i) (ν : cocharacterLattice T.torus) :
    cocharacterLattice S :=
  cocharacterLattice.baseChange (Spec.algebraMap R K) T.torus ν ≫
    (CommGroupScheme.isoOfGroupIso T.genericIso).hom

/-- The ambient integral cocharacter has the expected generic fibre. -/
theorem generic_ambientCocharacter (T : IntegralTorusData D S i)
    (ν : cocharacterLattice T.torus) :
    Dynamic.baseChangeCocharacter (Spec.algebraMap R K)
        (CommGroupScheme.groupHom ν ≫ T.inclusion) ≫ D.neutral.genericIso.hom =
      CommGroupScheme.groupHom (T.genericCocharacter ν) ≫ i := by
  rw [Dynamic.baseChangeCocharacter_comp_hom, Category.assoc, T.generic_comm,
    ← Category.assoc]
  rfl

variable (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {S' : CommGroupScheme (Spec (CommRingCat.of L))}
  {i' : S'.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}

/-- The integral ambient cocharacter in the upstairs split torus is the actual
coefficient base change of the downstairs ambient integral cocharacter. -/
theorem baseChange_ambientCocharacter (T : IntegralTorusData D S i)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i)
    (ν : cocharacterLattice T.torus) :
    Dynamic.baseChangeCocharacter (Spec.algebraMap R A)
        (CommGroupScheme.groupHom ν ≫ T.inclusion) =
      OrderedIntegralOpenCell.integralCocharacterHom T'
        (cocharacterLattice.baseChange (Spec.algebraMap K L) S
          (T.genericCocharacter ν) ≫ Additive.ofMul f) := by
  apply IntegralModel.cocharacterHom_eq_of_generic (D.baseChange A L).neutral
  rw [OrderedIntegralOpenCell.baseChange_integralCocharacterHom]
  change Dynamic.baseChangeCocharacter (Spec.algebraMap A L)
      (Dynamic.baseChangeCocharacter (Spec.algebraMap R A)
        (CommGroupScheme.groupHom ν ≫ T.inclusion)) ≫
      (D.neutral.baseChangeGenericIso A L).hom = _
  rw [IntegralModel.baseChangeGenericIso_eq_square]
  simp only [IntegralModel.baseChangeSquareIso, Iso.trans_hom,
    Functor.mapIso_hom, ← Category.assoc]
  rw [Dynamic.baseChangeCocharacter_square]
  rw [← Dynamic.baseChangeCocharacter_comp_hom, T.generic_ambientCocharacter,
    Dynamic.baseChangeCocharacter_comp_hom]
  change (CommGroupScheme.groupHom
      (cocharacterLattice.baseChange (Spec.algebraMap K L) S (T.genericCocharacter ν))) ≫
      (GroupScheme.baseChange (Spec.algebraMap K L)).map i = _
  rw [← hf, ← Category.assoc]
  rfl

section Residue

variable [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

local notation "resExt" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

/-- The specialized upstairs ambient cocharacter is the residue-field base
change of the reduction of the downstairs integral cocharacter. -/
theorem baseChange_specializedAmbientCocharacter (T : IntegralTorusData D S i)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i)
    (ν : cocharacterLattice T.torus) :
    Dynamic.baseChangeCocharacter resExt
        (CommGroupScheme.groupHom
          (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) T.torus ν) ≫
          T.specialFibreInclusion) ≫
        (specialFibreSquareIso A D.neutral.group).hom =
      CommGroupScheme.groupHom
          (T'.cocharacterSpecialization
            (cocharacterLattice.baseChange (Spec.algebraMap K L) S
              (T.genericCocharacter ν) ≫ Additive.ofMul f)) ≫
        T'.specialFibreInclusion := by
  rw [cocharacterLattice.groupHom_baseChange_dynamic, specialFibreInclusion,
    ← Dynamic.baseChangeCocharacter_comp_hom, baseChangeCocharacter_specialFibreSquare,
    T.baseChange_ambientCocharacter A L T' f hf]
  rw [OrderedIntegralOpenCell.integralCocharacterHom,
    Dynamic.baseChangeCocharacter_comp_hom]
  rfl

/-- Compatibility of the two canonical specializations, as actual ambient
cocharacters, for every generic cocharacter of the downstairs split torus. -/
def HasCoefficientCompatibleSpecialization (T : IntegralTorusData D S i)
    (hT : IsSplitTorus T.torus.toGrp)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp) :
    Prop :=
  ∀ c : cocharacterLattice S,
    Dynamic.baseChangeCocharacter resExt
        (CommGroupScheme.groupHom (T.cocharacterSpecialization hT c) ≫
          T.specialFibreInclusion) ≫
        (specialFibreSquareIso A D.neutral.group).hom =
      CommGroupScheme.groupHom
          (T'.cocharacterSpecialization
            (cocharacterLattice.baseChange (Spec.algebraMap K L) S c ≫ Additive.ofMul f)) ≫
        T'.specialFibreInclusion

/-- Canonical specialization is compatible with the coefficient square. -/
theorem coefficientCompatibleSpecialization (T : IntegralTorusData D S i)
    (hT : IsSplitTorus T.torus.toGrp)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i) :
    T.HasCoefficientCompatibleSpecialization A L hT T' f := by
  intro c
  obtain ⟨ν, rfl⟩ := (T.genericCocharacterEquiv hT).surjective c
  have h := T.baseChange_specializedAmbientCocharacter A L T' f hf ν
  change Dynamic.baseChangeCocharacter resExt
      (CommGroupScheme.groupHom (T.cocharacterSpecialization hT
        (T.genericCocharacterEquiv hT ν)) ≫ T.specialFibreInclusion) ≫
      (specialFibreSquareIso A D.neutral.group).hom = _
  rw [cocharacterSpecialization, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact h

/-- Projection to the actual reductive quotient cancels the special-fibre
square and identifies the two quotient cocharacters literally. -/
theorem baseChange_quotientCocharacter (T : IntegralTorusData D S i)
    (hT : IsSplitTorus T.torus.toGrp)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i)
    (Q : SpecialFibreQuotientData D) (c : cocharacterLattice S) :
    (CommGroupScheme.groupHom
        (T'.cocharacterSpecialization
          (cocharacterLattice.baseChange (Spec.algebraMap K L) S c ≫ Additive.ofMul f)) ≫
      T'.specialFibreInclusion) ≫ (Q.baseChange A L).projection =
    Dynamic.baseChangeCocharacter resExt
      ((CommGroupScheme.groupHom (T.cocharacterSpecialization hT c) ≫
        T.specialFibreInclusion) ≫ Q.projection) := by
  rw [← T.coefficientCompatibleSpecialization A L hT T' f hf c]
  simp only [SpecialFibreQuotientData.baseChange_projection, Category.assoc,
    Iso.hom_inv_id_assoc, Dynamic.baseChangeCocharacter_comp_hom, Functor.map_comp]

/-- The upstairs dynamic parabolic is exactly the residue-field base change
of the dynamic parabolic of the downstairs quotient cocharacter. -/
theorem baseChange_quotientParabolic (T : IntegralTorusData D S i)
    (hT : IsSplitTorus T.torus.toGrp)
    (T' : IntegralSplitTorusData (D.baseChange A L).neutral i')
    (f : ((CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S).toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i)
    (Q : SpecialFibreQuotientData D) (c : cocharacterLattice S) :
    Dynamic.parabolic
        ((CommGroupScheme.groupHom
            (T'.cocharacterSpecialization
              (cocharacterLattice.baseChange (Spec.algebraMap K L) S c ≫
                Additive.ofMul f)) ≫ T'.specialFibreInclusion) ≫
          (Q.baseChange A L).projection) =
      (Dynamic.parabolic
        ((CommGroupScheme.groupHom (T.cocharacterSpecialization hT c) ≫
          T.specialFibreInclusion) ≫ Q.projection)).baseChange resExt := by
  rw [T.baseChange_quotientCocharacter A L hT T' f hf Q c,
    Dynamic.parabolic_baseChange]

end Residue

end IntegralTorusData

end Langlands.BruhatTits.IntegralModels
