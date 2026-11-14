import Langlands.Sheaf.Equivariant.NaturalActionInverseImage
import Langlands.Sheaf.Equivariant.AnalyticInvariantSheaf
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology

/-!
# The inverse image `b^*` along `b : X → X(G)`

Let `X` be a `G`-space. The presheaf of invariant sections `F ↦ (V(G) ↦ F(V)^G)` from module
sheaves on the twisted quasi-étale site of `X` to module presheaves on `Qét(X(G))` has a left
adjoint, the inverse image. On presheaves it is a left Kan extension, and its value at `U`
is a colimit of the values `E(V(G))` over the twisted arrows `U → V`. At an object `U` of
`X_qét` this is the colimit over the untwisted arrows `U → V` over `X`, which is Berkovich's
formula (§1.2). Under the image pullback hypothesis the left adjoint restricts to sheaves on
`X(G)_qét`, with right adjoint the sheaf `(b_*F)^G`. The same holds for `X(G)_ét`.

Modules are taken in the universe `max u (v + 1) z uL`, which contains the comma categories
of the colimits and allows sheafification on the twisted sites.

That `b^*E` is a `G`-sheaf, and Berkovich's Theorem 1.4.2, are not proved here.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Sheaf (HasImagePullbacks)

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)
variable (R : Type (max u (v + 1) z uL)) [CommRing R]

section QuasiEtale

/-- Module presheaves on `Qét(X(G)) × G` have pointwise left Kan extensions along the
inflation of the action: the comma categories are small. -/
theorem quasiEtaleInflation_hasPointwiseLeftKanExtension
    (F : (EquivariantQuasiEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤
      ModuleCat.{max u (v + 1) z uL} R) :
    (quasiEtaleNaturalAction X).inflation.op.HasPointwiseLeftKanExtension F := fun U =>
  haveI : Small.{max u (v + 1) z uL}
      (CostructuredArrow (quasiEtaleNaturalAction X).inflation.op U) :=
    small_lift.{max u (v + 1) z, uL, max u (v + 1) z} _
  haveI : HasColimitsOfShape (CostructuredArrow (quasiEtaleNaturalAction X).inflation.op U)
      AddCommGrpCat.{max u (v + 1) z uL} := AddCommGrpCat.hasColimitsOfShape
  (ModuleCat.hasColimitsOfShape (J := _) (R := R)).has_colimit _

/-- Module presheaves on `Qét(X(G)) × G` have left Kan extensions along the inflation. -/
theorem quasiEtaleInflation_hasLeftKanExtension
    (F : (EquivariantQuasiEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤
      ModuleCat.{max u (v + 1) z uL} R) :
    (quasiEtaleNaturalAction X).inflation.op.HasLeftKanExtension F :=
  haveI := quasiEtaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R F
  Functor.HasLeftKanExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit _ F)

/-- The inverse image of module presheaves on `Qét(X(G))` to module presheaves on the twisted
quasi-étale site of `X`. -/
def quasiEtaleInverseImagePresheaf :
    ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) ⥤
      ((TwistedOver (quasiEtale (K := K)) X.obj.ρAut)ᵒᵖ ⥤
        ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  (quasiEtaleNaturalAction X).inverseImagePresheafFunctor R

/-- The inverse image presheaf is left adjoint to the presheaf of invariant sections. -/
def quasiEtaleInverseImagePresheafAdjunction :
    quasiEtaleInverseImagePresheaf.{u, v, uL, z} X R ⊣
      (quasiEtaleNaturalAction X).invariantFunctor R := by
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  exact (quasiEtaleNaturalAction X).inverseImagePresheafAdjunction R

/-- The value at `U` of the inverse image presheaf of `E` is the colimit of the values
`E(V(G))` over the comma category of twisted arrows `U → V` along the inflation. -/
def quasiEtaleInverseImagePresheafObjIsoColimit
    (E : (EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : TwistedOver (quasiEtale (K := K)) X.obj.ρAut) :
    haveI := quasiEtaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R
      ((CategoryTheory.Prod.fst (EquivariantQuasiEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E)
    ((quasiEtaleInverseImagePresheaf.{u, v, uL, z} X R).obj E).obj (op U) ≅
      colimit (CostructuredArrow.proj (quasiEtaleNaturalAction X).inflation.op (op U) ⋙
        (CategoryTheory.Prod.fst (EquivariantQuasiEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E) :=
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := quasiEtaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R
    ((CategoryTheory.Prod.fst (EquivariantQuasiEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E)
  (quasiEtaleNaturalAction X).inverseImagePresheafObjIsoColimit R E U

/-- Module presheaves on `Qét(X(G))` have colimits over the comma categories of arrows
`U → V` in `X_qét`. -/
theorem quasiEtaleUntwisted_hasColimit
    (E : (EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : QuasiEtaleSite (GSpace.forget.obj X)) :
    HasColimit (CostructuredArrow.proj (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).op (op U) ⋙
      E) :=
  haveI : Small.{max u (v + 1) z uL}
      (CostructuredArrow (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).op (op U)) :=
    small_lift.{max u (v + 1) z, uL, max u (v + 1) z} _
  haveI : HasColimitsOfShape
      (CostructuredArrow (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).op (op U))
      AddCommGrpCat.{max u (v + 1) z uL} := AddCommGrpCat.hasColimitsOfShape
  (ModuleCat.hasColimitsOfShape (J := _) (R := R)).has_colimit _

/-- Berkovich's formula for the inverse image: at an object `U` of `X_qét`, the inverse image
presheaf of `E` is the colimit of the values `E(V(G))` over the category `C(U/X(G))` of the
pairs of an object `V(G)` of `Qét(X(G))` and an arrow `U → V` over `X`. -/
def quasiEtaleInverseImagePresheafObjIsoUntwistedColimit
    (E : (EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : QuasiEtaleSite (GSpace.forget.obj X)) :
    haveI := quasiEtaleUntwisted_hasColimit.{u, v, uL, z} X R E U
    ((quasiEtaleInverseImagePresheaf.{u, v, uL, z} X R).obj E).obj
        (op ((TwistedOver.ι (quasiEtale (K := K)) X.obj.ρAut).obj U)) ≅
      colimit (CostructuredArrow.proj (EquivariantQuasiEtaleSite.toQuasiEtaleSite X).op (op U) ⋙
        E) :=
  haveI : ∀ F : (EquivariantQuasiEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤
      ModuleCat.{max u (v + 1) z uL} R,
      (NaturalAction.inflation (Φ := EquivariantQuasiEtaleSite.toQuasiEtaleSite X ⋙
        TwistedOver.ι (quasiEtale (K := K)) X.obj.ρAut)
        (quasiEtaleNaturalAction X)).op.HasLeftKanExtension F :=
    quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI : (NaturalAction.inflation
      (Φ := EquivariantQuasiEtaleSite.toQuasiEtaleSite X ⋙
        TwistedOver.ι (quasiEtale (K := K)) X.obj.ρAut)
      (quasiEtaleNaturalAction X)).op.HasPointwiseLeftKanExtension
        ((CategoryTheory.Prod.fst (EquivariantQuasiEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E) :=
    quasiEtaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R _
  haveI := quasiEtaleUntwisted_hasColimit.{u, v, uL, z} X R E U
  (quasiEtaleNaturalAction X).inverseImagePresheafObjIsoUntwistedColimit
    (Ψ := EquivariantQuasiEtaleSite.toQuasiEtaleSite X) (fun _ _ => rfl) R E U

/-- Module sheaves on the twisted quasi-étale site have sheafification in the universe
`max u (v + 1) z uL`. -/
theorem twistedQuasiEtale_hasSheafify_inverseImage :
    HasSheafify (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI : Small.{max u (v + 1) z uL} G := small_lift.{z, max u (v + 1) uL, z} G
  twistedQuasiEtale_hasSheafify.{u, v, max z uL} X.obj.V X.obj.ρAut R

/-- Berkovich's inverse image `b^*` of module presheaves on `Qét(X(G))` to module sheaves on
the twisted quasi-étale site: the sheafification of the inverse image presheaf. -/
def quasiEtaleInverseImage :
    ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) ⥤
      Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedQuasiEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  (quasiEtaleNaturalAction X).inverseImageFunctor R (twistedQuasiEtaleTopology X.obj.ρAut)

/-- The inverse image is left adjoint to the presheaf of invariant sections
`F ↦ (V(G) ↦ F(V)^G)`. -/
def quasiEtaleInverseImageAdjunction :
    quasiEtaleInverseImage.{u, v, uL, z} X R ⊣ quasiEtaleInvariantPresheaf X R := by
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedQuasiEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  exact (quasiEtaleNaturalAction X).inverseImageAdjunction R
    (twistedQuasiEtaleTopology X.obj.ρAut)

/-- Berkovich's inverse image `b^*` of module sheaves on `X(G)_qét` to module sheaves on the
twisted quasi-étale site, assuming image pullbacks. -/
def quasiEtaleSheafInverseImage
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    Sheaf (equivariantQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R) ⥤
      Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedQuasiEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  haveI := quasiEtaleToTwisted_isContinuous X hX
  (quasiEtaleNaturalAction X).sheafInverseImageFunctor R
    (twistedQuasiEtaleTopology X.obj.ρAut) (equivariantQuasiEtaleTopology X)

/-- Assuming image pullbacks, the inverse image of sheaves is left adjoint to the sheaf
`(b_*F)^G` of invariant sections. -/
def quasiEtaleSheafInverseImageAdjunction
    (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)) :
    quasiEtaleSheafInverseImage.{u, v, uL, z} X R hX ⊣ quasiEtaleInvariantSheaf X R hX := by
  haveI := quasiEtaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedQuasiEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  haveI := quasiEtaleToTwisted_isContinuous X hX
  exact (quasiEtaleNaturalAction X).sheafInverseImageAdjunction R
    (twistedQuasiEtaleTopology X.obj.ρAut) (equivariantQuasiEtaleTopology X)

end QuasiEtale

section Etale

/-- Module presheaves on `Ét(X(G)) × G` have pointwise left Kan extensions along the
inflation of the action: the comma categories are small. -/
theorem etaleInflation_hasPointwiseLeftKanExtension
    (F : (EquivariantEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) :
    (etaleNaturalAction X).inflation.op.HasPointwiseLeftKanExtension F := fun U =>
  haveI : Small.{max u (v + 1) z uL}
      (CostructuredArrow (etaleNaturalAction X).inflation.op U) :=
    small_lift.{max u (v + 1) z, uL, max u (v + 1) z} _
  haveI : HasColimitsOfShape (CostructuredArrow (etaleNaturalAction X).inflation.op U)
      AddCommGrpCat.{max u (v + 1) z uL} := AddCommGrpCat.hasColimitsOfShape
  (ModuleCat.hasColimitsOfShape (J := _) (R := R)).has_colimit _

/-- Module presheaves on `Ét(X(G)) × G` have left Kan extensions along the inflation. -/
theorem etaleInflation_hasLeftKanExtension
    (F : (EquivariantEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) :
    (etaleNaturalAction X).inflation.op.HasLeftKanExtension F :=
  haveI := etaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R F
  Functor.HasLeftKanExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit _ F)

/-- The inverse image of module presheaves on `Ét(X(G))` to module presheaves on the twisted
étale site of `X`. -/
def etaleInverseImagePresheaf :
    ((EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) ⥤
      ((TwistedOver (etale (K := K)) X.obj.ρAut)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  (etaleNaturalAction X).inverseImagePresheafFunctor R

/-- The inverse image presheaf is left adjoint to the presheaf of invariant sections. -/
def etaleInverseImagePresheafAdjunction :
    etaleInverseImagePresheaf.{u, v, uL, z} X R ⊣ (etaleNaturalAction X).invariantFunctor R := by
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  exact (etaleNaturalAction X).inverseImagePresheafAdjunction R

/-- The value at `U` of the inverse image presheaf of `E` is the colimit of the values
`E(V(G))` over the comma category of twisted arrows `U → V` along the inflation. -/
def etaleInverseImagePresheafObjIsoColimit
    (E : (EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : TwistedOver (etale (K := K)) X.obj.ρAut) :
    haveI := etaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R
      ((CategoryTheory.Prod.fst (EquivariantEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E)
    ((etaleInverseImagePresheaf.{u, v, uL, z} X R).obj E).obj (op U) ≅
      colimit (CostructuredArrow.proj (etaleNaturalAction X).inflation.op (op U) ⋙
        (CategoryTheory.Prod.fst (EquivariantEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E) :=
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := etaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R
    ((CategoryTheory.Prod.fst (EquivariantEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E)
  (etaleNaturalAction X).inverseImagePresheafObjIsoColimit R E U

/-- Module presheaves on `Ét(X(G))` have colimits over the comma categories of arrows
`U → V` in `X_ét`. -/
theorem etaleUntwisted_hasColimit
    (E : (EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : EtaleSite (GSpace.forget.obj X)) :
    HasColimit (CostructuredArrow.proj (EquivariantEtaleSite.toEtaleSite X).op (op U) ⋙ E) :=
  haveI : Small.{max u (v + 1) z uL}
      (CostructuredArrow (EquivariantEtaleSite.toEtaleSite X).op (op U)) :=
    small_lift.{max u (v + 1) z, uL, max u (v + 1) z} _
  haveI : HasColimitsOfShape (CostructuredArrow (EquivariantEtaleSite.toEtaleSite X).op (op U))
      AddCommGrpCat.{max u (v + 1) z uL} := AddCommGrpCat.hasColimitsOfShape
  (ModuleCat.hasColimitsOfShape (J := _) (R := R)).has_colimit _

/-- Berkovich's formula for the inverse image: at an object `U` of `X_ét`, the inverse image
presheaf of `E` is the colimit of the values `E(V(G))` over the category of the pairs of an
object `V(G)` of `Ét(X(G))` and an arrow `U → V` over `X`. -/
def etaleInverseImagePresheafObjIsoUntwistedColimit
    (E : (EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R)
    (U : EtaleSite (GSpace.forget.obj X)) :
    haveI := etaleUntwisted_hasColimit.{u, v, uL, z} X R E U
    ((etaleInverseImagePresheaf.{u, v, uL, z} X R).obj E).obj
        (op ((TwistedOver.ι (etale (K := K)) X.obj.ρAut).obj U)) ≅
      colimit (CostructuredArrow.proj (EquivariantEtaleSite.toEtaleSite X).op (op U) ⋙ E) :=
  haveI : ∀ F : (EquivariantEtaleSite X × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R,
      (NaturalAction.inflation (Φ := EquivariantEtaleSite.toEtaleSite X ⋙
        TwistedOver.ι (etale (K := K)) X.obj.ρAut)
        (etaleNaturalAction X)).op.HasLeftKanExtension F :=
    etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI : (NaturalAction.inflation
      (Φ := EquivariantEtaleSite.toEtaleSite X ⋙ TwistedOver.ι (etale (K := K)) X.obj.ρAut)
      (etaleNaturalAction X)).op.HasPointwiseLeftKanExtension
        ((CategoryTheory.Prod.fst (EquivariantEtaleSite X) (SingleObj Gᵐᵒᵖ)).op ⋙ E) :=
    etaleInflation_hasPointwiseLeftKanExtension.{u, v, uL, z} X R _
  haveI := etaleUntwisted_hasColimit.{u, v, uL, z} X R E U
  (etaleNaturalAction X).inverseImagePresheafObjIsoUntwistedColimit
    (Ψ := EquivariantEtaleSite.toEtaleSite X) (fun _ _ => rfl) R E U

/-- Module sheaves on the twisted étale site have sheafification in the universe
`max u (v + 1) z uL`. -/
theorem twistedEtale_hasSheafify_inverseImage :
    HasSheafify (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI : Small.{max u (v + 1) z uL} G := small_lift.{z, max u (v + 1) uL, z} G
  twistedEtale_hasSheafify.{u, v, max z uL} X.obj.V X.obj.ρAut R

/-- Berkovich's inverse image `b^*` of module presheaves on `Ét(X(G))` to module sheaves on
the twisted étale site: the sheafification of the inverse image presheaf. -/
def etaleInverseImage :
    ((EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uL} R) ⥤
      Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  (etaleNaturalAction X).inverseImageFunctor R (twistedEtaleTopology X.obj.ρAut)

/-- The inverse image is left adjoint to the presheaf of invariant sections
`F ↦ (V(G) ↦ F(V)^G)`. -/
def etaleInverseImageAdjunction :
    etaleInverseImage.{u, v, uL, z} X R ⊣ etaleInvariantPresheaf X R := by
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  exact (etaleNaturalAction X).inverseImageAdjunction R (twistedEtaleTopology X.obj.ρAut)

/-- Berkovich's inverse image `b^*` of module sheaves on `X(G)_ét` to module sheaves on the
twisted étale site, assuming image pullbacks. -/
def etaleSheafInverseImage (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    Sheaf (equivariantEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R) ⥤
      Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{max u (v + 1) z uL} R) :=
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  haveI := etaleToTwisted_isContinuous X hX
  (etaleNaturalAction X).sheafInverseImageFunctor R
    (twistedEtaleTopology X.obj.ρAut) (equivariantEtaleTopology X)

/-- Assuming image pullbacks, the inverse image of sheaves is left adjoint to the sheaf
`(b_*F)^G` of invariant sections. -/
def etaleSheafInverseImageAdjunction
    (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)) :
    etaleSheafInverseImage.{u, v, uL, z} X R hX ⊣ etaleInvariantSheaf X R hX := by
  haveI := etaleInflation_hasLeftKanExtension.{u, v, uL, z} X R
  haveI := twistedEtale_hasSheafify_inverseImage.{u, v, uL, z} X R
  haveI := etaleToTwisted_isContinuous X hX
  exact (etaleNaturalAction X).sheafInverseImageAdjunction R
    (twistedEtaleTopology X.obj.ρAut) (equivariantEtaleTopology X)

end Etale

end Langlands.Sheaf.Equivariant.Analytic
