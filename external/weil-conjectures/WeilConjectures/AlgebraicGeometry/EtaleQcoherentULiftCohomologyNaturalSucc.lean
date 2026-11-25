/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleULiftInjective
import WeilConjectures.AlgebraicGeometry.EtaleULiftHomology
import WeilConjectures.CategoryTheory.Sites.CohomologyResolutionEvaluationNatural

/-! # Positive-degree naturality of coefficient universe lift

Source: Stacks Project, Tags 01FT and 06XR (resolution computation);
Tag 01DO (the existing coefficient-lift injectivity theorem).
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural-succ)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The positive-degree naturality part of coefficient comparison.
Source: Stacks Project, Tags 01FT and 06XR, with coefficient-lift injectivity
from Tag 01DO. The original statement is the comparison needed in Tag 03P2.
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural-succ)

Proof: Choose an injective resolution R of the associated sheaf E. Coefficient
lift is additive and preserves homology by etale_ulift_preservesHomology; it
preserves injective sheaves by etale_ulift_injective. Apply it degreewise to R,
with the single-complex comparison on the augmentation, to construct a genuine
injective resolution S of L(E). This uses the proved preservation interfaces;
no preservation hypothesis is added to the statement. Evaluate both resolutions
at the terminal etale object. The evaluation complex of S is definitionally the
coefficient lift of the evaluation complex of R. Homology preservation by the
group lift gives an additive equivalence between their homology groups after
lowering the lifted group. The general natural resolution-evaluation comparison
identifies these groups with Sheaf.H, including the specified HasExt.standard
instance on the small side. Compose the three comparisons to choose e.

For any abelian sheaf endomorphism theta, InjectiveResolution.desc lifts it to
an endomorphism phi of R, with augmentation compatibility. L(phi) is a map of S
over L(theta), as follows by applying L to that compatibility. The two natural
resolution-evaluation comparisons and mapHomologyIso_hom_naturality identify the
induced maps under e. All comparisons are fixed before theta is introduced.
No O-linear hypothesis on theta is used. This argument works for every abelian
sheaf, hence in particular for the tensor-section sheaf in the statement, and
handles the empty scheme and zero sheaf without cases. Compactness, separatedness
and quasi-coherence are retained in the unchanged statement but are not needed
for this route. It avoids the finite affine cover and its spectral sequences.
-/
theorem exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    let E := etaleTensorSectionsSheaf F
    let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ e : Sheaf.H (L.obj E) (n + 1) ≃+
        @Sheaf.H _ _ X.smallEtaleTopology E inferInstance (HasExt.standard _) (n + 1),
      ∀ (θ : E ⟶ E) (x : Sheaf.H (L.obj E) (n + 1)),
        e (Sheaf.H.map (L.map θ) (n + 1) x) =
          @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
            inferInstance (HasExt.standard _)
            _ _ θ (n + 1) (e x)  := by
  classical
  let E := etaleTensorSectionsSheaf F
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  let A := AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.PreservesHomology := Scheme.etale_ulift_preservesHomology X
  have : L.Additive := { map_add := fun {_ _ _ _} => rfl }
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hT : CategoryTheory.Limits.IsTerminal T :=
    CategoryTheory.MorphismProperty.Over.mkIdTerminal _ _
  let V := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op T)
  let W := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op T)
  let R := injectiveResolution E
  let c := HomologicalComplex.singleMapHomologicalComplex L (.up ℕ) 0
  let S : InjectiveResolution (L.obj E) :=
    { cocomplex := (L.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
      injective := fun k => Scheme.etale_ulift_injective X (R.cocomplex.X k)
      ι := (c.app E).inv ≫ (L.mapHomologicalComplex (.up ℕ)).map R.ι
      quasiIso := by
        dsimp [c]
        infer_instance }
  obtain ⟨eL, heL⟩ := Sheaf.exists_cohomology_resolution_evaluation_natural_succ
    X.smallEtaleTopology T hT (L.obj E) S n
  obtain ⟨eS, heS⟩ :=
    @Sheaf.exists_cohomology_resolution_evaluation_natural_succ.{u + 1, u, u, u + 1}
      _ _ X.smallEtaleTopology _ (HasExt.standard _) _ T hT E R n
  let K := (V.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let h := (K.sc (n + 1)).mapHomologyIso A
  let e := eL.trans (h.addCommGroupIsoToAddEquiv.trans (AddEquiv.ulift.trans eS.symm))
  refine ⟨e, ?_⟩
  intro θ x
  let φ := InjectiveResolution.desc θ R R
  have comm : R.ι.f 0 ≫ φ.f 0 = θ ≫ R.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero θ R R
  let ψ := (L.mapHomologicalComplex (.up ℕ)).map φ
  have commL : S.ι.f 0 ≫ ψ.f 0 = L.map θ ≫ S.ι.f 0 := by
    have hc : S.ι.f 0 = L.map (R.ι.f 0) := by
      ext U a
      rfl
    rw [hc]
    change L.map (R.ι.f 0) ≫ L.map (φ.f 0) = L.map θ ≫ L.map (R.ι.f 0)
    rw [← L.map_comp, ← L.map_comp, comm]
  have hn := heL (L.map θ) ψ commL x
  have hs := heS θ φ comm (e x)
  have hh := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) (n + 1)).map
      ((V.mapHomologicalComplex (.up ℕ)).map φ)) A
  apply eS.injective
  change eS (eS.symm _) = _
  rw [AddEquiv.apply_symm_apply]
  change (h.hom (eL (Sheaf.H.map (L.map θ) (n + 1) x))).down =
    eS (@Sheaf.H.map _ _ X.smallEtaleTopology _ (HasExt.standard _)
      _ _ θ (n + 1) (e x))
  rw [hn, hs]
  have he : eS (e x) = (h.hom (eL x)).down := by
    change eS (eS.symm _) = _
    exact eS.apply_symm_apply _
  rw [he]
  change (h.hom (HomologicalComplex.homologyMap
    ((W.mapHomologicalComplex (.up ℕ)).map ψ) (n + 1) (eL x))).down =
    HomologicalComplex.homologyMap
      ((V.mapHomologicalComplex (.up ℕ)).map φ) (n + 1) (h.hom (eL x)).down
  exact congrArg ULift.down (ConcreteCategory.congr_hom hh (eL x))


end AlgebraicGeometry.Scheme.Modules
