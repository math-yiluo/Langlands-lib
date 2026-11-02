import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSheafProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartSheafCoherence

/-! # The actual algebra sheaf and its coefficient morphisms on the finite rational site -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The sheaf of actual weighted rational quotient algebras on the finite
rational chart site. Its sheaf proof has no descent hypothesis. -/
def algebraSheaf (A : PresentedAffinoidAlgebra K) :
    Sheaf (finiteRationalTopology K A) (CommAlgCat K) :=
  ⟨algebraPresheaf K A, rationalPresheafIsSheaf K A⟩

@[simp]
theorem algebraSheaf_obj (A : PresentedAffinoidAlgebra K) (d : RationalChart K A) :
    (algebraSheaf K A).obj.obj (Opposite.op d) = CommAlgCat.of K d.algebra := rfl

@[simp]
theorem algebraSheaf_map_apply {A : PresentedAffinoidAlgebra K}
    {d e : RationalChart K A} (f : d ⟶ e) (a : e.algebra) :
    (algebraSheaf K A).obj.map f.op a = f.restriction a := rfl

variable {K}

/-- A bounded coefficient map induces the actual algebra-sheaf morphism to
direct image on the finite rational sites, using quotient transport. -/
def algebraSheafMap {A B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A B) :
    algebraSheaf K A ⟶
      (coefficientSheafPushforward φ (CommAlgCat K)).obj (algebraSheaf K B) where
  hom := {
    app d := CommAlgCat.ofHom (pullbackMap φ d.unop).toAlgHom
    naturality d e h := by
      ext a
      exact congrArg
        (fun f : BoundedAlgHom K d.unop.algebra (pullback φ e.unop).algebra => f a)
        (pullbackRestriction_comp_pullbackMap φ h.unop).symm }

@[simp]
theorem algebraSheafMap_app_apply {A B : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) (a : d.algebra) :
    (algebraSheafMap φ).hom.app (Opposite.op d) a = pullbackMap φ d a := rfl

@[simp]
theorem algebraSheafMap_baseMap {A B : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) (a : A) :
    (algebraSheafMap φ).hom.app (Opposite.op d) (d.baseMap a) =
      (pullback φ d).baseMap (φ a) :=
  pullbackMap_baseMap φ d a

/-- The actual identity comparison identifies the identity coefficient
morphism with the identity of the bundled algebra sheaf. -/
theorem algebraSheafMap_id (A : PresentedAffinoidAlgebra K) :
    algebraSheafMap (BoundedAlgHom.id K A) ≫
        (coefficientSheafPushforwardIdIso A (CommAlgCat K)).hom.app (algebraSheaf K A) =
      𝟙 (algebraSheaf K A) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [coefficientSheafPushforwardIdIso_hom_app]
  ext a
  change (pullbackIdIso d.unop).inv.restriction
    (pullbackMap (BoundedAlgHom.id K A) d.unop a) = a
  rw [← pullbackIdIso_hom_restriction]
  change ((pullbackIdIso d.unop).inv ≫ (pullbackIdIso d.unop).hom).restriction a = a
  rw [Iso.inv_hom_id]
  rfl

/-- After the constructed direct-image comparison, successive coefficient
morphisms equal the morphism for the composite bounded algebra map. -/
theorem algebraSheafMap_comp {A B C : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    algebraSheafMap φ ≫
        (coefficientSheafPushforward φ (CommAlgCat K)).map (algebraSheafMap ψ) ≫
        (coefficientSheafPushforwardCompIso φ ψ (CommAlgCat K)).hom.app
          (algebraSheaf K C) =
      algebraSheafMap (ψ.comp φ) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [coefficientSheafPushforwardCompIso_hom_app]
  ext a
  change (pullbackCompIso φ ψ d.unop).hom.restriction
    (pullbackMap ψ (pullback φ d.unop) (pullbackMap φ d.unop a)) =
      pullbackMap (ψ.comp φ) d.unop a
  exact congrArg
    (fun f : BoundedAlgHom K d.unop.algebra (pullback (ψ.comp φ) d.unop).algebra => f a)
    (pullbackCompIso_hom_transport φ ψ d.unop)

variable (K)

/-- The original affinoid algebra is the section algebra on the actual
terminal whole chart, through its constructed bounded equivalence. -/
def wholeSectionIso (A : PresentedAffinoidAlgebra K) :
    CommAlgCat.of K A ≅ (algebraSheaf K A).obj.obj (Opposite.op (whole K A)) :=
  CommAlgCat.isoMk (wholeEquiv K A).toAlgEquiv

@[simp]
theorem wholeSectionIso_hom_apply (A : PresentedAffinoidAlgebra K) (a : A) :
    (wholeSectionIso K A).hom a = (whole K A).baseMap a := rfl

@[simp]
theorem wholeSectionIso_inv_apply (A : PresentedAffinoidAlgebra K)
    (a : (whole K A).algebra) :
    (wholeSectionIso K A).inv a = wholeRetraction K A a := rfl

/-- Restricting the corresponding whole-chart section is precisely the
original bounded structural map of the chosen rational quotient. -/
@[simp]
theorem wholeSectionIso_restrict (A : PresentedAffinoidAlgebra K)
    (d : RationalChart K A) (a : A) :
    (algebraSheaf K A).obj.map (toWhole K A d).op ((wholeSectionIso K A).hom a) =
      d.baseMap a := by
  change d.baseMap (wholeRetraction K A ((whole K A).baseMap a)) = d.baseMap a
  rw [wholeRetraction_baseMap]

variable {K}

/-- The whole-chart identification recovers the original coefficient map
after the actual comparison between the pulled-back and target whole charts. -/
theorem wholeSectionIso_naturality {A B : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) :
    (wholeSectionIso K A).hom ≫
        (algebraSheafMap φ).hom.app (Opposite.op (whole K A)) ≫
        (algebraSheaf K B).obj.map (pullbackWholeIso φ).inv.op =
      CommAlgCat.ofHom φ.toAlgHom ≫ (wholeSectionIso K B).hom := by
  ext a
  change (pullbackWholeIso φ).inv.restriction
    (pullbackMap φ (whole K A) ((whole K A).baseMap a)) =
      (whole K B).baseMap (φ a)
  rw [pullbackMap_baseMap]
  exact congrArg
    (fun f : BoundedAlgHom K B (whole K B).algebra => f (φ a))
    (pullbackWholeIso φ).inv.comp_baseMap

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
